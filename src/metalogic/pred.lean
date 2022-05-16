/-
References:

https://www.cambridge.org/core/books/handbook-of-practical-logic-and-automated-reasoning/EB6396296813CB562987E8C37AC4520D
https://www.cl.cam.ac.uk/~jrh13/atp/index.html
Harrison, J. (2009).
Handbook of Practical Logic and Automated Reasoning.
Cambridge: Cambridge University Press.
doi:10.1017/CBO9780511576430
-/


import data.set


namespace finset
variables {α : Type*} {β : Type*} {γ : Type*}

lemma mem_ite (x : α) (p : Prop) [decidable p] (s s' : finset α) :
  x ∈ (if p then s else s') ↔ (p → x ∈ s) ∧ (¬ p → x ∈ s') :=
by split_ifs with h; simp [h]

lemma bUnion_sdiff [decidable_eq α] [decidable_eq β]
  (s : finset α) (t : α → finset β) (s' : finset β) :
  s.bUnion t \ s' = s.bUnion (λ x, t x \ s') :=
by { ext, simp only [mem_sdiff, mem_bUnion, exists_prop], tauto }

lemma bUnion_filter [decidable_eq α] [decidable_eq β]
  (s : finset α) (t : α → finset β) (p : α → Prop) [decidable_pred p] :
  (s.filter p).bUnion t = s.bUnion (λ x, if p x then t x else ∅) :=
begin
  ext,
  simp only [mem_ite, imp_iff_not_or, or_and_distrib_right, mem_bUnion, mem_filter, exists_prop,
    not_mem_empty, not_not, or_false, not_and_self, false_or],
  tauto,
end

lemma and_self_imp {p q : Prop} : p ∧ (p → q) ↔ p ∧ q := by tauto

lemma finset.sdiff_bUnion_sdiff [decidable_eq α] [decidable_eq β]
  (s s' : finset α) (t : α → finset β) :
  (s \ s').bUnion t \ s'.bUnion t = s.bUnion t \ s'.bUnion t :=
begin
  simp only [sdiff_eq_filter, bUnion_filter, filter_bUnion, ite_not, mem_bUnion,
    exists_prop, not_exists, not_and],
  congr',
  ext,
  simp only [mem_ite, imp_false, and_self_imp, imp_not_comm, mem_filter, not_mem_empty,
    and.congr_left_iff, and_iff_right_iff_imp],
  intro h,
  exact h x,
end

lemma sdiff_singleton_bUnion [decidable_eq α] [decidable_eq β]
  (s : finset α) (t : α → finset β)
  (x : α) (s' : finset β)
  (h : t x = s') :
  (s \ {x}).bUnion t \ s' = s.bUnion t \ s' :=
begin
  rw [← h, bUnion_sdiff, bUnion_sdiff, sdiff_eq_filter s, bUnion_filter],
  congr',
  ext y,
  suffices : (a ∉ t y ∨ a ∈ t x) ∨ ¬y = x,
  { simpa [mem_ite, imp_false, imp_iff_not_or, and_or_distrib_left] },
  rw [or_comm, ← imp_iff_not_or],
  rintro rfl,
  apply em',
end

lemma bUnion_union [decidable_eq α] [decidable_eq β]
  (s s' : finset α) (t : α → finset β) :
  (s ∪ s').bUnion t = s.bUnion t ∪ s'.bUnion t :=
by { ext, simp [or_and_distrib_right, exists_or_distrib] }

lemma bUnion_sdiff_of_forall_disjoint [decidable_eq β]
  (s : finset α) (t : α → finset β) (s' : finset β)
  (h : ∀ y : α, y ∈ s → disjoint (t y) s') :
  (s.bUnion t) \ s' = s.bUnion t :=
by simpa [sdiff_eq_self_iff_disjoint, disjoint_bUnion_left]

-- Maybe this might be somewhat too specialized?
lemma bUnion_sdiff_singleton_of_forall_not_mem [decidable_eq β]
  (s : finset α) (x : β) (t : α → finset β)
  (h : ∀ y : α, y ∈ s → x ∉ t y) :
  (s.bUnion t) \ {x} = s.bUnion t :=
bUnion_sdiff_of_forall_disjoint s t _ (by simpa [disjoint_singleton_right])

end finset


def list.to_fin_fun {T : Type} (l : list T) : fin l.length → T :=
fun i : fin l.length, list.nth_le l i.val i.property


meta def fin_fun_to_string {T : Type} [has_to_string T] {n : ℕ} (f : fin n → T) : string :=
list.to_string (list.of_fn f)


/-
Term schemes.
var "x" : An object variable named "x". Ranges over the domain of each interpretation.
func 0 "c" [] : A constant named "c".
func n "f" [x1 ... xn] : A function named "f" of n terms (arguments).
-/
inductive term : Type
| var : string → term
| func (n : ℕ) : string → (fin n → term) → term

open term

meta def term.repr : term → string
| (var x) := x.quote
| (func n f terms) := f.quote ++ fin_fun_to_string (fun i : fin n, (terms i).repr)

meta instance : has_repr term := has_repr.mk term.repr

def mk_const (name : string) :=
func 0 name list.nil.to_fin_fun

def mk_func (name : string) (terms : list term) :=
func terms.length name terms.to_fin_fun


/-
Formula schemes.
atom 0 "P" [] : A propositional variable named "P".
atom n "P" [x1 ... xn] : A predicate variable named "P" of n terms (arguments).
-/
inductive formula : Type
| bottom : formula
| top : formula
| atom (n : ℕ) : string → (fin n → term) → formula
| not : formula → formula
| and : formula → formula → formula
| or : formula → formula → formula
| imp : formula → formula → formula
| iff : formula → formula → formula
| forall_ : string → formula → formula
| exists_ : string → formula → formula

open formula

meta def formula.repr : formula → string
| bottom := "⊥"
| top := "⊤"
| (atom n x terms) := x.quote ++ fin_fun_to_string (fun i : fin n, (terms i).repr)
| (not p) := sformat!"(¬ {p.repr})"
| (and p q) := sformat!"({p.repr} ∧ {q.repr})"
| (or p q) := sformat!"({p.repr} ∨ {q.repr})"
| (imp p q) := sformat!"({p.repr} → {q.repr})"
| (iff p q) := sformat!"({p.repr} ↔ {q.repr})"
| (forall_ x p) := sformat!"(∀ {x.quote}. {p.repr})"
| (exists_ x p) := sformat!"(∃ {x.quote}. {p.repr})"

meta instance : has_repr formula := has_repr.mk formula.repr

def mk_prop (name : string) :=
atom 0 name list.nil.to_fin_fun

def mk_pred (name : string) (terms : list term) :=
atom terms.length name terms.to_fin_fun


#eval not (forall_ "x" (mk_pred "P" [mk_func "f" [(var "x")], var "y"]))


/-
domain: A nonempty set D called the domain of the interpretation. The intention is that all terms have values in D.

nonempty: A proof that there is at least one element in the domain.

func: (n : ℕ, f : string) → (f_{M} : (terms : fin n → T) → v : T)
A mapping of each n-ary function symbol f to a function f_{M}.
n : The arity of the function symbol.
f : The function symbol.
f_{M} : The function that the function symbol is mapped to.
terms : fin n → T : The n terms (arguments) of the function expressed as a finite function.
v : T : The result of the function. An element in the domain.

pred: (n : ℕ, P : string) → (P_{M} : (terms : fin n → T) → v : Prop)
A mapping of each n-ary predicate symbol P to a predicate P_{M}.
n : The arity of the predicate symbol.
P : The predicate symbol.
P_{M} : The predicate that the predicate symbol is mapped to.
terms : fin n → T : The n terms (arguments) of the predicate expressed as a finite function.
v : Prop : The result of the predicate. True or false.
-/
structure interpretation (T : Type) : Type :=
(domain : set T)
(nonempty : domain.nonempty)
(func (n : ℕ) : string → (fin n → T) → T)
(pred (n : ℕ) : string → (fin n → T) → Prop)


/-
The type of mappings of object variable names to elements of a domain.
-/
def valuation (T : Type) := string → T

/-
The function mapping each term to an element of a domain by a given interpretation and valuation.
-/
def eval_term (T : Type) (m : interpretation T) (v : valuation T) : term → T
| (var x) := v x
| (func n f terms) := m.func n f (fun i : fin n, eval_term (terms i))

/-
v is a function. x is an element in the domain of v. a is an element in the range of v.
if y = x then (`[` x `↦` a `]` v) y = a
if y ≠ x then (`[` x `↦` a `]` v) y = v y
-/
notation  `[` a' `↦` v `]` f := function.update f a' v

example
  {T U : Type}
  [decidable_eq T]
  (f : T → U)
  (a' a : T)
  (v : U)
  (h1 : a = a') :
  ([a' ↦ v] f) a = v :=
begin
  rewrite <- h1, exact function.update_same a v f,
end

example
  {T U : Type}
  [decidable_eq T]
  (f : T → U)
  (a' a : T)
  (v : U)
  (h1 : a ≠ a') :
  ([a' ↦ v] f) a = f a := function.update_noteq h1 v f


def holds (T : Type) (m : interpretation T) : valuation T → formula → Prop
| _ bottom := false
| _ top := true
| v (atom n x terms) := m.pred n x (fun i : fin n, eval_term T m v (terms i))
| v (not p) := ¬ holds v p
| v (and p q) := holds v p ∧ holds v q
| v (or p q) := holds v p ∨ holds v q
| v (imp p q) := holds v p → holds v q
| v (iff p q) := holds v p ↔ holds v q
| v (forall_ x p) := ∀ a ∈ m.domain, holds ([x ↦ a] v) p
| v (exists_ x p) := ∃ a ∈ m.domain, holds ([x ↦ a] v) p


def term.all_var_set : term → finset string
| (var x) := {x}
| (func n f terms) := finset.bUnion finset.univ (fun i : fin n, (terms i).all_var_set)


theorem thm_3_1
  {T : Type}
  {m : interpretation T}
  {t : term}
  (v v' : valuation T)
  (h1 : ∀ x ∈ t.all_var_set, v x = v' x) :
  eval_term T m v t = eval_term T m v' t :=
begin
  induction t,
  case term.var : x {
    have s1 : x ∈ (var x).all_var_set, unfold term.all_var_set, simp only [finset.mem_singleton],
    calc
          eval_term T m v (var x)
        = v x : by unfold eval_term
    ... = v' x : h1 x s1
    ... = eval_term T m v' (var x) : by unfold eval_term
  },
  case term.func : n f terms ih {
    calc
          eval_term T m v (func n f terms)
        = m.func n f (fun i : fin n, eval_term T m v (terms i)) : by unfold eval_term
    ... = m.func n f (fun i : fin n, eval_term T m v' (terms i)) :
      begin
        congr, funext, apply ih,
        intros x h2, apply h1, unfold term.all_var_set,
        simp only [finset.mem_bUnion, finset.mem_univ, exists_true_left], exact exists.intro i h2
      end
    ... = eval_term T m v' (func n f terms) : by unfold eval_term
	}
end


def formula.all_var_set : formula → finset string
| bottom := ∅
| top := ∅
| (atom n x terms) := finset.bUnion finset.univ (fun i : fin n, (terms i).all_var_set)
| (not p) := p.all_var_set
| (and p q) := p.all_var_set ∪ q.all_var_set
| (or p q) := p.all_var_set ∪ q.all_var_set
| (imp p q) := p.all_var_set ∪ q.all_var_set
| (iff p q) := p.all_var_set ∪ q.all_var_set
| (forall_ x p) := p.all_var_set ∪ {x}
| (exists_ x p) := p.all_var_set ∪ {x}

def formula.free_var_set : formula → finset string
| bottom := ∅
| top := ∅
| (atom n x terms) := finset.bUnion finset.univ (fun i : fin n, (terms i).all_var_set)
| (not p) := p.free_var_set
| (and p q) := p.free_var_set ∪ q.free_var_set
| (or p q) := p.free_var_set ∪ q.free_var_set
| (imp p q) := p.free_var_set ∪ q.free_var_set
| (iff p q) := p.free_var_set ∪ q.free_var_set
| (forall_ x p) := p.free_var_set \ {x}
| (exists_ x p) := p.free_var_set \ {x}


theorem thm_3_2
  {T : Type}
  {m : interpretation T}
  {p : formula}
  (v v' : valuation T)
  (h1 : ∀ x ∈ p.free_var_set, v x = v' x) :
  holds T m v p ↔ holds T m v' p :=
begin
  induction p generalizing v v',
  case formula.bottom {
    calc
          holds T m v bottom
        ↔ false : by unfold holds
    ... ↔ holds T m v' bottom : by unfold holds
  },
  case formula.top {
    calc
          holds T m v top
        ↔ true : by unfold holds
    ... ↔ holds T m v' top : by unfold holds
  },
  case formula.atom : n x terms {
    unfold formula.free_var_set at h1,
    calc
        holds T m v (atom n x terms)
        ↔ m.pred n x (fun i : fin n, eval_term T m v (terms i)) : by unfold holds
    ... ↔ m.pred n x (fun i : fin n, eval_term T m v' (terms i)) :
      begin
        apply iff_of_eq, congr, funext,
        apply thm_3_1, intros x h, apply h1, simp only [finset.mem_bUnion, finset.mem_univ, exists_true_left], exact exists.intro i h
      end
    ... ↔ holds T m v' (atom n x terms) : by unfold holds
  },
  case formula.not : p ih {
    unfold formula.free_var_set at h1,
    have s1 : holds T m v p ↔ holds T m v' p, exact ih v v' h1,
    calc
          holds T m v (not p)
        ↔ ¬ holds T m v p : by unfold holds
    ... ↔ ¬ holds T m v' p : by simp only [s1]
    ... ↔ holds T m v' (not p) : by unfold holds
  },
  case formula.and : p q ih_p ih_q {
    unfold formula.free_var_set at h1, simp only [finset.mem_union, or_imp_distrib, forall_and_distrib] at h1, cases h1,
    have s1 : holds T m v p ↔ holds T m v' p, exact ih_p v v' h1_left,
    have s2 : holds T m v q ↔ holds T m v' q, exact ih_q v v' h1_right,
    calc
          holds T m v (and p q)
        ↔ (holds T m v p ∧ holds T m v q) : by unfold holds
    ... ↔ (holds T m v' p ∧ holds T m v' q) : by simp only [s1, s2]
    ... ↔ holds T m v' (and p q) : by unfold holds
  },
  case formula.or : p q ih_p ih_q {
    unfold formula.free_var_set at h1, simp only [finset.mem_union, or_imp_distrib, forall_and_distrib] at h1, cases h1,
    have s1 : holds T m v p ↔ holds T m v' p, exact ih_p v v' h1_left,
    have s2 : holds T m v q ↔ holds T m v' q, exact ih_q v v' h1_right,
    calc
          holds T m v (or p q)
        ↔ (holds T m v p ∨ holds T m v q) : by unfold holds
    ... ↔ (holds T m v' p ∨ holds T m v' q) : by simp only [s1, s2]
    ... ↔ holds T m v' (or p q) : by unfold holds
  },
  case formula.imp : p q ih_p ih_q {
    unfold formula.free_var_set at h1, simp only [finset.mem_union, or_imp_distrib, forall_and_distrib] at h1, cases h1,
    have s1 : holds T m v p ↔ holds T m v' p, exact ih_p v v' h1_left,
    have s2 : holds T m v q ↔ holds T m v' q, exact ih_q v v' h1_right,
    calc
          holds T m v (imp p q)
        ↔ (holds T m v p → holds T m v q) : by unfold holds
    ... ↔ (holds T m v' p → holds T m v' q) : by simp only [s1, s2]
    ... ↔ holds T m v' (imp p q) : by unfold holds
  },
  case formula.iff : p q ih_p ih_q {
    unfold formula.free_var_set at h1, simp only [finset.mem_union, or_imp_distrib, forall_and_distrib] at h1, cases h1,
    have s1 : holds T m v p ↔ holds T m v' p, exact ih_p v v' h1_left,
    have s2 : holds T m v q ↔ holds T m v' q, exact ih_q v v' h1_right,
    calc
          holds T m v (iff p q)
        ↔ (holds T m v p ↔ holds T m v q) : by unfold holds
    ... ↔ (holds T m v' p ↔ holds T m v' q) : by simp only [s1, s2]
    ... ↔ holds T m v' (iff p q) : by unfold holds
  },
  case formula.forall_ : x p ih {
    unfold formula.free_var_set at h1, simp only [finset.mem_sdiff, finset.mem_singleton] at h1,
    calc
          holds T m v (forall_ x p)
        ↔ ∀ a ∈ m.domain, holds T m ([x ↦ a] v) p : by unfold holds
    ... ↔ ∀ a ∈ m.domain, holds T m ([x ↦ a] v') p :
      begin
        apply ball_congr, intros a h2, apply ih, intros y h3,
        by_cases y = x, {
        calc
              ([x ↦ a] v) y
            = ([x ↦ a] v) x : by rewrite h
        ... = a : dif_pos rfl
        ... = ([x ↦ a] v') x : begin symmetry, exact dif_pos rfl end
        ... = ([x ↦ a] v') y : by rewrite <- h
        },
        {
        calc
              ([x ↦ a] v) y
            = v y : dif_neg h
        ... = v' y : begin apply h1, exact and.intro h3 h end
        ... = ([x ↦ a] v') y : begin symmetry, exact dif_neg h end
        }
      end
    ... ↔ holds T m v' (forall_ x p) : by unfold holds
  },
  case formula.exists_ : x p ih {
    unfold formula.free_var_set at h1, simp only [finset.mem_sdiff, finset.mem_singleton] at h1,
    calc
          holds T m v (exists_ x p)
        ↔ ∃ a ∈ m.domain, holds T m ([x ↦ a] v) p : by unfold holds
    ... ↔ ∃ a ∈ m.domain, holds T m ([x ↦ a] v') p :
      begin
        apply bex_congr, intros a h2, apply ih, intros y h3,
        by_cases y = x, {
        calc
              ([x ↦ a] v) y
            = ([x ↦ a] v) x : by rewrite h
        ... = a : dif_pos rfl
        ... = ([x ↦ a] v') x : begin symmetry, exact dif_pos rfl end
        ... = ([x ↦ a] v') y : by rewrite <- h
        },
        {
        calc
              ([x ↦ a] v) y
            = v y : dif_neg h
        ... = v' y : begin apply h1, exact and.intro h3 h end
        ... = ([x ↦ a] v') y : begin symmetry, exact dif_neg h end
        }
      end
    ... ↔ holds T m v' (exists_ x p) : by unfold holds
  }
end


def is_sentence (p : formula) : Prop :=
p.free_var_set = ∅


theorem cor_3_3
  {p : formula}
  {T : Type}
  {m : interpretation T}
  (v v' : valuation T)
  (h1 : is_sentence p) :
  holds T m v p ↔ holds T m v' p :=
begin
  unfold is_sentence at h1,
  have s1 : ∀ x ∈ p.free_var_set, v x = v' x,
    rewrite h1, simp only [finset.not_mem_empty, forall_false_left, forall_const],
  exact thm_3_2 v v' s1
end


def is_valid (p : formula) : Prop :=
∀ T : Type, ∀ m : interpretation T, ∀ v : valuation T, holds T m v p


/-
satisfies T m p = m satisfies p.
-/
def satisfies (T : Type) (m : interpretation T) (p : formula) : Prop :=
∀ v : valuation T, holds T m v p

/-
satisfies_set T m S = m satisfies S.
-/
def satisfies_set (T : Type) (m : interpretation T) (S : set formula) : Prop :=
∀ p ∈ S, satisfies T m p


def is_satisfiable (p : formula) : Prop :=
∃ T : Type, ∃ m : interpretation T, satisfies T m p

def is_satisfiable_set (S : set formula) : Prop :=
∃ T : Type, ∃ m : interpretation T, ∀ p ∈ S, satisfies T m p


/-
holds_in p T m = p holds in m.
-/
def holds_in (p : formula) (T : Type) (m : interpretation T) : Prop :=
satisfies T m p

/-
set_holds_in S T m = S holds in m.
-/
def set_holds_in (S : set formula) (T : Type) (m : interpretation T) : Prop :=
satisfies_set T m S


example
	(p : formula)
	(h1 : is_sentence p) :
	is_valid p ↔ ¬ (is_satisfiable (not p)) :=
begin
  have s1 : (∀ (T : Type) (m : interpretation T) (v : valuation T), holds T m v p) →
    ∀ (T : Type) (m : interpretation T), ∃ (v : valuation T), holds T m v p,
      intros h2 T m, let v := fun _ : string, m.nonempty.some, exact exists.intro v (h2 T m v),
  have s2 : (∀ (T : Type) (m : interpretation T), ∃ (v : valuation T), holds T m v p) →
    ∀ (T : Type) (m : interpretation T) (v : valuation T), holds T m v p,
      intros h2 T m v, apply exists.elim, exact h2 T m, intros v', exact iff.elim_right (cor_3_3 v v' h1),
  calc
        is_valid p
      ↔ ∀ (T : Type) (m : interpretation T) (v : valuation T), holds T m v p : by unfold is_valid
  ... ↔ ∀ (T : Type) (m : interpretation T), ∃ (v : valuation T), holds T m v p : iff.intro s1 s2
  ... ↔ ¬∃ (T : Type) (m : interpretation T), ∀ (v : valuation T), ¬holds T m v p : begin push_neg, refl end
  ... ↔ ¬∃ (T : Type) (m : interpretation T), ∀ (v : valuation T), holds T m v (not p) : by unfold holds
  ... ↔ ¬∃ (T : Type) (m : interpretation T), satisfies T m (not p) : by unfold satisfies
  ... ↔ ¬is_satisfiable (not p) : by unfold is_satisfiable
end


/-
is_model_of T m Γ = m is a model of Γ
-/
def is_model_of (T : Type) (m : interpretation T) (Γ : set formula) :=
satisfies_set T m Γ


/-
Γ ⊨ p = p holds in all models of Γ.
-/
notation Γ `⊨` p := ∀ T : Type, ∀ m : interpretation T, (is_model_of T m Γ) → (holds_in p T m)


example
	(p : formula) :
	(is_valid p) ↔ (∅ ⊨ p) :=
begin
  split,
  {
    unfold is_valid, unfold holds_in, unfold satisfies, intros h1 T m h2, exact h1 T m
  },
  {
    unfold is_valid, unfold is_model_of, unfold satisfies_set, unfold holds_in,
    unfold satisfies, simp only [set.mem_empty_eq],
    intros h1 T m v, apply h1, intros p h2, contradiction
  }
end


example
	(Γ : set formula) :
	¬ (is_satisfiable_set Γ) ↔ (Γ ⊨ bottom) :=
begin
  unfold is_model_of, unfold is_satisfiable_set, unfold satisfies_set, unfold holds_in, unfold satisfies,
  split,
  {
    intros h1 T m h2 v, unfold holds, apply h1, apply exists.intro T, exact exists.intro m h2
  },
  {
    intros h1, push_neg, intros T m, by_contradiction, push_neg at h,
    exact h1 T m h (fun _ : string, m.nonempty.some)
  }
end


example
	(T : Type)
	(m : interpretation T)
	(p : formula) :
	(∀ x : string, ∀ v : valuation T, ∀ a ∈ m.domain, holds T m ([x ↦ a] v) p) ↔ (∀ v : valuation T, holds T m v p) :=
begin
  split,
  intros h1 v, sorry,
  intros h1 x v a h2, exact h1 ([x ↦ a] v)
end


/-
A substitution mapping.
A mapping of each variable name to a term.
-/
def instantiation := string → term

def sub_term (s : instantiation) : term → term
| (var x) := s x
| (func n name terms) := func n name (fun i : fin n, sub_term (terms i))


lemma lem_3_4
  (t : term)
  (s : instantiation) :
  (sub_term s t).all_var_set = finset.bUnion t.all_var_set (fun y : string, (s y).all_var_set) :=
begin
  induction t,
  case term.var : x {
    calc
          (sub_term s (var x)).all_var_set
        = (s x).all_var_set : by unfold sub_term
    ... = finset.bUnion {x} (fun y : string, (s y).all_var_set) : by simp only [finset.singleton_bUnion]
    ... = finset.bUnion (var x).all_var_set (fun y : string, (s y).all_var_set) : by unfold term.all_var_set
  },
  case term.func : n f terms ih {
    simp at ih,
    calc
          (sub_term s (func n f terms)).all_var_set
        = (func n f (fun i : fin n, sub_term s (terms i))).all_var_set : by unfold sub_term
    ... = finset.bUnion finset.univ (fun i : fin n, (sub_term s (terms i)).all_var_set) : by unfold term.all_var_set
    ... = finset.bUnion finset.univ (fun i : fin n, finset.bUnion (terms i).all_var_set (fun y : string, (s y).all_var_set)) : by simp only [ih]
    ... = finset.bUnion (finset.bUnion finset.univ (fun i : fin n, (terms i).all_var_set)) (fun y : string, (s y).all_var_set) : begin symmetry, apply finset.bUnion_bUnion end
    ... = finset.bUnion (func n f terms).all_var_set (fun y : string, (s y).all_var_set) : by unfold term.all_var_set
  }
end


lemma lem_3_5
  (T : Type)
  (t : term)
  (s : instantiation)
  (m : interpretation T)
  (v : valuation T) :
  eval_term T m v (sub_term s t) = eval_term T m ((eval_term T m v) ∘ s) t :=
begin
  induction t,
  case term.var : x {
    calc
          eval_term T m v (sub_term s (var x))
        = eval_term T m v (s x) : by unfold sub_term
    ... = ((eval_term T m v) ∘ s) x : by unfold function.comp
    ... = eval_term T m ((eval_term T m v) ∘ s) (var x) : by unfold eval_term
  },
  case term.func : n f terms ih {
    have ih' : ∀ (i : fin n), eval_term T m v (sub_term s (terms i)) =
      eval_term T m ((eval_term T m v) ∘ s) (terms i), exact ih,
    calc
          eval_term T m v (sub_term s (func n f terms))
        = eval_term T m v (func n f (fun i, sub_term s (terms i))) : by unfold sub_term
    ... = m.func n f (fun i, eval_term T m v (sub_term s (terms i))) : by unfold eval_term
    ... = m.func n f (fun i, eval_term T m ((eval_term T m v) ∘ s) (terms i)) : begin congr, apply funext, exact ih' end
    ... = eval_term T m ((eval_term T m v) ∘ s) (func n f terms) : by unfold eval_term
  }
end


def sub_formula_simp (s : instantiation) : formula → formula
| bottom := bottom
| top := top
| (atom n x terms) := atom n x (fun i : fin n, sub_term s (terms i))
| (not p) := not (sub_formula_simp p)
| (and p q) := and (sub_formula_simp p) (sub_formula_simp q)
| (or p q) := or (sub_formula_simp p) (sub_formula_simp q)
| (imp p q) := imp (sub_formula_simp p) (sub_formula_simp q)
| (iff p q) := iff (sub_formula_simp p) (sub_formula_simp q)
| (forall_ x p) := forall_ x (sub_formula_simp p)
| (exists_ x p) := exists_ x (sub_formula_simp p)

def sub_admits (s : instantiation) : formula → Prop
| bottom := true
| top := true
| (atom _ _ _) := true
| (not p) := sub_admits p
| (and p q) := sub_admits p ∧ sub_admits q
| (or p q) := sub_admits p ∧ sub_admits q
| (imp p q) := sub_admits p ∧ sub_admits q
| (iff p q) := sub_admits p ∧ sub_admits q
| (forall_ x p) := s x = var x ∧ sub_admits p ∧ ∀ y ∈ p.free_var_set \ {x}, x ∉ (s y).all_var_set
| (exists_ x p) := s x = var x ∧ sub_admits p ∧ ∀ y ∈ p.free_var_set \ {x}, x ∉ (s y).all_var_set


lemma lem_3_6_simp
  (p : formula)
  (s : instantiation)
  (h1 : sub_admits s p) :
  (sub_formula_simp s p).free_var_set = finset.bUnion p.free_var_set (fun y : string, (s y).all_var_set) :=
begin
  induction p generalizing s,
  case formula.bottom {
    unfold sub_formula_simp, unfold formula.free_var_set, simp only [finset.bUnion_empty]
  },
  case formula.top {
    unfold sub_formula_simp, unfold formula.free_var_set, simp only [finset.bUnion_empty]
  },
  case formula.atom : n x terms {
    calc
          (sub_formula_simp s (atom n x terms)).free_var_set
        = (atom n x (fun i : fin n, sub_term s (terms i))).free_var_set : by unfold sub_formula_simp
    ... = finset.bUnion finset.univ (fun i : fin n, (sub_term s (terms i)).all_var_set) : by unfold formula.free_var_set
    ... = finset.bUnion finset.univ (fun i : fin n, (finset.bUnion (terms i).all_var_set (fun y : string, (s y).all_var_set))) :
          begin congr, funext, apply lem_3_4 end
    ... = finset.bUnion (finset.bUnion finset.univ (fun i : fin n, (terms i).all_var_set)) (fun y : string, (s y).all_var_set) :
          begin symmetry, apply finset.bUnion_bUnion end
    ... = finset.bUnion (atom n x terms).free_var_set (fun y : string, (s y).all_var_set) : by unfold formula.free_var_set
  },
  case formula.not : p ih {
    calc
          (sub_formula_simp s (not p)).free_var_set
        = (not (sub_formula_simp s p)).free_var_set : by unfold sub_formula_simp
    ... = (sub_formula_simp s p).free_var_set : by unfold formula.free_var_set
    ... = finset.bUnion p.free_var_set (fun y : string, (s y).all_var_set) : begin unfold sub_admits at h1, exact ih s h1 end
    ... = finset.bUnion (not p).free_var_set (fun y : string, (s y).all_var_set) : by unfold formula.free_var_set
  },
  case formula.and : p q ih_p ih_q {
    calc
          (sub_formula_simp s (and p q)).free_var_set
        = (and (sub_formula_simp s p) (sub_formula_simp s q)).free_var_set : by unfold sub_formula_simp
    ... = (sub_formula_simp s p).free_var_set ∪ (sub_formula_simp s q).free_var_set : by unfold formula.free_var_set
    ... = finset.bUnion p.free_var_set (fun y : string, (s y).all_var_set) ∪
            finset.bUnion q.free_var_set (fun y : string, (s y).all_var_set) :
          begin
            unfold sub_admits at h1, cases h1,
            congr, exact ih_p s h1_left, exact ih_q s h1_right,
          end
    ... = finset.bUnion (p.free_var_set ∪ q.free_var_set) (fun y : string, (s y).all_var_set) : by simp [finset.bUnion_union, finset.union_comm]
    ... = finset.bUnion (and p q).free_var_set (fun y : string, (s y).all_var_set) : by unfold formula.free_var_set
  },
  case formula.or : p q ih_p ih_q {
    sorry
  },
  case formula.imp : p q ih_p ih_q {
    sorry
  },
  case formula.iff : p q ih_p ih_q {
    sorry
  },
  case formula.forall_ : x p ih {
    unfold sub_admits at h1, cases h1, cases h1_right,
    calc
          (sub_formula_simp s (forall_ x p)).free_var_set
        = (forall_ x (sub_formula_simp s p)).free_var_set :
            by unfold sub_formula_simp
    ... = (sub_formula_simp s p).free_var_set \ {x} :
            by unfold formula.free_var_set
    ... = (finset.bUnion p.free_var_set (fun y : string, (s y).all_var_set)) \ {x} : by rewrite ih s h1_right_left
    ... = (finset.bUnion (p.free_var_set \ {x}) (fun (y : string), (s y).all_var_set)) \ {x} :
            begin symmetry, apply finset.sdiff_singleton_bUnion, rewrite h1_left, unfold term.all_var_set end
    ... = finset.bUnion (p.free_var_set \ {x}) (fun (y : string), (s y).all_var_set) :
            begin
              apply finset.bUnion_sdiff_of_forall_disjoint,
              simp only [finset.disjoint_singleton_right], apply h1_right_right
            end
    ... = finset.bUnion (forall_ x p).free_var_set (fun y : string, (s y).all_var_set) : by unfold formula.free_var_set
  },
  case formula.exists_ : x p ih {
    sorry
  }
end


theorem thm_3_7_simp
  (p : formula)
  (s : instantiation)
  (T : Type)
  (m : interpretation T)
  (v : valuation T)
  (h1 : sub_admits s p) :
  holds T m v (sub_formula_simp s p) ↔ holds T m ((eval_term T m v) ∘ s) p :=
begin
  induction p generalizing s v,
  case formula.bottom {
    unfold sub_formula_simp, unfold holds
  },
  case formula.top {
    unfold sub_formula_simp, unfold holds
  },
  case formula.atom : n x terms {
    calc
    holds T m v (sub_formula_simp s (atom n x terms)) ↔
      holds T m v (atom n x (fun i : fin n, sub_term s (terms i))) : by unfold sub_formula_simp
    ... ↔ m.pred n x (fun i : fin n, eval_term T m v (sub_term s (terms i))) : by unfold holds
    ... ↔ m.pred n x (fun i : fin n, eval_term T m ((eval_term T m v) ∘ s) (terms i)) : by simp only [lem_3_5]
    ... ↔ holds T m ((eval_term T m v) ∘ s) (atom n x terms) : by unfold holds
  },
  case formula.not : p ih {
    calc
    holds T m v (sub_formula_simp s (not p)) ↔ holds T m v (not (sub_formula_simp s p)) : by unfold sub_formula_simp
    ... ↔ ¬ holds T m v (sub_formula_simp s p) : by unfold holds
    ... ↔ ¬ holds T m ((eval_term T m v) ∘ s) p : begin unfold sub_admits at h1, rewrite ih s v h1 end
    ... ↔ holds T m ((eval_term T m v) ∘ s) (not p) : by unfold holds
  },
  case formula.and : p q ih_p ih_q {
    calc
    holds T m v (sub_formula_simp s (and p q)) ↔ holds T m v (and (sub_formula_simp s p) (sub_formula_simp s q)) : by unfold sub_formula_simp
    ... ↔ (holds T m v (sub_formula_simp s p)) ∧ (holds T m v (sub_formula_simp s q)) : by unfold holds
    ... ↔ (holds T m ((eval_term T m v) ∘ s) p) ∧ (holds T m ((eval_term T m v) ∘ s) q) :
        begin unfold sub_admits at h1, cases h1, rewrite ih_p s v h1_left, rewrite ih_q s v h1_right end
    ... ↔ holds T m ((eval_term T m v) ∘ s) (and p q) : by unfold holds
  },
  case formula.or : p q ih_p ih_q {
    sorry
  },
  case formula.imp : p q ih_p ih_q {
    sorry
  },
  case formula.iff : p q ih_p ih_q {
    sorry
  },
  case formula.forall_ : x p ih {
    begin
      unfold sub_admits at h1, cases h1, cases h1_right,
      calc
            holds T m v (sub_formula_simp s (forall_ x p))
          ↔ holds T m v (forall_ x (sub_formula_simp s p)) : by unfold sub_formula_simp
      ... ↔ (∀ a ∈ m.domain, holds T m ([x ↦ a] v) (sub_formula_simp s p)) : by unfold holds
      ... ↔ (∀ a ∈ m.domain, holds T m (eval_term T m ([x ↦ a] v) ∘ s) p) :
            begin
              apply forall_congr, intros a, apply imp_congr, refl,
              exact ih s ([x ↦ a] v) h1_right_left
            end
      ... ↔ (∀ a ∈ m.domain, holds T m ([x ↦ a] eval_term T m v ∘ s) p) :
            begin
              apply forall_congr, intros a, apply imp_congr, refl,
              apply thm_3_2, intros z h2,
              by_cases z = x,
              {
                calc
                      (eval_term T m ([x ↦ a] v) ∘ s) z
                    = (eval_term T m ([x ↦ a] v) ∘ s) x : by rewrite h
                ... = eval_term T m ([x ↦ a] v) (s x) : by unfold function.comp
                ... = eval_term T m ([x ↦ a] v) (var x) : by rewrite h1_left
                ... = ([x ↦ a] v) x : by unfold eval_term
                ... = a : by simp only [function.update_same]
                ... = ([x ↦ a] eval_term T m v ∘ s) x : by simp only [function.update_same]
                ... = ([x ↦ a] eval_term T m v ∘ s) z : by rewrite h
              },
              {
                calc
                      (eval_term T m ([x ↦ a] v) ∘ s) z
                    = eval_term T m ([x ↦ a] v) (s z) : by unfold function.comp
                ... = eval_term T m v (s z) :
                      begin
                        apply thm_3_1, intros y h3,
                        apply function.update_noteq, intros h4, apply h1_right_right z,
                        simp only [finset.mem_sdiff, finset.mem_singleton], exact and.intro h2 h,
                        rewrite h4 at h3, exact h3
                      end
                ... = (eval_term T m v ∘ s) z : by unfold function.comp
                ... = ([x ↦ a] eval_term T m v ∘ s) z : by simp only [function.update_noteq h]
              }
            end
      ... ↔ holds T m (eval_term T m v ∘ s) (forall_ x p) : by unfold holds
    end
  },
  case formula.exists_ : x p ih {
    sorry
  }
end


theorem cor_3_8_simp
  (p : formula)
  (s : instantiation)
  (h1 : sub_admits s p)
  (h2 : is_valid p) :
  is_valid (sub_formula_simp s p) :=
begin
  sorry
end


def alpha_convert_term (s: string → string) : term → term
| (var x) := var (s x)
| (func n f terms) := func n f (fun i : fin n, alpha_convert_term (terms i))

def alpha_convert_formula (s : string → string) : formula → formula
| bottom := bottom
| top := top
| (atom n x terms) := atom n x (fun i : fin n, alpha_convert_term s (terms i))
| (not p) := not (alpha_convert_formula p)
| (and p q) := and (alpha_convert_formula p) (alpha_convert_formula q)
| (or p q) := or (alpha_convert_formula p) (alpha_convert_formula q)
| (imp p q) := imp (alpha_convert_formula p) (alpha_convert_formula q)
| (iff p q) := iff (alpha_convert_formula p) (alpha_convert_formula q)
| (forall_ x p) := forall_ (s x) (alpha_convert_formula p)
| (exists_ x p) := exists_ (s x) (alpha_convert_formula p)

def alpha_convert_valid (s : string → string) : formula → Prop
| bottom := true
| top := true
| (atom _ _ _) := true
| (not p) := alpha_convert_valid p
| (and p q) := alpha_convert_valid p ∧ alpha_convert_valid q
| (or p q) := alpha_convert_valid p ∧ alpha_convert_valid q
| (imp p q) := alpha_convert_valid p ∧ alpha_convert_valid q
| (iff p q) := alpha_convert_valid p ∧ alpha_convert_valid q
| (forall_ x p) := alpha_convert_valid p ∧ s x ∉ p.free_var_set \ {x}
| (exists_ x p) := alpha_convert_valid p ∧ s x ∉ p.free_var_set \ {x}


theorem is_valid_mp
  (p q : formula)
  (h1 : is_valid p)
  (h2 : is_valid (p.imp q)) :
  is_valid q :=
begin
  unfold is_valid at *,
  intros T m v,
  unfold holds at h2, apply h2, apply h1
end

theorem is_valid_prop_1
  (p q : formula) :
  is_valid (p.imp (q.imp p)) :=
begin
  unfold is_valid, unfold holds,
  intros T m v h1 h2, exact h1
end

theorem is_valid_prop_2
  (p q r : formula) :
  is_valid ((p.imp (q.imp r)).imp ((p.imp q).imp (p.imp r))) :=
begin
  unfold is_valid, unfold holds,
  intros T m v h1 h2 h3,
  apply h1, exact h3, apply h2, exact h3
end

theorem is_valid_prop_3
  (p q : formula) :
  is_valid (((not p).imp (not q)).imp (q.imp p)) :=
begin
  unfold is_valid, unfold holds,
  intros T m v,
  intros h1 h2,
  by_contradiction, apply h1, exact h, exact h2
end


theorem is_valid_gen
  (p : formula)
  (x : string)
  (h1 : is_valid p) :
  is_valid (forall_ x p) :=
begin
  unfold is_valid at *, unfold holds at *,
  intros T m v a h2,
  apply h1
end

theorem is_valid_pred_1
  (p q : formula)
  (x : string):
  is_valid ((forall_ x (p.imp q)).imp ((forall_ x p).imp (forall_ x q))) :=
begin
  unfold is_valid, unfold holds,
  intros T m v h1 h2 a h3,
  apply h1 a h3, exact h2 a h3
end

def sub_single_var (x : string) (t : term) : instantiation := [x ↦ t] (fun v : string, var v)

theorem is_valid_pred_2
  (p : formula)
  (x : string)
  (t : term)
  (h1 : sub_admits (sub_single_var x t) p) :
  is_valid ((forall_ x p).imp (sub_formula_simp (sub_single_var x t) p)) :=
begin
  unfold is_valid, unfold holds,
  intros T m v h2,
  apply cor_3_8_simp, exact h1,
  unfold is_valid,
  intros T' m' v', sorry
end

theorem is_valid_pred_3
  (p : formula)
  (x : string)
  (h1 : x ∉ p.free_var_set) :
  is_valid (p.imp (forall_ x p)) :=
begin
  unfold is_valid, unfold holds,
  intros T m v h2 a h3,
  have s1 : ∀ x' ∈ p.free_var_set, ([x ↦ a] v) x' = v x', intros x' h4, apply function.update_noteq,
    by_contradiction, apply h1, rewrite <- h, exact h4,
  rewrite thm_3_2 ([x ↦ a] v) v s1, exact h2
end


/-
/-
def variant : string → finset string → string
| x vars := if x ∈ vars then variant (string.push x '\'') vars else x
-/

def variant : string → finset string → string
| x vars := if x ∈ vars then
  have vars.sup (λ i, i.length) + 1 - (string.push x '\'').length < vars.sup (λ i, i.length)  + 1 - x.length, from sorry,
  variant (string.push x '\'') vars else x
using_well_founded { rel_tac := λ _ _,
  `[exact ⟨_, measure_wf (λ ⟨x, vars⟩, vars.sup (λ i, i.length) + 1 - x.length)⟩] }

lemma variant_not_mem (x : string) (s : finset string) : variant x s ∉ s :=
begin
  sorry
end

def sub_formula : instantiation → formula → formula
| _ bottom := bottom
| _ top := top
| s (atom n x terms) := atom n x (fun i : fin n, sub_term s (terms i))
| s (not p) := not (sub_formula s p)
| s (and p q) := and (sub_formula s p) (sub_formula s q)
| s (or p q) := or (sub_formula s p) (sub_formula s q)
| s (imp p q) := imp (sub_formula s p) (sub_formula s q)
| s (iff p q) := iff (sub_formula s p) (sub_formula s q)
| s (forall_ x p) :=
  let x' :=
    if ∃ y ∈ p.free_var_set \ {x}, x ∈ (s y).all_var_set
    then variant x (sub_formula ([x ↦ var x] s) p).free_var_set
    else x
  in forall_ x' (sub_formula ([x ↦ var x'] s) p)
| s (exists_ x p) :=
  let x' :=
    if ∃ y ∈ p.free_var_set \ {x}, x ∈ (s y).all_var_set
    then variant x (sub_formula ([x ↦ var x] s) p).free_var_set
    else x
  in exists_ x' (sub_formula ([x ↦ var x'] s) p)


lemma lem_3_6_1
  (x : string)
  (p : formula)
  (s : instantiation)
  (h1 : ∀ s : instantiation, (sub_formula s p).free_var_set =
    finset.bUnion p.free_var_set (fun y : string, (s y).all_var_set)) :
  let x' :=
      if ∃ y ∈ p.free_var_set \ {x}, x ∈ (s y).all_var_set
      then variant x (sub_formula ([x ↦ var x] s) p).free_var_set
      else x
  in
  x' ∉ finset.bUnion (p.free_var_set \ {x}) (fun y : string, (s y).all_var_set) :=
begin
  intro x',
  by_cases x ∈ finset.bUnion (p.free_var_set \ {x}) (fun y : string, (s y).all_var_set),
  {
    have s1 : finset.bUnion (p.free_var_set \ {x}) (fun y : string, (s y).all_var_set) ⊆
      (sub_formula ([x ↦ var x] s) p).free_var_set,
      calc
      finset.bUnion (p.free_var_set \ {x}) (fun y : string, (s y).all_var_set) =
        finset.bUnion (p.free_var_set \ {x}) (fun y : string, (([x ↦ var x] s) y).all_var_set) :
          begin
            symmetry, apply finset.bUnion_congr, refl, intros a h1, congr,
            simp only [finset.mem_sdiff, finset.mem_singleton] at h1, cases h1,
            exact function.update_noteq h1_right (var x) s
          end
      ... ⊆ finset.bUnion p.free_var_set (fun y : string, (([x ↦ var x] s) y).all_var_set) : 
          begin apply finset.bUnion_subset_bUnion_of_subset_left, apply finset.sdiff_subset end
      ... = (sub_formula ([x ↦ var x] s) p).free_var_set :
          begin symmetry, exact h1 (function.update s x (var x)) end,
    have s2 : x' = variant x (sub_formula ([x ↦ var x] s) p).free_var_set, simp only [finset.mem_bUnion] at h, exact if_pos h,
    have s3 : x' ∉ (sub_formula ([x ↦ var x] s) p).free_var_set, rewrite s2, apply variant_not_mem,
    exact finset.not_mem_mono s1 s3
  },
  {
    have s1 : x' = x, simp only [finset.mem_bUnion] at h, exact if_neg h,
    rewrite s1, exact h
  }
end


lemma lem_3_6
  (p : formula)
  (s : instantiation) :
  (sub_formula s p).free_var_set = finset.bUnion p.free_var_set (fun y : string, (s y).all_var_set) :=
begin
  induction p generalizing s,
  case formula.bottom {
    unfold sub_formula, unfold formula.free_var_set, simp only [finset.bUnion_empty]
  },
  case formula.top {
    unfold sub_formula, unfold formula.free_var_set, simp only [finset.bUnion_empty]
  },
  case formula.atom : n x terms {
    calc
    (sub_formula s (atom n x terms)).free_var_set = (atom n x (fun i : fin n, sub_term s (terms i))).free_var_set : by unfold sub_formula
    ... = finset.bUnion finset.univ (fun i : fin n, (sub_term s (terms i)).all_var_set) : by unfold formula.free_var_set
    ... = finset.bUnion finset.univ (fun i : fin n, (finset.bUnion (terms i).all_var_set (fun y : string, (s y).all_var_set))) :
        by simp only [lem_3_4]
    ... = finset.bUnion (finset.bUnion finset.univ (fun i : fin n, (terms i).all_var_set)) (fun y : string, (s y).all_var_set) :
        begin ext1, simp only [finset.mem_bUnion, finset.mem_univ, exists_prop, exists_true_left], tauto end
    ... = finset.bUnion (atom n x terms).free_var_set (fun y : string, (s y).all_var_set) : by unfold formula.free_var_set
  },
  case formula.not : p ih {
    calc
    (sub_formula s (not p)).free_var_set = (not (sub_formula s p)).free_var_set : by unfold sub_formula
    ... = (sub_formula s p).free_var_set : by unfold formula.free_var_set
    ... = finset.bUnion p.free_var_set (fun y : string, (s y).all_var_set) : ih s
    ... = finset.bUnion (not p).free_var_set (fun y : string, (s y).all_var_set) : by unfold formula.free_var_set
  },
  case formula.and : p q ih_p ih_q {
    calc
    (sub_formula s (and p q)).free_var_set = (and (sub_formula s p) (sub_formula s q)).free_var_set : by unfold sub_formula
    ... = (sub_formula s p).free_var_set ∪ (sub_formula s q).free_var_set : by unfold formula.free_var_set
    ... = finset.bUnion p.free_var_set (fun y : string, (s y).all_var_set) ∪
            finset.bUnion q.free_var_set (fun y : string, (s y).all_var_set) : by simp only [ih_p, ih_q]
    ... = finset.bUnion (p.free_var_set ∪ q.free_var_set) (fun y : string, (s y).all_var_set) :
          begin ext1, simp only [finset.mem_union, finset.mem_bUnion, exists_prop], split, finish, finish end
    ... = finset.bUnion (and p q).free_var_set (fun y : string, (s y).all_var_set) : by unfold formula.free_var_set
  },
  case formula.or : p q ih_p ih_q {
    calc
    (sub_formula s (or p q)).free_var_set = (or (sub_formula s p) (sub_formula s q)).free_var_set : by unfold sub_formula
    ... = (sub_formula s p).free_var_set ∪ (sub_formula s q).free_var_set : by unfold formula.free_var_set
    ... = finset.bUnion p.free_var_set (fun y : string, (s y).all_var_set) ∪
            finset.bUnion q.free_var_set (fun y : string, (s y).all_var_set) : by simp only [ih_p, ih_q]
    ... = finset.bUnion (p.free_var_set ∪ q.free_var_set) (fun y : string, (s y).all_var_set) :
          begin ext1, simp only [finset.mem_union, finset.mem_bUnion, exists_prop], split, finish, finish end
    ... = finset.bUnion (or p q).free_var_set (fun y : string, (s y).all_var_set) : by unfold formula.free_var_set
  },
  case formula.imp : p q ih_p ih_q {
    calc
    (sub_formula s (imp p q)).free_var_set = (imp (sub_formula s p) (sub_formula s q)).free_var_set : by unfold sub_formula
    ... = (sub_formula s p).free_var_set ∪ (sub_formula s q).free_var_set : by unfold formula.free_var_set
    ... = finset.bUnion p.free_var_set (fun y : string, (s y).all_var_set) ∪
            finset.bUnion q.free_var_set (fun y : string, (s y).all_var_set) : by simp only [ih_p, ih_q]
    ... = finset.bUnion (p.free_var_set ∪ q.free_var_set) (fun y : string, (s y).all_var_set) :
          begin ext1, simp only [finset.mem_union, finset.mem_bUnion, exists_prop], split, finish, finish end
    ... = finset.bUnion (imp p q).free_var_set (fun y : string, (s y).all_var_set) : by unfold formula.free_var_set
  },
  case formula.iff : p q ih_p ih_q {
    calc
    (sub_formula s (iff p q)).free_var_set = (iff (sub_formula s p) (sub_formula s q)).free_var_set : by unfold sub_formula
    ... = (sub_formula s p).free_var_set ∪ (sub_formula s q).free_var_set : by unfold formula.free_var_set
    ... = finset.bUnion p.free_var_set (fun y : string, (s y).all_var_set) ∪
            finset.bUnion q.free_var_set (fun y : string, (s y).all_var_set) : by simp only [ih_p, ih_q]
    ... = finset.bUnion (p.free_var_set ∪ q.free_var_set) (fun y : string, (s y).all_var_set) :
          begin ext1, simp only [finset.mem_union, finset.mem_bUnion, exists_prop], split, finish, finish end
    ... = finset.bUnion (iff p q).free_var_set (fun y : string, (s y).all_var_set) : by unfold formula.free_var_set
  },
  case formula.forall_ : x p ih {
    let x' :=
      if ∃ y ∈ p.free_var_set \ {x}, x ∈ (s y).all_var_set
      then variant x (sub_formula ([x ↦ var x] s) p).free_var_set
      else x,
    calc
          (sub_formula s (forall_ x p)).free_var_set
        = (forall_ x' (sub_formula ([x ↦ var x'] s) p)).free_var_set :
            by unfold sub_formula
    ... = (sub_formula ([x ↦ var x'] s) p).free_var_set \ {x'} :
            by unfold formula.free_var_set
    ... = (finset.bUnion p.free_var_set (fun (y : string), (([x ↦ var x'] s) y).all_var_set)) \ {x'} :
            by simp only [ih ([x ↦ var x'] s)]
    ... = (finset.bUnion (p.free_var_set \ {x}) (fun (y : string), (([x ↦ var x'] s) y).all_var_set)) \ {x'} :
            begin apply finset_bUnion_sdiff, finish end
    ... = (finset.bUnion (p.free_var_set \ {x}) (fun (y : string), (s y).all_var_set)) \ {x'} :
            begin congr' 1, apply finset.bUnion_congr, refl, intros a h1, congr, apply function.update_noteq,
            simp only [finset.mem_sdiff, finset.mem_singleton] at h1, cases h1, exact h1_right end
    ... = finset.bUnion (p.free_var_set \ {x}) (fun (y : string), (s y).all_var_set) :
            begin apply finset.sdiff_singleton_not_mem_eq_self, exact lem_3_6_1 x p s ih end
  },
  case formula.exists_ : x p ih {
    let x' :=
      if ∃ y ∈ p.free_var_set \ {x}, x ∈ (s y).all_var_set
      then variant x (sub_formula ([x ↦ var x] s) p).free_var_set
      else x,
    calc
          (sub_formula s (exists_ x p)).free_var_set
        = (exists_ x' (sub_formula ([x ↦ var x'] s) p)).free_var_set :
            by unfold sub_formula
    ... = (sub_formula ([x ↦ var x'] s) p).free_var_set \ {x'} :
            by unfold formula.free_var_set
    ... = (finset.bUnion p.free_var_set (fun (y : string), (([x ↦ var x'] s) y).all_var_set)) \ {x'} :
            by simp only [ih ([x ↦ var x'] s)]
    ... = (finset.bUnion (p.free_var_set \ {x}) (fun (y : string), (([x ↦ var x'] s) y).all_var_set)) \ {x'} :
            begin apply finset_bUnion_sdiff, finish end
    ... = (finset.bUnion (p.free_var_set \ {x}) (fun (y : string), (s y).all_var_set)) \ {x'} :
            begin congr' 1, apply finset.bUnion_congr, refl, intros a h1, congr, apply function.update_noteq,
            simp only [finset.mem_sdiff, finset.mem_singleton] at h1, cases h1, exact h1_right end
    ... = finset.bUnion (p.free_var_set \ {x}) (fun (y : string), (s y).all_var_set) :
            begin apply finset.sdiff_singleton_not_mem_eq_self, exact lem_3_6_1 x p s ih end
  }
end

theorem thm_3_7
  (p : formula)
  (s : instantiation)
  (T : Type)
  (m : interpretation T)
  (v : valuation T) :
  holds T m v (sub_formula s p) ↔ holds T m ((eval_term T m v) ∘ s) p :=
begin
  induction p generalizing s v,
  case formula.bottom {
    unfold sub_formula, unfold holds
  },
  case formula.top {
    unfold sub_formula, unfold holds
  },
  case formula.atom : n x terms {
    calc
    holds T m v (sub_formula s (atom n x terms)) ↔
      holds T m v (atom n x (fun i : fin n, sub_term s (terms i))) : by unfold sub_formula
    ... ↔ m.pred n x (fun i : fin n, eval_term T m v (sub_term s (terms i))) : by unfold holds
    ... ↔ m.pred n x (fun i : fin n, eval_term T m ((eval_term T m v) ∘ s) (terms i)) : by simp only [lem_3_5]
    ... ↔ holds T m ((eval_term T m v) ∘ s) (atom n x terms) : by unfold holds
  },
  case formula.not : p ih {
    calc
    holds T m v (sub_formula s (not p)) ↔ holds T m v (not (sub_formula s p)) : by unfold sub_formula
    ... ↔ ¬ holds T m v (sub_formula s p) : by unfold holds
    ... ↔ ¬ holds T m ((eval_term T m v) ∘ s) p : by rewrite ih s v
    ... ↔ holds T m ((eval_term T m v) ∘ s) (not p) : by unfold holds
  },
  case formula.and : p q ih_p ih_q {
    calc
    holds T m v (sub_formula s (and p q)) ↔ holds T m v (and (sub_formula s p) (sub_formula s q)) : by unfold sub_formula
    ... ↔ (holds T m v (sub_formula s p)) ∧ (holds T m v (sub_formula s q)) : by unfold holds
    ... ↔ (holds T m ((eval_term T m v) ∘ s) p) ∧ (holds T m ((eval_term T m v) ∘ s) q) :
        begin rewrite ih_p s v, rewrite ih_q s v end
    ... ↔ holds T m ((eval_term T m v) ∘ s) (and p q) : by unfold holds
  },
  case formula.or : p q ih_p ih_q {
    calc
    holds T m v (sub_formula s (or p q)) ↔ holds T m v (or (sub_formula s p) (sub_formula s q)) : by unfold sub_formula
    ... ↔ (holds T m v (sub_formula s p)) ∨ (holds T m v (sub_formula s q)) : by unfold holds
    ... ↔ (holds T m ((eval_term T m v) ∘ s) p) ∨ (holds T m ((eval_term T m v) ∘ s) q) :
        begin rewrite ih_p s v, rewrite ih_q s v end
    ... ↔ holds T m ((eval_term T m v) ∘ s) (or p q) : by unfold holds
  },
  case formula.imp : p q ih_p ih_q {
    calc
    holds T m v (sub_formula s (imp p q)) ↔ holds T m v (imp (sub_formula s p) (sub_formula s q)) : by unfold sub_formula
    ... ↔ (holds T m v (sub_formula s p)) → (holds T m v (sub_formula s q)) : by unfold holds
    ... ↔ (holds T m ((eval_term T m v) ∘ s) p) → (holds T m ((eval_term T m v) ∘ s) q) :
        begin rewrite ih_p s v, rewrite ih_q s v end
    ... ↔ holds T m ((eval_term T m v) ∘ s) (imp p q) : by unfold holds
  },
  case formula.iff : p q ih_p ih_q {
    calc
    holds T m v (sub_formula s (iff p q)) ↔ holds T m v (iff (sub_formula s p) (sub_formula s q)) : by unfold sub_formula
    ... ↔ ((holds T m v (sub_formula s p)) ↔ (holds T m v (sub_formula s q))) : by unfold holds
    ... ↔ ((holds T m ((eval_term T m v) ∘ s) p) ↔ (holds T m ((eval_term T m v) ∘ s) q)) :
        begin rewrite ih_p s v, rewrite ih_q s v end
    ... ↔ holds T m ((eval_term T m v) ∘ s) (iff p q) : by unfold holds
  },
  case formula.forall_ : x p ih {
    let x' :=
      if ∃ y ∈ p.free_var_set \ {x}, x ∈ (s y).all_var_set
      then variant x (sub_formula ([x ↦ var x] s) p).free_var_set
      else x,
    have s1 : ∀ a ∈ m.domain, ∀ z ∈ p.free_var_set,
      ((eval_term T m ([x' ↦ a] v)) ∘ ([x ↦ (var x')] s)) z = ([x ↦ a] ((eval_term T m v) ∘ s)) z,
      intros a h2 z h1,
      by_cases z = x, {
        calc
        ((eval_term T m ([x' ↦ a] v)) ∘ ([x ↦ (var x')] s)) z =
              ((eval_term T m ([x' ↦ a] v)) ∘ ([x ↦ (var x')] s)) x : by rewrite h
        ... = (eval_term T m ([x' ↦ a] v)) (([x ↦ (var x')] s) x) : by simp only [function.comp_app]
        ... = (eval_term T m ([x' ↦ a] v)) (var x') : by simp only [function.update_same]
        ... = ([x' ↦ a] v) x' : by unfold eval_term
        ... = a : by simp only [function.update_same]
        ... = ([x ↦ a] ((eval_term T m v) ∘ s)) x : by simp only [function.update_same]
        ... = ([x ↦ a] ((eval_term T m v) ∘ s)) z : by rewrite h
      },
      {
        have s2 : z ∈ p.free_var_set \ {x}, simp only [finset.mem_sdiff, finset.mem_singleton], exact and.intro h1 h,
        have s3 : x' ∉ finset.bUnion (p.free_var_set \ {x}) (fun y : string, (s y).all_var_set),
          exact lem_3_6_1 x p s (lem_3_6 p),
        have s4 : (s z).all_var_set ⊆ finset.bUnion (p.free_var_set \ {x}) (fun y : string, (s y).all_var_set),
          exact finset.subset_bUnion_of_mem (fun y : string, (s y).all_var_set) s2,
        have s5 : x' ∉ (s z).all_var_set, exact finset.not_mem_mono s4 s3,
        have s6 : ∀ (x : string), x ∈ (s z).all_var_set → x ≠ x', intros y h3, by_contradiction, apply s5, rewrite <- h, exact h3,
        calc
        ((eval_term T m ([x' ↦ a] v)) ∘ ([x ↦ (var x')] s)) z =
              (eval_term T m ([x' ↦ a] v)) (([x ↦ (var x')] s) z) : by simp only [function.comp_app]
        ... = (eval_term T m ([x' ↦ a] v)) (s z) : by simp only [function.update_noteq h]
        ... = eval_term T m v (s z) : begin apply thm_3_1 ([x' ↦ a] v) v, intros x h3,
                                      apply function.update_noteq, exact s6 x h3 end
        ... = ((eval_term T m v) ∘ s) z : by simp only [eq_self_iff_true]
        ... = ([x ↦ a] ((eval_term T m v) ∘ s)) z : begin symmetry, apply function.update_noteq h end
      },
    calc
    holds T m v (sub_formula s (forall_ x p))
      ↔ holds T m v (forall_ x' (sub_formula ([x ↦ (var x')] s) p)) : by unfold sub_formula
    ... ↔ ∀ a ∈ m.domain, holds T m ([x' ↦ a] v) (sub_formula ([x ↦ (var x')] s) p) : by unfold holds
    ... ↔ (∀ a ∈ m.domain, (holds T m ((eval_term T m ([x' ↦ a] v)) ∘ ([x ↦ (var x')] s)) p)) : by finish
    ... ↔ (∀ a ∈ m.domain, holds T m ([x ↦ a] ((eval_term T m v) ∘ s)) p) :
      begin split,
      intros h1 a h2,
      rewrite <- (thm_3_2 ((eval_term T m ([x' ↦ a] v)) ∘ ([x ↦ (var x')] s)) ([x ↦ a] ((eval_term T m v) ∘ s)) (s1 a h2)), exact h1 a h2,
      intros h1 a h2,
      rewrite (thm_3_2 ((eval_term T m ([x' ↦ a] v)) ∘ ([x ↦ (var x')] s)) ([x ↦ a] ((eval_term T m v) ∘ s)) (s1 a h2)), exact h1 a h2
      end
    ... ↔ holds T m (eval_term T m v ∘ s) (forall_ x p) : by unfold holds
  },
  case formula.exists_ : x p ih {
    let x' :=
      if ∃ y ∈ p.free_var_set \ {x}, x ∈ (s y).all_var_set
      then variant x (sub_formula ([x ↦ var x] s) p).free_var_set
      else x,
    have s1 : ∀ a ∈ m.domain, ∀ z ∈ p.free_var_set,
      ((eval_term T m ([x' ↦ a] v)) ∘ ([x ↦ (var x')] s)) z = ([x ↦ a] ((eval_term T m v) ∘ s)) z,
      intros a h2 z h1,
      by_cases z = x, {
        calc
        ((eval_term T m ([x' ↦ a] v)) ∘ ([x ↦ (var x')] s)) z =
              ((eval_term T m ([x' ↦ a] v)) ∘ ([x ↦ (var x')] s)) x : by rewrite h
        ... = (eval_term T m ([x' ↦ a] v)) (([x ↦ (var x')] s) x) : by simp only [function.comp_app]
        ... = (eval_term T m ([x' ↦ a] v)) (var x') : by simp only [function.update_same]
        ... = ([x' ↦ a] v) x' : by unfold eval_term
        ... = a : by simp only [function.update_same]
        ... = ([x ↦ a] ((eval_term T m v) ∘ s)) x : by simp only [function.update_same]
        ... = ([x ↦ a] ((eval_term T m v) ∘ s)) z : by rewrite h
      },
      {
        have s2 : z ∈ p.free_var_set \ {x}, simp only [finset.mem_sdiff, finset.mem_singleton], exact and.intro h1 h,
        have s3 : x' ∉ finset.bUnion (p.free_var_set \ {x}) (fun y : string, (s y).all_var_set),
          exact lem_3_6_1 x p s (lem_3_6 p),
        have s4 : (s z).all_var_set ⊆ finset.bUnion (p.free_var_set \ {x}) (fun y : string, (s y).all_var_set),
          exact finset.subset_bUnion_of_mem (fun y : string, (s y).all_var_set) s2,
        have s5 : x' ∉ (s z).all_var_set, exact finset.not_mem_mono s4 s3,
        have s6 : ∀ (x : string), x ∈ (s z).all_var_set → x ≠ x', intros y h3, by_contradiction, apply s5, rewrite <- h, exact h3,
        calc
        ((eval_term T m ([x' ↦ a] v)) ∘ ([x ↦ (var x')] s)) z =
              (eval_term T m ([x' ↦ a] v)) (([x ↦ (var x')] s) z) : by simp only [function.comp_app]
        ... = (eval_term T m ([x' ↦ a] v)) (s z) : by simp only [function.update_noteq h]
        ... = eval_term T m v (s z) : begin apply thm_3_1 ([x' ↦ a] v) v, intros x h3,
                                      apply function.update_noteq, exact s6 x h3 end
        ... = ((eval_term T m v) ∘ s) z : by simp only [eq_self_iff_true]
        ... = ([x ↦ a] ((eval_term T m v) ∘ s)) z : begin symmetry, apply function.update_noteq h end
      },
    calc
    holds T m v (sub_formula s (exists_ x p))
      ↔ holds T m v (exists_ x' (sub_formula ([x ↦ (var x')] s) p)) : by unfold sub_formula
    ... ↔ ∃ a ∈ m.domain, holds T m ([x' ↦ a] v) (sub_formula ([x ↦ (var x')] s) p) : by unfold holds
    ... ↔ (∃ a ∈ m.domain, (holds T m ((eval_term T m ([x' ↦ a] v)) ∘ ([x ↦ (var x')] s)) p)) : by finish
    ... ↔ (∃ a ∈ m.domain, holds T m ([x ↦ a] ((eval_term T m v) ∘ s)) p) :
    begin
      split,
      intros h1, cases h1 with a h2, cases h2 with h3 h4, apply exists.intro a, apply exists.intro h3,
      rewrite <- thm_3_2 ((eval_term T m ([x' ↦ a] v)) ∘ ([x ↦ (var x')] s)) ([x ↦ a] ((eval_term T m v) ∘ s)) (s1 a h3),
      exact h4,
      intros h1, cases h1 with a h2, cases h2 with h3 h4, apply exists.intro a, apply exists.intro h3,
      rewrite thm_3_2 ((eval_term T m ([x' ↦ a] v)) ∘ ([x ↦ (var x')] s)) ([x ↦ a] ((eval_term T m v) ∘ s)) (s1 a h3),
      exact h4
    end
    ... ↔ holds T m (eval_term T m v ∘ s) (exists_ x p) : by unfold holds
  }
end

theorem cor_3_8
  (p : formula)
  (s : instantiation)
  (h1 : is_valid p) :
  is_valid (sub_formula s p) :=
begin
  sorry
end
-/
