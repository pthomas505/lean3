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


-- #eval not (forall_ "x" (mk_pred "P" [mk_func "f" [(var "x")], var "y"]))


/-
domain: A nonempty set D called the domain of the interpretation. The intention is that all terms have values in D.

nonempty: A proof that there is at least one element in the domain.

func: (n : ℕ, f : string) → (f_{M} : (terms : fin n → domain) → v : domain)
A mapping of each n-ary function symbol f to a function f_{M}.
n : The arity of the function symbol.
f : The function symbol.
f_{M} : The function that the function symbol is mapped to.
terms : fin n → domain : The n terms (arguments) of the function expressed as a finite function.
v : domain : The result of the function. An element in the domain.

pred: (n : ℕ, P : string) → (P_{M} : (terms : fin n → domain) → v : Prop)
A mapping of each n-ary predicate symbol P to a predicate P_{M}.
n : The arity of the predicate symbol.
P : The predicate symbol.
P_{M} : The predicate that the predicate symbol is mapped to.
terms : fin n → domain : The n terms (arguments) of the predicate expressed as a finite function.
v : Prop : The result of the predicate. True or false.
-/
structure interpretation (domain : Type) : Type :=
(nonempty : nonempty domain)
(func (n : ℕ) : string → (fin n → domain) → domain)
(pred (n : ℕ) : string → (fin n → domain) → Prop)


/-
The type of mappings of object variable names to elements of a domain.
-/
def valuation (D : Type) := string → D

/-
The function mapping each term to an element of a domain by a given interpretation and valuation.
-/
def eval_term (D : Type) (m : interpretation D) (v : valuation D) : term → D
| (var x) := v x
| (func n f terms) := m.func n f (fun i : fin n, eval_term (terms i))

/-
f is a function. a' is an element in the domain of f. v is an element in the range of f.
if y = a' then (`[` a' `↦` v `]` f) y = v
if y ≠ a' then (`[` a' `↦` v `]` f) y = f y
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


def holds (D : Type) (m : interpretation D) : valuation D → formula → Prop
| _ bottom := false
| _ top := true
| v (atom n x terms) := m.pred n x (fun i : fin n, eval_term D m v (terms i))
| v (not p) := ¬ holds v p
| v (and p q) := holds v p ∧ holds v q
| v (or p q) := holds v p ∨ holds v q
| v (imp p q) := holds v p → holds v q
| v (iff p q) := holds v p ↔ holds v q
| v (forall_ x p) := ∀ a : D, holds ([x ↦ a] v) p
| v (exists_ x p) := ∃ a : D, holds ([x ↦ a] v) p


def term.all_var_set : term → finset string
| (var x) := {x}
| (func n f terms) := finset.bUnion finset.univ (fun i : fin n, (terms i).all_var_set)


theorem thm_3_1
  {D : Type}
  {m : interpretation D}
  {t : term}
  (v v' : valuation D)
  (h1 : ∀ x ∈ t.all_var_set, v x = v' x) :
  eval_term D m v t = eval_term D m v' t :=
begin
  induction t,
  case term.var : x {
    have s1 : x ∈ (var x).all_var_set, unfold term.all_var_set, simp only [finset.mem_singleton],
    calc
          eval_term D m v (var x)
        = v x : by unfold eval_term
    ... = v' x : h1 x s1
    ... = eval_term D m v' (var x) : by unfold eval_term
  },
  case term.func : n f terms ih {
    calc
          eval_term D m v (func n f terms)
        = m.func n f (fun i : fin n, eval_term D m v (terms i)) : by unfold eval_term
    ... = m.func n f (fun i : fin n, eval_term D m v' (terms i)) :
      begin
        congr, funext, apply ih,
        intros x h2, apply h1, unfold term.all_var_set,
        simp only [finset.mem_bUnion, finset.mem_univ, exists_true_left], exact exists.intro i h2
      end
    ... = eval_term D m v' (func n f terms) : by unfold eval_term
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
  {D : Type}
  {m : interpretation D}
  {p : formula}
  (v v' : valuation D)
  (h1 : ∀ x ∈ p.free_var_set, v x = v' x) :
  holds D m v p ↔ holds D m v' p :=
begin
  induction p generalizing v v',
  case formula.bottom {
    calc
          holds D m v bottom
        ↔ false : by unfold holds
    ... ↔ holds D m v' bottom : by unfold holds
  },
  case formula.top {
    calc
          holds D m v top
        ↔ true : by unfold holds
    ... ↔ holds D m v' top : by unfold holds
  },
  case formula.atom : n x terms {
    unfold formula.free_var_set at h1,
    calc
        holds D m v (atom n x terms)
        ↔ m.pred n x (fun i : fin n, eval_term D m v (terms i)) : by unfold holds
    ... ↔ m.pred n x (fun i : fin n, eval_term D m v' (terms i)) :
      begin
        apply iff_of_eq, congr, funext,
        apply thm_3_1, intros x h, apply h1, simp only [finset.mem_bUnion, finset.mem_univ, exists_true_left], exact exists.intro i h
      end
    ... ↔ holds D m v' (atom n x terms) : by unfold holds
  },
  case formula.not : p ih {
    unfold formula.free_var_set at h1,
    have s1 : holds D m v p ↔ holds D m v' p, exact ih v v' h1,
    calc
          holds D m v (not p)
        ↔ ¬ holds D m v p : by unfold holds
    ... ↔ ¬ holds D m v' p : by simp only [s1]
    ... ↔ holds D m v' (not p) : by unfold holds
  },
  case formula.and : p q ih_p ih_q {
    unfold formula.free_var_set at h1, simp only [finset.mem_union, or_imp_distrib, forall_and_distrib] at h1, cases h1,
    have s1 : holds D m v p ↔ holds D m v' p, exact ih_p v v' h1_left,
    have s2 : holds D m v q ↔ holds D m v' q, exact ih_q v v' h1_right,
    calc
          holds D m v (and p q)
        ↔ (holds D m v p ∧ holds D m v q) : by unfold holds
    ... ↔ (holds D m v' p ∧ holds D m v' q) : by simp only [s1, s2]
    ... ↔ holds D m v' (and p q) : by unfold holds
  },
  case formula.or : p q ih_p ih_q {
    unfold formula.free_var_set at h1, simp only [finset.mem_union, or_imp_distrib, forall_and_distrib] at h1, cases h1,
    have s1 : holds D m v p ↔ holds D m v' p, exact ih_p v v' h1_left,
    have s2 : holds D m v q ↔ holds D m v' q, exact ih_q v v' h1_right,
    calc
          holds D m v (or p q)
        ↔ (holds D m v p ∨ holds D m v q) : by unfold holds
    ... ↔ (holds D m v' p ∨ holds D m v' q) : by simp only [s1, s2]
    ... ↔ holds D m v' (or p q) : by unfold holds
  },
  case formula.imp : p q ih_p ih_q {
    unfold formula.free_var_set at h1, simp only [finset.mem_union, or_imp_distrib, forall_and_distrib] at h1, cases h1,
    have s1 : holds D m v p ↔ holds D m v' p, exact ih_p v v' h1_left,
    have s2 : holds D m v q ↔ holds D m v' q, exact ih_q v v' h1_right,
    calc
          holds D m v (imp p q)
        ↔ (holds D m v p → holds D m v q) : by unfold holds
    ... ↔ (holds D m v' p → holds D m v' q) : by simp only [s1, s2]
    ... ↔ holds D m v' (imp p q) : by unfold holds
  },
  case formula.iff : p q ih_p ih_q {
    unfold formula.free_var_set at h1, simp only [finset.mem_union, or_imp_distrib, forall_and_distrib] at h1, cases h1,
    have s1 : holds D m v p ↔ holds D m v' p, exact ih_p v v' h1_left,
    have s2 : holds D m v q ↔ holds D m v' q, exact ih_q v v' h1_right,
    calc
          holds D m v (iff p q)
        ↔ (holds D m v p ↔ holds D m v q) : by unfold holds
    ... ↔ (holds D m v' p ↔ holds D m v' q) : by simp only [s1, s2]
    ... ↔ holds D m v' (iff p q) : by unfold holds
  },
  case formula.forall_ : x p ih {
    unfold formula.free_var_set at h1, simp only [finset.mem_sdiff, finset.mem_singleton] at h1,
    calc
          holds D m v (forall_ x p)
        ↔ ∀ a : D, holds D m ([x ↦ a] v) p : by unfold holds
    ... ↔ ∀ a : D, holds D m ([x ↦ a] v') p :
      begin
        apply forall_congr, intros a, apply ih, intros y h3,
        by_cases y = x,
        rewrite h, simp only [function.update_same],
        simp only [function.update_noteq h], apply h1, exact and.intro h3 h
      end
    ... ↔ holds D m v' (forall_ x p) : by unfold holds
  },
  case formula.exists_ : x p ih {
    unfold formula.free_var_set at h1, simp only [finset.mem_sdiff, finset.mem_singleton] at h1,
    calc
          holds D m v (exists_ x p)
        ↔ ∃ a : D, holds D m ([x ↦ a] v) p : by unfold holds
    ... ↔ ∃ a : D, holds D m ([x ↦ a] v') p :
      begin
        apply exists_congr, intros a, apply ih, intros y h3,
        by_cases y = x,
        rewrite h, simp only [function.update_same],
        simp only [function.update_noteq h], apply h1, exact and.intro h3 h
      end
    ... ↔ holds D m v' (exists_ x p) : by unfold holds
  }
end


def is_sentence (p : formula) : Prop :=
p.free_var_set = ∅


theorem cor_3_3
  {p : formula}
  {D : Type}
  {m : interpretation D}
  (v v' : valuation D)
  (h1 : is_sentence p) :
  holds D m v p ↔ holds D m v' p :=
begin
  unfold is_sentence at h1,
  have s1 : ∀ x ∈ p.free_var_set, v x = v' x,
    rewrite h1, simp only [finset.not_mem_empty, forall_false_left, forall_const],
  exact thm_3_2 v v' s1
end


def is_valid (p : formula) : Prop :=
∀ D : Type, ∀ m : interpretation D, ∀ v : valuation D, holds D m v p


/-
satisfies D m p = m satisfies p.
-/
def satisfies (D : Type) (m : interpretation D) (p : formula) : Prop :=
∀ v : valuation D, holds D m v p

/-
satisfies_set D m S = m satisfies S.
-/
def satisfies_set (D : Type) (m : interpretation D) (S : set formula) : Prop :=
∀ p ∈ S, satisfies D m p


def is_satisfiable (p : formula) : Prop :=
∃ D : Type, ∃ m : interpretation D, satisfies D m p

def is_satisfiable_set (S : set formula) : Prop :=
∃ D : Type, ∃ m : interpretation D, ∀ p ∈ S, satisfies D m p


/-
holds_in p D m = p holds in m.
-/
def holds_in (p : formula) (D : Type) (m : interpretation D) : Prop :=
satisfies D m p

/-
set_holds_in S D m = S holds in m.
-/
def set_holds_in (S : set formula) (D : Type) (m : interpretation D) : Prop :=
satisfies_set D m S


example
	(p : formula)
	(h1 : is_sentence p) :
	is_valid p ↔ ¬ (is_satisfiable (not p)) :=
begin
  have s1 : (∀ (D : Type) (m : interpretation D) (v : valuation D), holds D m v p) →
    ∀ (D : Type) (m : interpretation D), ∃ (v : valuation D), holds D m v p,
      intros h2 D m, let v := fun _ : string, m.nonempty.some, exact exists.intro v (h2 D m v),
  have s2 : (∀ (D : Type) (m : interpretation D), ∃ (v : valuation D), holds D m v p) →
    ∀ (D : Type) (m : interpretation D) (v : valuation D), holds D m v p,
      intros h2 D m v, apply exists.elim, exact h2 D m, intros v', exact iff.elim_right (cor_3_3 v v' h1),
  calc
        is_valid p
      ↔ ∀ (D : Type) (m : interpretation D) (v : valuation D), holds D m v p : by unfold is_valid
  ... ↔ ∀ (D : Type) (m : interpretation D), ∃ (v : valuation D), holds D m v p : iff.intro s1 s2
  ... ↔ ¬∃ (D : Type) (m : interpretation D), ∀ (v : valuation D), ¬holds D m v p : begin push_neg, refl end
  ... ↔ ¬∃ (D : Type) (m : interpretation D), ∀ (v : valuation D), holds D m v (not p) : by unfold holds
  ... ↔ ¬∃ (D : Type) (m : interpretation D), satisfies D m (not p) : by unfold satisfies
  ... ↔ ¬is_satisfiable (not p) : by unfold is_satisfiable
end


/-
is_model_of D m Γ = m is a model of Γ
-/
def is_model_of (D : Type) (m : interpretation D) (Γ : set formula) :=
satisfies_set D m Γ


/-
Γ ⊨ p = p holds in all models of Γ.
-/
notation Γ `⊨` p := ∀ D : Type, ∀ m : interpretation D, (is_model_of D m Γ) → (holds_in p D m)


example
	(p : formula) :
	(is_valid p) ↔ (∅ ⊨ p) :=
begin
  split,
  {
    unfold is_valid, unfold holds_in, unfold satisfies, intros h1 D m h2, exact h1 D m
  },
  {
    unfold is_valid, unfold is_model_of, unfold satisfies_set, unfold holds_in,
    unfold satisfies, simp only [set.mem_empty_eq],
    intros h1 D m v, apply h1, intros p h2, contradiction
  }
end


example
	(Γ : set formula) :
	¬ (is_satisfiable_set Γ) ↔ (Γ ⊨ bottom) :=
begin
  unfold is_model_of, unfold is_satisfiable_set, unfold satisfies_set, unfold holds_in, unfold satisfies,
  split,
  {
    intros h1 D m h2 v, unfold holds, apply h1, apply exists.intro D, exact exists.intro m h2
  },
  {
    intros h1, push_neg, intros D m, by_contradiction, push_neg at h,
    exact h1 D m h (fun _ : string, m.nonempty.some)
  }
end


example
	(D : Type)
	(m : interpretation D)
	(p : formula) :
	(∀ x : string, ∀ v : valuation D, ∀ a : D, holds D m ([x ↦ a] v) p) ↔ (∀ v : valuation D, holds D m v p) :=
begin
  split,
  intros h1 v,
  rewrite <- function.update_eq_self default v, exact h1 default v (v default),
  intros h1 x v a, exact h1 ([x ↦ a] v)
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
  (D : Type)
  (t : term)
  (s : instantiation)
  (m : interpretation D)
  (v : valuation D) :
  eval_term D m v (sub_term s t) = eval_term D m ((eval_term D m v) ∘ s) t :=
begin
  induction t,
  case term.var : x {
    calc
          eval_term D m v (sub_term s (var x))
        = eval_term D m v (s x) : by unfold sub_term
    ... = ((eval_term D m v) ∘ s) x : by unfold function.comp
    ... = eval_term D m ((eval_term D m v) ∘ s) (var x) : by unfold eval_term
  },
  case term.func : n f terms ih {
    have ih' : ∀ (i : fin n), eval_term D m v (sub_term s (terms i)) =
      eval_term D m ((eval_term D m v) ∘ s) (terms i), exact ih,
    calc
          eval_term D m v (sub_term s (func n f terms))
        = eval_term D m v (func n f (fun i, sub_term s (terms i))) : by unfold sub_term
    ... = m.func n f (fun i, eval_term D m v (sub_term s (terms i))) : by unfold eval_term
    ... = m.func n f (fun i, eval_term D m ((eval_term D m v) ∘ s) (terms i)) : begin congr, apply funext, exact ih' end
    ... = eval_term D m ((eval_term D m v) ∘ s) (func n f terms) : by unfold eval_term
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
    calc
          (sub_formula_simp s (or p q)).free_var_set
        = (or (sub_formula_simp s p) (sub_formula_simp s q)).free_var_set : by unfold sub_formula_simp
    ... = (sub_formula_simp s p).free_var_set ∪ (sub_formula_simp s q).free_var_set : by unfold formula.free_var_set
    ... = finset.bUnion p.free_var_set (fun y : string, (s y).all_var_set) ∪
            finset.bUnion q.free_var_set (fun y : string, (s y).all_var_set) :
          begin
            unfold sub_admits at h1, cases h1,
            congr, exact ih_p s h1_left, exact ih_q s h1_right,
          end
    ... = finset.bUnion (p.free_var_set ∪ q.free_var_set) (fun y : string, (s y).all_var_set) : by simp [finset.bUnion_union, finset.union_comm]
    ... = finset.bUnion (or p q).free_var_set (fun y : string, (s y).all_var_set) : by unfold formula.free_var_set
  },
  case formula.imp : p q ih_p ih_q {
    calc
          (sub_formula_simp s (imp p q)).free_var_set
        = (imp (sub_formula_simp s p) (sub_formula_simp s q)).free_var_set : by unfold sub_formula_simp
    ... = (sub_formula_simp s p).free_var_set ∪ (sub_formula_simp s q).free_var_set : by unfold formula.free_var_set
    ... = finset.bUnion p.free_var_set (fun y : string, (s y).all_var_set) ∪
            finset.bUnion q.free_var_set (fun y : string, (s y).all_var_set) :
          begin
            unfold sub_admits at h1, cases h1,
            congr, exact ih_p s h1_left, exact ih_q s h1_right,
          end
    ... = finset.bUnion (p.free_var_set ∪ q.free_var_set) (fun y : string, (s y).all_var_set) : by simp [finset.bUnion_union, finset.union_comm]
    ... = finset.bUnion (imp p q).free_var_set (fun y : string, (s y).all_var_set) : by unfold formula.free_var_set
  },
  case formula.iff : p q ih_p ih_q {
    calc
          (sub_formula_simp s (iff p q)).free_var_set
        = (iff (sub_formula_simp s p) (sub_formula_simp s q)).free_var_set : by unfold sub_formula_simp
    ... = (sub_formula_simp s p).free_var_set ∪ (sub_formula_simp s q).free_var_set : by unfold formula.free_var_set
    ... = finset.bUnion p.free_var_set (fun y : string, (s y).all_var_set) ∪
            finset.bUnion q.free_var_set (fun y : string, (s y).all_var_set) :
          begin
            unfold sub_admits at h1, cases h1,
            congr, exact ih_p s h1_left, exact ih_q s h1_right,
          end
    ... = finset.bUnion (p.free_var_set ∪ q.free_var_set) (fun y : string, (s y).all_var_set) : by simp [finset.bUnion_union, finset.union_comm]
    ... = finset.bUnion (iff p q).free_var_set (fun y : string, (s y).all_var_set) : by unfold formula.free_var_set
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
    unfold sub_admits at h1, cases h1, cases h1_right,
    calc
          (sub_formula_simp s (exists_ x p)).free_var_set
        = (exists_ x (sub_formula_simp s p)).free_var_set :
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
    ... = finset.bUnion (exists_ x p).free_var_set (fun y : string, (s y).all_var_set) : by unfold formula.free_var_set
  }
end


theorem thm_3_7_simp
  {D : Type}
  {m : interpretation D}
  (v : valuation D)
  (s : instantiation)
  (p : formula)
  (h1 : sub_admits s p) :
  holds D m v (sub_formula_simp s p) ↔ holds D m ((eval_term D m v) ∘ s) p :=
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
    holds D m v (sub_formula_simp s (atom n x terms)) ↔
      holds D m v (atom n x (fun i : fin n, sub_term s (terms i))) : by unfold sub_formula_simp
    ... ↔ m.pred n x (fun i : fin n, eval_term D m v (sub_term s (terms i))) : by unfold holds
    ... ↔ m.pred n x (fun i : fin n, eval_term D m ((eval_term D m v) ∘ s) (terms i)) : by simp only [lem_3_5]
    ... ↔ holds D m ((eval_term D m v) ∘ s) (atom n x terms) : by unfold holds
  },
  case formula.not : p ih {
    calc
    holds D m v (sub_formula_simp s (not p)) ↔ holds D m v (not (sub_formula_simp s p)) : by unfold sub_formula_simp
    ... ↔ ¬ holds D m v (sub_formula_simp s p) : by unfold holds
    ... ↔ ¬ holds D m ((eval_term D m v) ∘ s) p : begin unfold sub_admits at h1, rewrite ih s v h1 end
    ... ↔ holds D m ((eval_term D m v) ∘ s) (not p) : by unfold holds
  },
  case formula.and : p q ih_p ih_q {
    calc
    holds D m v (sub_formula_simp s (and p q)) ↔ holds D m v (and (sub_formula_simp s p) (sub_formula_simp s q)) : by unfold sub_formula_simp
    ... ↔ (holds D m v (sub_formula_simp s p)) ∧ (holds D m v (sub_formula_simp s q)) : by unfold holds
    ... ↔ (holds D m ((eval_term D m v) ∘ s) p) ∧ (holds D m ((eval_term D m v) ∘ s) q) :
        begin unfold sub_admits at h1, cases h1, rewrite ih_p s v h1_left, rewrite ih_q s v h1_right end
    ... ↔ holds D m ((eval_term D m v) ∘ s) (and p q) : by unfold holds
  },
  case formula.or : p q ih_p ih_q {
    calc
    holds D m v (sub_formula_simp s (or p q)) ↔ holds D m v (or (sub_formula_simp s p) (sub_formula_simp s q)) : by unfold sub_formula_simp
    ... ↔ (holds D m v (sub_formula_simp s p)) ∨ (holds D m v (sub_formula_simp s q)) : by unfold holds
    ... ↔ (holds D m ((eval_term D m v) ∘ s) p) ∨ (holds D m ((eval_term D m v) ∘ s) q) :
        begin unfold sub_admits at h1, cases h1, rewrite ih_p s v h1_left, rewrite ih_q s v h1_right end
    ... ↔ holds D m ((eval_term D m v) ∘ s) (or p q) : by unfold holds
  },
  case formula.imp : p q ih_p ih_q {
    calc
    holds D m v (sub_formula_simp s (imp p q)) ↔ holds D m v (imp (sub_formula_simp s p) (sub_formula_simp s q)) : by unfold sub_formula_simp
    ... ↔ (holds D m v (sub_formula_simp s p)) → (holds D m v (sub_formula_simp s q)) : by unfold holds
    ... ↔ (holds D m ((eval_term D m v) ∘ s) p) → (holds D m ((eval_term D m v) ∘ s) q) :
        begin unfold sub_admits at h1, cases h1, rewrite ih_p s v h1_left, rewrite ih_q s v h1_right end
    ... ↔ holds D m ((eval_term D m v) ∘ s) (imp p q) : by unfold holds
  },
  case formula.iff : p q ih_p ih_q {
    calc
    holds D m v (sub_formula_simp s (iff p q)) ↔ holds D m v (iff (sub_formula_simp s p) (sub_formula_simp s q)) : by unfold sub_formula_simp
    ... ↔ ((holds D m v (sub_formula_simp s p)) ↔ (holds D m v (sub_formula_simp s q))) : by unfold holds
    ... ↔ ((holds D m ((eval_term D m v) ∘ s) p) ↔ (holds D m ((eval_term D m v) ∘ s) q)) :
        begin unfold sub_admits at h1, cases h1, rewrite ih_p s v h1_left, rewrite ih_q s v h1_right end
    ... ↔ holds D m ((eval_term D m v) ∘ s) (iff p q) : by unfold holds
  },
  case formula.forall_ : x p ih {
    begin
      unfold sub_admits at h1, cases h1, cases h1_right,
      calc
            holds D m v (sub_formula_simp s (forall_ x p))
          ↔ holds D m v (forall_ x (sub_formula_simp s p)) : by unfold sub_formula_simp
      ... ↔ (∀ a : D, holds D m ([x ↦ a] v) (sub_formula_simp s p)) : by unfold holds
      ... ↔ (∀ a : D, holds D m (eval_term D m ([x ↦ a] v) ∘ s) p) :
            begin
              apply forall_congr, intros a,
              exact ih s ([x ↦ a] v) h1_right_left
            end
      ... ↔ (∀ a : D, holds D m ([x ↦ a] eval_term D m v ∘ s) p) :
            begin
              apply forall_congr, intros a,
              apply thm_3_2, intros z h2,
              by_cases z = x,
              {
                calc
                      (eval_term D m ([x ↦ a] v) ∘ s) z
                    = (eval_term D m ([x ↦ a] v) ∘ s) x : by rewrite h
                ... = eval_term D m ([x ↦ a] v) (s x) : by unfold function.comp
                ... = eval_term D m ([x ↦ a] v) (var x) : by rewrite h1_left
                ... = ([x ↦ a] v) x : by unfold eval_term
                ... = a : by simp only [function.update_same]
                ... = ([x ↦ a] eval_term D m v ∘ s) x : by simp only [function.update_same]
                ... = ([x ↦ a] eval_term D m v ∘ s) z : by rewrite h
              },
              {
                calc
                      (eval_term D m ([x ↦ a] v) ∘ s) z
                    = eval_term D m ([x ↦ a] v) (s z) : by unfold function.comp
                ... = eval_term D m v (s z) :
                      begin
                        apply thm_3_1, intros y h3,
                        apply function.update_noteq, intros h4, apply h1_right_right z,
                        simp only [finset.mem_sdiff, finset.mem_singleton], exact and.intro h2 h,
                        rewrite h4 at h3, exact h3
                      end
                ... = (eval_term D m v ∘ s) z : by unfold function.comp
                ... = ([x ↦ a] eval_term D m v ∘ s) z : by simp only [function.update_noteq h]
              }
            end
      ... ↔ holds D m (eval_term D m v ∘ s) (forall_ x p) : by unfold holds
    end
  },
  case formula.exists_ : x p ih {
    begin
      unfold sub_admits at h1, cases h1, cases h1_right,
      calc
            holds D m v (sub_formula_simp s (exists_ x p))
          ↔ holds D m v (exists_ x (sub_formula_simp s p)) : by unfold sub_formula_simp
      ... ↔ (∃ a : D, holds D m ([x ↦ a] v) (sub_formula_simp s p)) : by unfold holds
      ... ↔ (∃ a : D, holds D m (eval_term D m ([x ↦ a] v) ∘ s) p) :
            begin
              apply exists_congr, intros a,
              exact ih s ([x ↦ a] v) h1_right_left
            end
      ... ↔ (∃ a : D, holds D m ([x ↦ a] eval_term D m v ∘ s) p) :
            begin
              apply exists_congr, intros a,
              apply thm_3_2, intros z h2,
              by_cases z = x,
              {
                calc
                      (eval_term D m ([x ↦ a] v) ∘ s) z
                    = (eval_term D m ([x ↦ a] v) ∘ s) x : by rewrite h
                ... = eval_term D m ([x ↦ a] v) (s x) : by unfold function.comp
                ... = eval_term D m ([x ↦ a] v) (var x) : by rewrite h1_left
                ... = ([x ↦ a] v) x : by unfold eval_term
                ... = a : by simp only [function.update_same]
                ... = ([x ↦ a] eval_term D m v ∘ s) x : by simp only [function.update_same]
                ... = ([x ↦ a] eval_term D m v ∘ s) z : by rewrite h
              },
              {
                calc
                      (eval_term D m ([x ↦ a] v) ∘ s) z
                    = eval_term D m ([x ↦ a] v) (s z) : by unfold function.comp
                ... = eval_term D m v (s z) :
                      begin
                        apply thm_3_1, intros y h3,
                        apply function.update_noteq, intros h4, apply h1_right_right z,
                        simp only [finset.mem_sdiff, finset.mem_singleton], exact and.intro h2 h,
                        rewrite h4 at h3, exact h3
                      end
                ... = (eval_term D m v ∘ s) z : by unfold function.comp
                ... = ([x ↦ a] eval_term D m v ∘ s) z : by simp only [function.update_noteq h]
              }
            end
      ... ↔ holds D m (eval_term D m v ∘ s) (exists_ x p) : by unfold holds
    end
  }
end


theorem cor_3_8_simp
  (p : formula)
  (s : instantiation)
  (h1 : sub_admits s p)
  (h2 : is_valid p) :
  is_valid (sub_formula_simp s p) :=
begin
  unfold is_valid at *,
  intros D m v,
  simp only [thm_3_7_simp v s p h1], apply h2
end


def alpha_eqv_var : list (string × string) → string → string → Prop
| list.nil x y := x = y
| ((a, b) :: m) x y := if x = a then b = y else b ≠ y ∧ alpha_eqv_var m x y

inductive alpha_eqv_term (m : list (string × string)) : term → term → Prop
| var (x : string) (y : string) :
  alpha_eqv_var m x y → alpha_eqv_term (var x) (var y)
| func (n : ℕ) (f : string) (terms terms' : fin n → term) :
  (∀ i : fin n, alpha_eqv_term (terms i) (terms' i)) →
    alpha_eqv_term (func n f terms) (func n f terms')

inductive alpha_eqv : list (string × string) -> formula → formula → Prop
| bottom (m : list (string × string)) :
  alpha_eqv m bottom bottom
| top (m : list (string × string)) :
  alpha_eqv m top top
| atom (m : list (string × string)) (n : ℕ) (p : string) (terms terms' : fin n → term) :
  (∀ i : fin n, alpha_eqv_term m (terms i) (terms' i)) →
    alpha_eqv m (atom n p terms) (atom n p terms')
| not (m : list (string × string)) (p p' : formula) :
  alpha_eqv m p p' → alpha_eqv m (not p) (not p')
| and (m : list (string × string)) (p p' q q' : formula) :
  alpha_eqv m p p' → alpha_eqv m q q' → alpha_eqv m (and p q) (and p' q')
| or (m : list (string × string)) (p p' q q' : formula) :
  alpha_eqv m p p' → alpha_eqv m q q' → alpha_eqv m (or p q) (or p' q')
| imp (m : list (string × string)) (p p' q q' : formula) :
  alpha_eqv m p p' → alpha_eqv m q q' → alpha_eqv m (imp p q) (imp p' q')
| iff (m : list (string × string)) (p p' q q' : formula) :
  alpha_eqv m p p' → alpha_eqv m q q' → alpha_eqv m (iff p q) (iff p' q')
| forall_ (m : list (string × string)) (x y : string) (p p' : formula) :
  alpha_eqv ((x, y) :: m) p p' → alpha_eqv m (forall_ x p) (forall_ y p')
| exists_ (m : list (string × string)) (x y : string) (p p' : formula) :
  alpha_eqv ((x, y) :: m) p p' → alpha_eqv m (exists_ x p) (exists_ y p')


theorem is_valid_mp
  (p q : formula)
  (h1 : is_valid p)
  (h2 : is_valid (p.imp q)) :
  is_valid q :=
begin
  unfold is_valid at *, unfold holds at h2,
  intros D m v,
  apply h2, apply h1
end

theorem is_valid_prop_1
  (p q : formula) :
  is_valid (p.imp (q.imp p)) :=
begin
  unfold is_valid, unfold holds,
  intros D m v h1 h2,
  exact h1
end

theorem is_valid_prop_2
  (p q r : formula) :
  is_valid ((p.imp (q.imp r)).imp ((p.imp q).imp (p.imp r))) :=
begin
  unfold is_valid, unfold holds,
  intros D m v h1 h2 h3,
  apply h1, exact h3, apply h2, exact h3
end

theorem is_valid_prop_3
  (p q : formula) :
  is_valid (((not p).imp (not q)).imp (q.imp p)) :=
begin
  unfold is_valid, unfold holds,
  intros D m v h1 h2,
  by_contradiction, apply h1, exact h, exact h2
end


theorem is_valid_gen
  (p : formula)
  (x : string)
  (h1 : is_valid p) :
  is_valid (forall_ x p) :=
begin
  unfold is_valid at *, unfold holds at *,
  intros D m v a,
  apply h1
end

theorem is_valid_pred_1
  (p q : formula)
  (x : string):
  is_valid ((forall_ x (p.imp q)).imp ((forall_ x p).imp (forall_ x q))) :=
begin
  unfold is_valid, unfold holds,
  intros D m v h1 h2 a,
  apply h1 a, exact h2 a
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
  intros D m v h2,
  simp only [thm_3_7_simp v (sub_single_var x t) p h1],
  have s1 : ((eval_term D m v) ∘ (sub_single_var x t)) = ([x ↦ (eval_term D m v t)] v),
    apply funext, intros y, unfold function.comp, unfold sub_single_var,
    by_cases y = x,
    {
      rewrite h, simp only [function.update_same]
    },
    {
      simp only [function.update_noteq h], unfold eval_term
    },
  rewrite s1, apply h2
end

theorem is_valid_pred_3
  (p : formula)
  (x : string)
  (h1 : x ∉ p.free_var_set) :
  is_valid (p.imp (forall_ x p)) :=
begin
  unfold is_valid, unfold holds,
  intros D m v h2 a,
  have s1 : ∀ x' ∈ p.free_var_set, ([x ↦ a] v) x' = v x', intros x' h4, apply function.update_noteq,
    by_contradiction, apply h1, rewrite <- h, exact h4,
  rewrite thm_3_2 ([x ↦ a] v) v s1, exact h2
end
