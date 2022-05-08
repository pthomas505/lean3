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
atom n "P" [x1 ... xn] : A predicate variable named "P" of n terms.
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

func: (n : ℕ, string) → ((fin n → T) → T)
A mapping of each n-ary function symbol f to a function f_{M} : D^{n} → D.

pred: (n : ℕ, string) → ((fin n → T) → Prop)
A mapping of each n-ary predicate symbol P to a predicate P_{M} : D^{n} → Prop.
-/
structure interpretation (T : Type) : Type :=
(domain : set T)
(nonempty : domain.nonempty)
(func (n : ℕ) : string → (fin n → T) → T)
(pred (n : ℕ) : string → (fin n → T) → Prop)


/-
A mapping of each variable name to an element of the domain.
-/
def valuation (T : Type) := string → T

def eval_term (T : Type) (m : interpretation T) (v : valuation T) : term → T
| (var x) := v x
| (func n f terms) := m.func n f (fun i : fin n, eval_term (terms i))


notation  `[` x `↦` a `]` v := function.update v x a

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


lemma finset.mem_bUnion_univ
  {T : Type}
  [decidable_eq T]
  {x : T}
  {n : ℕ}
  {f : fin n → finset T}
  {i : fin n}
  (h : x ∈ f i) :
  x ∈ finset.bUnion finset.univ (fun i : fin n, f i) :=
begin
  simp only [finset.mem_bUnion, finset.mem_univ, exists_true_left],
  exact exists.intro i h
end


theorem thm_3_1
  (T : Type)
  (m : interpretation T)
  (t : term)
  (v v' : valuation T)
  (h1 : ∀ x ∈ t.all_var_set, v x = v' x) :
  eval_term T m v t = eval_term T m v' t :=
begin
  induction t,
  case term.var : x {
    have s1 : x ∈ (var x).all_var_set, unfold term.all_var_set, simp only [finset.mem_singleton],
    calc
    eval_term T m v (var x) = v x : by unfold eval_term
    ... = v' x : h1 x s1
    ... = eval_term T m v' (var x) : by unfold eval_term
  },
  case term.func : n f terms ih {
    calc
    eval_term T m v (func n f terms) = m.func n f (fun i : fin n, eval_term T m v (terms i)) : by unfold eval_term
    ... = m.func n f (fun i : fin n, eval_term T m v' (terms i)) :
      begin
        congr, funext, apply ih,
        intros x h2, apply h1, unfold term.all_var_set,
        exact finset.mem_bUnion_univ h2,
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
  (T : Type)
  (m : interpretation T)
  (p : formula)
  (v v' : valuation T)
  (h1 : ∀ x ∈ p.free_var_set, v x = v' x) :
  holds T m v p ↔ holds T m v' p :=
begin
  induction p generalizing v v',
  case formula.bottom {
    calc
    holds T m v bottom ↔ false : by unfold holds
    ... ↔ holds T m v' bottom : by unfold holds
  },
  case formula.top {
    calc
    holds T m v top ↔ true : by unfold holds
    ... ↔ holds T m v' top : by unfold holds
  },
  case formula.atom : n x terms {
    unfold formula.free_var_set at h1,
    calc
    holds T m v (atom n x terms) ↔ m.pred n x (fun i : fin n, eval_term T m v (terms i)) : by unfold holds
    ... ↔ m.pred n x (fun i : fin n, eval_term T m v' (terms i)) :
      begin
        apply iff_of_eq, congr, funext,
        apply thm_3_1, intros x h, apply h1, exact finset.mem_bUnion_univ h,
      end
    ... ↔ holds T m v' (atom n x terms) : by unfold holds
  },
  case formula.not : p ih {
    unfold formula.free_var_set at h1,
    have s1 : holds T m v p ↔ holds T m v' p, exact ih v v' h1,
    calc
    holds T m v (not p) ↔ ¬ holds T m v p : by unfold holds
    ... ↔ ¬ holds T m v' p : by simp only [s1]
    ... ↔ holds T m v' (not p) : by unfold holds
  },
  case formula.and : p q ih_p ih_q {
    unfold formula.free_var_set at h1, simp only [finset.mem_union, or_imp_distrib, forall_and_distrib] at h1, cases h1,
    have s1 : holds T m v p ↔ holds T m v' p, exact ih_p v v' h1_left,
    have s2 : holds T m v q ↔ holds T m v' q, exact ih_q v v' h1_right,
    calc
    holds T m v (and p q) ↔ (holds T m v p ∧ holds T m v q) : by unfold holds
    ... ↔ (holds T m v' p ∧ holds T m v' q) : by simp only [s1, s2]
    ... ↔ holds T m v' (and p q) : by unfold holds
  },
  case formula.or : p q ih_p ih_q {
    unfold formula.free_var_set at h1, simp only [finset.mem_union, or_imp_distrib, forall_and_distrib] at h1, cases h1,
    have s1 : holds T m v p ↔ holds T m v' p, exact ih_p v v' h1_left,
    have s2 : holds T m v q ↔ holds T m v' q, exact ih_q v v' h1_right,
    calc
    holds T m v (or p q) ↔ (holds T m v p ∨ holds T m v q) : by unfold holds
    ... ↔ (holds T m v' p ∨ holds T m v' q) : by simp only [s1, s2]
    ... ↔ holds T m v' (or p q) : by unfold holds
  },
  case formula.imp : p q ih_p ih_q {
    unfold formula.free_var_set at h1, simp only [finset.mem_union, or_imp_distrib, forall_and_distrib] at h1, cases h1,
    have s1 : holds T m v p ↔ holds T m v' p, exact ih_p v v' h1_left,
    have s2 : holds T m v q ↔ holds T m v' q, exact ih_q v v' h1_right,
    calc
    holds T m v (imp p q) ↔ (holds T m v p → holds T m v q) : by unfold holds
    ... ↔ (holds T m v' p → holds T m v' q) : by simp only [s1, s2]
    ... ↔ holds T m v' (imp p q) : by unfold holds
  },
  case formula.iff : p q ih_p ih_q {
    unfold formula.free_var_set at h1, simp only [finset.mem_union, or_imp_distrib, forall_and_distrib] at h1, cases h1,
    have s1 : holds T m v p ↔ holds T m v' p, exact ih_p v v' h1_left,
    have s2 : holds T m v q ↔ holds T m v' q, exact ih_q v v' h1_right,
    calc
    holds T m v (iff p q) ↔ (holds T m v p ↔ holds T m v q) : by unfold holds
    ... ↔ (holds T m v' p ↔ holds T m v' q) : by simp only [s1, s2]
    ... ↔ holds T m v' (iff p q) : by unfold holds
  },
  case formula.forall_ : x p ih {
    unfold formula.free_var_set at h1, simp only [finset.mem_sdiff, finset.mem_singleton] at h1,
    calc
    holds T m v (forall_ x p) ↔ ∀ a ∈ m.domain, holds T m ([x ↦ a] v) p : by unfold holds
    ... ↔ ∀ a ∈ m.domain, holds T m ([x ↦ a] v') p :
      begin
        apply ball_congr, intros a h2, apply ih, intros y h3,
        by_cases y = x, {
        calc
        ([x ↦ a] v) y = ([x ↦ a] v) x : by rewrite h
        ... = a : dif_pos rfl
        ... = ([x ↦ a] v') x : begin symmetry, exact dif_pos rfl end
        ... = ([x ↦ a] v') y : by rewrite <- h
        },
        {
        calc
        ([x ↦ a] v) y = v y : dif_neg h
        ... = v' y : begin apply h1, exact and.intro h3 h end
        ... = ([x ↦ a] v') y : begin symmetry, exact dif_neg h end
        }
      end
    ... ↔ holds T m v' (forall_ x p) : by unfold holds
  },
  case formula.exists_ : x p ih {
    unfold formula.free_var_set at h1, simp only [finset.mem_sdiff, finset.mem_singleton] at h1,
    calc
    holds T m v (exists_ x p) ↔ ∃ a ∈ m.domain, holds T m ([x ↦ a] v) p : by unfold holds
    ... ↔ ∃ a ∈ m.domain, holds T m ([x ↦ a] v') p :
      begin
        apply bex_congr, intros a h2, apply ih, intros y h3,
        by_cases y = x, {
        calc
        ([x ↦ a] v) y = ([x ↦ a] v) x : by rewrite h
        ... = a : dif_pos rfl
        ... = ([x ↦ a] v') x : begin symmetry, exact dif_pos rfl end
        ... = ([x ↦ a] v') y : by rewrite <- h
        },
        {
        calc
        ([x ↦ a] v) y = v y : dif_neg h
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
  (p : formula)
  (h1 : is_sentence p) :
  ∀ T : Type, ∀ m : interpretation T, forall v : valuation T, forall v' : valuation T,
    holds T m v p ↔ holds T m v' p :=
begin
  intros T m v v',
  unfold is_sentence at h1,
  have s1 : ∀ x ∈ p.free_var_set, v x = v' x,
    rewrite h1, simp only [finset.not_mem_empty, forall_false_left, forall_const],
  exact thm_3_2 T m p v v' s1
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
  unfold is_valid, unfold is_satisfiable, unfold satisfies, unfold holds, push_neg, split,
  intros h2 T m, fconstructor, exact fun s, m.nonempty.some, apply h2,
  intros h2 T m v, cases h2 T m, rewrite <- cor_3_3 p h1 T m w, exact h
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
  intros h1 T m h2,
  unfold holds_in, unfold satisfies, intros v, unfold is_valid at h1, exact h1 T m v,
  unfold is_model_of, unfold satisfies_set,
  intros h1 T m v, unfold holds_in at h1, unfold satisfies at h1, apply h1, intros p h1, simp at h1, contradiction
end


example
	(Γ : set formula) :
	¬ (is_satisfiable_set Γ) ↔ (Γ ⊨ bottom) :=
begin
  unfold is_model_of, unfold holds_in, unfold is_satisfiable_set, unfold satisfies_set,
  split,
  intros h1 T m h2 v, push_neg at h1, cases h1 T m, cases h, exfalso, apply h_right, apply h2, exact h_left,
  unfold satisfies, intros h1 h2, unfold holds at h1, cases h2, cases h2_h,
  apply h1 h2_w h2_h_w h2_h_h, exact fun x, h2_h_w.nonempty.some
end


example
	(T : Type)
	(m : interpretation T)
	(p : formula) :
	(∀ x : string, ∀ v : valuation T, ∀ a ∈ m.domain, holds T m ([x ↦ a] v) p) ↔ (∀ v : valuation T, holds T m v p) :=
begin
  dsimp, split,
  intros h1 v, sorry,
  intros h1 x v a h2, exact h1 (function.update v x a)
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
    (sub_term s (var x)).all_var_set = (s x).all_var_set : by unfold sub_term
    ... = finset.bUnion {x} (fun y : string, (s y).all_var_set) : by simp only [finset.singleton_bUnion]
    ... = finset.bUnion (var x).all_var_set (fun y : string, (s y).all_var_set) : by unfold term.all_var_set
  },
  case term.func : n f terms ih {
    simp at ih,
    have s1 : (sub_term s (func n f terms)).all_var_set =
      (func n f (fun i : fin n, sub_term s (terms i))).all_var_set, unfold sub_term,
    have s2 : (func n f (fun i : fin n, sub_term s (terms i))).all_var_set =
      finset.bUnion finset.univ (fun i : fin n, (sub_term s (terms i)).all_var_set), unfold term.all_var_set,
    have s3 : finset.bUnion finset.univ (fun i : fin n, (sub_term s (terms i)).all_var_set) =
      finset.bUnion finset.univ (fun i : fin n, finset.bUnion (terms i).all_var_set (fun y : string, (s y).all_var_set)), simp only [ih],
    have s4 : finset.bUnion finset.univ (fun i : fin n, finset.bUnion (terms i).all_var_set (fun y : string, (s y).all_var_set)) =
      finset.bUnion (finset.bUnion finset.univ (fun i : fin n, (terms i).all_var_set)) (fun y : string, (s y).all_var_set), sorry,
    have s5 : finset.bUnion (finset.bUnion finset.univ (fun i : fin n, (terms i).all_var_set)) (fun y : string, (s y).all_var_set) = 
      finset.bUnion (func n f terms).all_var_set (fun y : string, (s y).all_var_set), refl,
    sorry
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
    eval_term T m v (sub_term s (var x)) = eval_term T m v (s x) : by unfold sub_term
    ... = ((eval_term T m v) ∘ s) x : by unfold function.comp
    ... = eval_term T m ((eval_term T m v) ∘ s) (var x) : by unfold eval_term
  },
  case term.func : n f terms ih {
    have ih' : ∀ (i : fin n), eval_term T m v (sub_term s (terms i)) =
      eval_term T m ((eval_term T m v) ∘ s) (terms i), exact ih,
    calc
    eval_term T m v (sub_term s (func n f terms)) = eval_term T m v (func n f (fun i, sub_term s (terms i))) : by unfold sub_term
    ... = m.func n f (fun i, eval_term T m v (sub_term s (terms i))) : by unfold eval_term
    ... = m.func n f (fun i, eval_term T m ((eval_term T m v) ∘ s) (terms i)) : begin congr, apply funext, intros j, exact ih' j end
    ... = eval_term T m ((eval_term T m v) ∘ s) (func n f terms) : by unfold eval_term
  }
end


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


example (α : Type) (β : Type) [decidable_eq α] [decidable_eq β] (s : finset α) (t : α → finset β) (x : α) :
(finset.bUnion s (fun y : α, t y)) \ (t x) = (finset.bUnion (s \ {x}) (fun y : α, t y)) \ (t x) := sorry


lemma lem_3_6_1
  (x : string)
  (p : formula)
  (s : instantiation)
  (h1 : ∀ (s : instantiation), (sub_formula s p).free_var_set =
    p.free_var_set.bUnion (fun y : string, (s y).all_var_set)) :
  let x' :=
      if ∃ y ∈ p.free_var_set \ {x}, x ∈ (s y).all_var_set
      then variant x (sub_formula ([x ↦ var x] s) p).free_var_set
      else x
  in
  x' ∉ (p.free_var_set \ {x}).bUnion (λ (y : string), (s y).all_var_set) :=
begin
  intro x',
  by_cases x ∈ (finset.bUnion (p.free_var_set \ {x}) (fun (y : string), (s y).all_var_set)), {
    simp only [finset.mem_bUnion] at h,
    have s1 : x' = variant x (sub_formula ([x ↦ var x] s) p).free_var_set, exact if_pos h,
    have s2 : x' ∉ (sub_formula ([x ↦ var x] s) p).free_var_set, rewrite s1, apply variant_not_mem,
    have s3 : finset.bUnion (p.free_var_set \ {x}) (fun (y : string), (s y).all_var_set) ⊆
      (sub_formula ([x ↦ var x] s) p).free_var_set,
      calc
      finset.bUnion (p.free_var_set \ {x}) (fun (y : string), (s y).all_var_set) =
        finset.bUnion (p.free_var_set \ {x}) (fun y : string, (([x ↦ var x] s) y).all_var_set) :
          begin symmetry, apply finset.bUnion_congr, refl, intros a h1, congr,
            simp only [finset.mem_sdiff, finset.mem_singleton] at h1, cases h1,
            exact function.update_noteq h1_right (var x) s end
      ... ⊆ finset.bUnion p.free_var_set (fun y : string, (([x ↦ var x] s) y).all_var_set) : 
          begin apply finset.bUnion_subset_bUnion_of_subset_left, apply finset.sdiff_subset end
      ... = (sub_formula ([x ↦ var x] s) p).free_var_set :
          begin symmetry, exact h1 (function.update s x (var x)) end,
    exact finset.not_mem_mono s3 s2,
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
    ... = finset.bUnion (finset.bUnion finset.univ (fun i : fin n, (terms i).all_var_set)) (fun y : string, (s y).all_var_set) : sorry
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
    ... = finset.bUnion (p.free_var_set ∪ q.free_var_set) (fun y : string, (s y).all_var_set) : sorry
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
    let x' :=
      if ∃ y ∈ p.free_var_set \ {x}, x ∈ (s y).all_var_set
      then variant x (sub_formula ([x ↦ var x] s) p).free_var_set
      else x,
    have s1 : x' ∉ (finset.bUnion (p.free_var_set \ {x}) (fun (y : string), (s y).all_var_set)),
      exact lem_3_6_1 x p s ih,
    calc
    (sub_formula s (forall_ x p)).free_var_set =
          (forall_ x' (sub_formula ([x ↦ var x'] s) p)).free_var_set :
            by unfold sub_formula
    ... = (sub_formula ([x ↦ var x'] s) p).free_var_set \ {x'} :
            by unfold formula.free_var_set
    ... = (finset.bUnion p.free_var_set (fun (y : string), (([x ↦ var x'] s) y).all_var_set)) \ {x'} :
            by simp only [ih ([x ↦ var x'] s)]
    ... = (finset.bUnion (p.free_var_set \ {x}) (fun (y : string), (([x ↦ var x'] s) y).all_var_set)) \ {x'} :
            sorry
    ... = (finset.bUnion (p.free_var_set \ {x}) (fun (y : string), (s y).all_var_set)) \ {x'} :
            begin congr' 1, apply finset.bUnion_congr, refl, intros a h1, congr, apply function.update_noteq,
            simp only [finset.mem_sdiff, finset.mem_singleton] at h1, cases h1, exact h1_right end
    ... = finset.bUnion (p.free_var_set \ {x}) (fun (y : string), (s y).all_var_set) :
            begin apply finset.sdiff_singleton_not_mem_eq_self, exact s1 end
  },
  case formula.exists_ : x p ih {
    sorry
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
    sorry
  },
  case formula.imp : p q ih_p ih_q {
    sorry
  },
  case formula.iff : p q ih_p ih_q {
    sorry
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
        ... = eval_term T m v (s z) : begin apply thm_3_1 T m (s z) ([x' ↦ a] v) v, intros x h3,
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
      intros h10 a h11, rewrite <- (thm_3_2 T m p ((eval_term T m ([x' ↦ a] v)) ∘ ([x ↦ (var x')] s)) ([x ↦ a] ((eval_term T m v) ∘ s)) (s1 a h11)), exact h10 a h11,
      intros h10 a h11, rewrite (thm_3_2 T m p ((eval_term T m ([x' ↦ a] v)) ∘ ([x ↦ (var x')] s)) ([x ↦ a] ((eval_term T m v) ∘ s)) (s1 a h11)), exact h10 a h11
      end
    ... ↔ holds T m (eval_term T m v ∘ s) (forall_ x p) : by unfold holds
  },
  case formula.exists_ : x p ih {
    sorry
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
