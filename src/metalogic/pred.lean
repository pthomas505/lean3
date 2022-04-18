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


meta def fin_fun_to_string {α : Type} [has_to_string α] {n : ℕ} (as : fin n → α) : string :=
list.to_string (list.of_fn as)


/-
Term schemes.
var "x" : An object variable named "x". Ranges over the domain of each interpretation.
func "c" [] : A constant named "c".
func "f" [x1 .. xn] : A function named "f" of n terms.
-/
inductive term : Type
| var : string → term
| func (n : ℕ) : string → (fin n → term) → term

open term

meta def term.repr : term → string
| (var x) := x.quote
| (func n f args) := f.quote ++ fin_fun_to_string (fun i : fin n, (args i).repr)

meta instance : has_repr term := has_repr.mk term.repr

def mk_func (name : string) (terms : list term)
:= func terms.length name terms.to_fin_fun


/-
Formula schemes.
atom "P" [] : A propositional variable named "P".
atom "P" [x1 .. xn] : A predicate variable named "P" of n terms.
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
| bottom := sformat!"F"
| top := sformat!"T"
| (atom n x terms) := x.quote ++ fin_fun_to_string (fun i : fin n, (terms i).repr)
| (not p) := sformat!"(¬ {p.repr})"
| (and p q) := sformat!"({p.repr} ∧ {q.repr})"
| (or p q) := sformat!"({p.repr} ∨ {q.repr})"
| (imp p q) := sformat!"({p.repr} → {q.repr})"
| (iff p q) := sformat!"({p.repr} ↔ {q.repr})"
| (forall_ x p) := sformat!"(∀ {x.quote}. {p.repr})"
| (exists_ x p) := sformat!"(∃ {x.quote}. {p.repr})"

meta instance : has_repr formula := has_repr.mk formula.repr

def mk_atom (name : string) (terms : list term) :=
atom terms.length name terms.to_fin_fun


/-
domain: A nonempty set D called the domain of the interpretation. The intention is that all terms have values in D.

func: (n : nat, string) → ((fin n → T) → T)
A mapping of each n-ary function symbol f to a function f_{M} : D^{n} → D.

pred: (n : nat, string) → ((fin n → T) → bool)
A mapping of each n-ary predicate symbol P to a Boolean function P_{M} : D^{n} → {false, true}.
-/
structure interpretation (T : Type) : Type :=
(domain : set T)
(nonempty : domain.nonempty)
(func (n : ℕ) : string → (fin n → T) → T)
(pred (n : ℕ) : string → (fin n → T) → bool)

/-
A mapping of each variable name to an element of the domain.
-/
def valuation (T : Type) := string → T

def term.eval
(T : Type) (m : interpretation T) (v : valuation T) : term → T
| (var x) := v x
| (func n f args) := m.func n f (fun i : fin n, term.eval (args i))

notation  x `↦` a := fun v, function.update v x a

def holds (T : Type) (m : interpretation T) : valuation T → formula → Prop
| _ bottom := false
| _ top := true
| v (atom n x args) := m.pred n x (fun i : fin n, term.eval T m v (args i))
| v (not p) := ¬ holds v p
| v (and p q) := holds v p ∧ holds v q
| v (or p q) := holds v p ∨ holds v q
| v (imp p q) := holds v p → holds v q
| v (iff p q) := holds v p ↔ holds v q
| v (forall_ x p) := forall a ∈ m.domain, holds ((x ↦ a) v) p
| v (exists_ x p) := exists a ∈ m.domain, holds ((x ↦ a) v) p

def term.all_var_set : term → finset string
| (var x) := {x}
| (func n f args) := finset.bUnion finset.univ (fun i : fin n, (args i).all_var_set)

theorem thm_3_1
  (T : Type)
  (m : interpretation T)
  (t : term)
  (v v' : valuation T)
  (h1 : ∀ x ∈ (term.all_var_set t), v x = v' x) :
  term.eval T m v t = term.eval T m v' t :=
begin
  induction t,
  case term.var : x {
    have s1 : x ∈ (var x).all_var_set, unfold term.all_var_set, simp only [finset.mem_singleton],
    calc
    term.eval T m v (var x) = v x : by unfold term.eval
    ... = v' x : h1 x s1
    ... = term.eval T m v' (var x) : by unfold term.eval
  },
  case term.func : n f args ih {
    calc
    term.eval T m v (func n f args)
      = m.func n f (fun i : fin n, term.eval T m v (args i)) : by unfold term.eval
    ... = 
      m.func n f (fun i : fin n, term.eval T m v' (args i)) :
        begin
          congr, funext, apply ih,
          intros x h2, apply h1, unfold term.all_var_set,
          simp only [finset.mem_bUnion, finset.mem_univ, exists_true_left],
          exact exists.intro i h2
        end
    ... =
      term.eval T m v' (func n f args) : by unfold term.eval
	}
end

#eval (forall_ "x" (mk_atom "P" [mk_func "f" [(var "x")], var "y"]))

def formula.all_var_set : formula → finset string
| bottom := ∅
| top := ∅
| (atom n x terms) := finset.bUnion finset.univ (fun i : fin n, (terms i).all_var_set)
| (not p) := p.all_var_set
| (and p q) := p.all_var_set ∪ q.all_var_set
| (or p q) := p.all_var_set ∪ q.all_var_set
| (imp p q) := p.all_var_set ∪ q.all_var_set
| (iff p q) := p.all_var_set ∪ q.all_var_set
| (forall_ x p) := {x} ∪ p.all_var_set
| (exists_ x p) := {x} ∪ p.all_var_set

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
  (h1 : ∀ x ∈ (formula.free_var_set p), v x = v' x) :
  holds T m v p ↔ holds T m v' p :=
begin
  induction p generalizing v v',
  case formula.bottom {
    unfold holds
  },
  case formula.top {
    unfold holds
  },
  case formula.atom : n f terms {
    unfold formula.free_var_set at h1,
    have s1 : forall i, term.eval T m v (terms i) = term.eval T m v' (terms i),
      intros i, apply thm_3_1, intros x h, apply h1, simp only [finset.mem_bUnion, finset.mem_univ, exists_true_left],
      exact exists.intro i h,
    unfold holds, finish
  },
  case formula.not : p ih {
    have s1 : holds T m v p ↔ holds T m v' p, apply ih, unfold formula.free_var_set at h1,
      exact h1,
    unfold holds, rewrite s1
  },
  case formula.and : p q ih_p ih_q {
    have s1 : holds T m v p ↔ holds T m v' p, apply ih_p, intros x h, apply h1,
      unfold formula.free_var_set, finish,
    have s2 : holds T m v q ↔ holds T m v' q, apply ih_q, intros x h, apply h1,
      unfold formula.free_var_set, finish,
    unfold holds, rewrite s1, rewrite s2
  },
  case formula.or : p q ih_p ih_q {
    have s1 : holds T m v p ↔ holds T m v' p, apply ih_p, intros x h, apply h1,
      unfold formula.free_var_set, finish,
    have s2 : holds T m v q ↔ holds T m v' q, apply ih_q, intros x h, apply h1,
      unfold formula.free_var_set, finish,
    unfold holds, rewrite s1, rewrite s2
  },
  case formula.imp : p q ih_p ih_q {
    have s1 : holds T m v p ↔ holds T m v' p, apply ih_p, intros x h, apply h1,
      unfold formula.free_var_set, finish,
    have s2 : holds T m v q ↔ holds T m v' q, apply ih_q, intros x h, apply h1,
      unfold formula.free_var_set, finish,
    unfold holds, rewrite s1, rewrite s2
  },
  case formula.iff : p q ih_p ih_q {
    have s1 : holds T m v p ↔ holds T m v' p, apply ih_p, intros x h, apply h1,
      unfold formula.free_var_set, finish,
    have s2 : holds T m v q ↔ holds T m v' q, apply ih_q, intros x h, apply h1,
      unfold formula.free_var_set, finish,
    unfold holds, rewrite s1, rewrite s2
  },
  case formula.forall_ : x p ih {
    unfold formula.free_var_set at h1,
    unfold holds,
    have s1 : ∀ (a : T), a ∈ m.domain →
      (holds T m ((x ↦ a) v) p ↔ holds T m ((x ↦ a) v') p),
        intros a h, apply ih, intros y h',
        unfold function.update, simp, split_ifs, refl,
        apply h1, simp only [finset.mem_sdiff, finset.mem_singleton], exact and.intro h' h_1,
    exact ball_congr s1
  },
  case formula.exists_ : x p ih {
    unfold formula.free_var_set at h1,
    unfold holds,
    have s1 : ∀ (a : T), a ∈ m.domain →
      (holds T m ((x ↦ a) v) p ↔ holds T m ((x ↦ a) v') p),
        intros a h, apply ih, intros y h',
        unfold function.update, simp, split_ifs, refl,
        apply h1, simp only [finset.mem_sdiff, finset.mem_singleton], exact and.intro h' h_1,
    exact bex_congr s1
  }
end

def is_sentence (p : formula) : Prop := p.free_var_set = ∅

theorem cor_3_3
  (p : formula)
  (h1 : is_sentence p) :
  ∀ T : Type, ∀ m : interpretation T, forall v : valuation T, forall v' : valuation T,
    holds T m v p ↔ holds T m v' p :=
begin
  intros T m v v',
  unfold is_sentence at h1,
  have s1 : ∀ x ∈ (formula.free_var_set p), v x = v' x,
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


def is_satisfiable (p : formula) : Prop := ∃ T : Type, ∃ m : interpretation T, satisfies T m p

def is_satisfiable_set (S : set formula) : Prop := ∃ T : Type, ∃ m : interpretation T, ∀ p ∈ S, satisfies T m p


/-
holds_in p T m = p holds in m.
-/
def holds_in (p : formula) (T : Type) (m : interpretation T) : Prop := satisfies T m p

/-
set_holds_in S T m = S holds in m.
-/
def set_holds_in (S : set formula) (T : Type) (m : interpretation T) : Prop := satisfies_set T m S


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
def is_model_of (T : Type) (m : interpretation T) (Γ : set formula) := satisfies_set T m Γ


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
	(∀ x : string, ∀ v : valuation T, ∀ a ∈ m.domain, holds T m ((x ↦ a) v) p) ↔ (∀ v : valuation T, holds T m v p) :=
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

def term_sub (i : instantiation) : term → term
| (var x) := i x
| (func n name args) := func n name (fun n, term_sub (args n))


lemma lem_3_4
  (t : term)
  (i : instantiation) :
  term.all_var_set (term_sub i t) = finset.bUnion (term.all_var_set t) (fun y, term.all_var_set (i y)) :=
begin
  induction t,
  case term.var : x {
    unfold term_sub, unfold term.all_var_set, simp only [finset.singleton_bUnion],
  },
  case term.func : n f args ih {
    sorry
  }
end


lemma lem_3_5
  (T : Type)
  (t : term)
  (i : instantiation)
  (m : interpretation T)
  (v : valuation T) :
  term.eval T m v (term_sub i t) = term.eval T m ((term.eval T m v) ∘ i) t :=
begin
  induction t,
  case term.var : x {
    calc
    term.eval T m v (term_sub i (var x)) = term.eval T m v (i x) : by unfold term_sub
    ...                                  = ((term.eval T m v) ∘ i) x : by unfold function.comp
    ...                                  = term.eval T m ((term.eval T m v) ∘ i) (var x) : by unfold term.eval
  },
  case term.func : n f args ih {
    have ih' : ∀ (j : fin n), term.eval T m v (term_sub i (args j)) =
      term.eval T m ((term.eval T m v) ∘ i) (args j), exact ih,
    calc
    term.eval T m v (term_sub i (func n f args)) = term.eval T m v (func n f (fun j, term_sub i (args j))) : by unfold term_sub
    ... = m.func n f (fun j, term.eval T m v (term_sub i (args j))) : by unfold term.eval
    ... = m.func n f (fun j, term.eval T m ((term.eval T m v) ∘ i) (args j)) : begin congr, apply funext, intros j, exact ih' j end
    ... = term.eval T m ((term.eval T m v) ∘ i) (func n f args) : by unfold term.eval
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


def formula_sub : instantiation → formula → formula
| _ bottom := bottom
| _ top := top
| i (atom n x terms) := atom n x (fun n, term_sub i (terms n))
| i (not p) := not (formula_sub i p)
| i (and p q) := and (formula_sub i p) (formula_sub i q)
| i (or p q) := or (formula_sub i p) (formula_sub i q)
| i (imp p q) := imp (formula_sub i p) (formula_sub i q)
| i (iff p q) := iff (formula_sub i p) (formula_sub i q)
| i (forall_ x p) :=
  let x' :=
    if ∃ y ∈ formula.free_var_set p \ {x}, x ∈ term.all_var_set (i y)
    then (variant x (formula.free_var_set (formula_sub ((x ↦ var x) i) p)))
    else x
  in forall_ x' (formula_sub ((x ↦ var x') i) p)

| i (exists_ x p) := sorry


lemma lem_3_6
  (p : formula)
  (i : instantiation) :
  formula.free_var_set (formula_sub i p) = finset.bUnion (formula.free_var_set p) (fun y, term.all_var_set (i y)) :=
begin
  sorry
end

theorem thm_3_7
  (p : formula)
  (i : instantiation)
  (T : Type)
  (m : interpretation T)
  (v : valuation T) :
  holds T m v (formula_sub i p) = holds T m ((term.eval T m v) ∘ i) p :=
begin
  sorry
end

theorem cor_3_8
  (p : formula)
  (i : instantiation)
  (h1 : is_valid p) :
  is_valid (formula_sub i p) :=
begin
  sorry
end
