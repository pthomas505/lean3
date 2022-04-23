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
func 0 "c" [] : A constant named "c".
func n "f" [x1 .. xn] : A function named "f" of n arguments.
-/
inductive term : Type
| var : string → term
| func (n : ℕ) : string → (fin n → term) → term

open term

meta def term.repr : term → string
| (var x) := x.quote
| (func n f args) := f.quote ++ fin_fun_to_string (fun i : fin n, (args i).repr)

meta instance : has_repr term := has_repr.mk term.repr

def mk_const (name : string) :=
func 0 name list.nil.to_fin_fun

def mk_func (name : string) (terms : list term) :=
func terms.length name terms.to_fin_fun


/-
Formula schemes.
atom 0 "P" [] : A propositional variable named "P".
atom n "P" [x1 .. xn] : A predicate variable named "P" of n terms.
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
| bottom := sformat!"⊥"
| top := sformat!"⊤"
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


#eval (forall_ "x" (mk_pred "P" [mk_func "f" [(var "x")], var "y"]))


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

def eval_term (T : Type) (m : interpretation T) (v : valuation T) : term → T
| (var x) := v x
| (func n f args) := m.func n f (fun i : fin n, eval_term (args i))


notation  x `↦` a := fun v, function.update v x a

def holds (T : Type) (m : interpretation T) : valuation T → formula → Prop
| _ bottom := false
| _ top := true
| v (atom n x terms) := m.pred n x (fun i : fin n, eval_term T m v (terms i))
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
  case term.func : n f args ih {
    calc
    eval_term T m v (func n f args) = m.func n f (fun i : fin n, eval_term T m v (args i)) : by unfold eval_term
    ... = m.func n f (fun i : fin n, eval_term T m v' (args i)) :
      begin
        congr, funext, apply ih,
        intros x h2, apply h1, unfold term.all_var_set,
        simp only [finset.mem_bUnion, finset.mem_univ, exists_true_left],
        exact exists.intro i h2
      end
    ... = eval_term T m v' (func n f args) : by unfold eval_term
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
    unfold holds
  },
  case formula.top {
    unfold holds
  },
  case formula.atom : n x terms {
    unfold formula.free_var_set at h1,
    have s1 : forall i : fin n, eval_term T m v (terms i) = eval_term T m v' (terms i),
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
      unfold formula.free_var_set, simp only [finset.mem_union], apply or.intro_left, exact h,
    have s2 : holds T m v q ↔ holds T m v' q, apply ih_q, intros x h, apply h1,
      unfold formula.free_var_set, simp only [finset.mem_union], apply or.intro_right, exact h,
    unfold holds, rewrite s1, rewrite s2
  },
  case formula.or : p q ih_p ih_q {
    have s1 : holds T m v p ↔ holds T m v' p, apply ih_p, intros x h, apply h1,
      unfold formula.free_var_set, simp only [finset.mem_union], apply or.intro_left, exact h,
    have s2 : holds T m v q ↔ holds T m v' q, apply ih_q, intros x h, apply h1,
      unfold formula.free_var_set, simp only [finset.mem_union], apply or.intro_right, exact h,
    unfold holds, rewrite s1, rewrite s2
  },
  case formula.imp : p q ih_p ih_q {
    have s1 : holds T m v p ↔ holds T m v' p, apply ih_p, intros x h, apply h1,
      unfold formula.free_var_set, simp only [finset.mem_union], apply or.intro_left, exact h,
    have s2 : holds T m v q ↔ holds T m v' q, apply ih_q, intros x h, apply h1,
      unfold formula.free_var_set, simp only [finset.mem_union], apply or.intro_right, exact h,
    unfold holds, rewrite s1, rewrite s2
  },
  case formula.iff : p q ih_p ih_q {
    have s1 : holds T m v p ↔ holds T m v' p, apply ih_p, intros x h, apply h1,
      unfold formula.free_var_set, simp only [finset.mem_union], apply or.intro_left, exact h,
    have s2 : holds T m v q ↔ holds T m v' q, apply ih_q, intros x h, apply h1,
      unfold formula.free_var_set, simp only [finset.mem_union], apply or.intro_right, exact h,
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

def sub_term (s : instantiation) : term → term
| (var x) := s x
| (func n name args) := func n name (fun i : fin n, sub_term (args i))


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
  case term.func : n f args ih {
    simp at ih,
    have s1 : (sub_term s (func n f args)).all_var_set =
      (func n f (fun i : fin n, sub_term s (args i))).all_var_set, unfold sub_term,
    have s2 : (func n f (fun i : fin n, sub_term s (args i))).all_var_set =
      finset.bUnion finset.univ (fun i : fin n, (sub_term s (args i)).all_var_set), unfold term.all_var_set,
    have s3 : finset.bUnion finset.univ (fun i : fin n, (sub_term s (args i)).all_var_set) =
      finset.bUnion finset.univ (fun i : fin n, finset.bUnion (args i).all_var_set (fun y : string, (s y).all_var_set)), simp only [ih],
    have s4 : finset.bUnion finset.univ (fun i : fin n, finset.bUnion (args i).all_var_set (fun y : string, (s y).all_var_set)) =
      finset.bUnion (finset.bUnion finset.univ (fun i : fin n, (args i).all_var_set)) (fun y : string, (s y).all_var_set), sorry,
    have s5 : finset.bUnion (finset.bUnion finset.univ (fun i : fin n, (args i).all_var_set)) (fun y : string, (s y).all_var_set) = 
      finset.bUnion (func n f args).all_var_set (fun y : string, (s y).all_var_set), refl,
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
  case term.func : n f args ih {
    have ih' : ∀ (i : fin n), eval_term T m v (sub_term s (args i)) =
      eval_term T m ((eval_term T m v) ∘ s) (args i), exact ih,
    calc
    eval_term T m v (sub_term s (func n f args)) = eval_term T m v (func n f (fun i, sub_term s (args i))) : by unfold sub_term
    ... = m.func n f (fun i, eval_term T m v (sub_term s (args i))) : by unfold eval_term
    ... = m.func n f (fun i, eval_term T m ((eval_term T m v) ∘ s) (args i)) : begin congr, apply funext, intros j, exact ih' j end
    ... = eval_term T m ((eval_term T m v) ∘ s) (func n f args) : by unfold eval_term
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
    if ∃ y ∈ formula.free_var_set p \ {x}, x ∈ term.all_var_set (s y)
    then (variant x (formula.free_var_set (sub_formula ((x ↦ var x) s) p)))
    else x
  in forall_ x' (sub_formula ((x ↦ var x') s) p)
| s (exists_ x p) :=
  let x' :=
    if ∃ y ∈ formula.free_var_set p \ {x}, x ∈ term.all_var_set (s y)
    then (variant x (formula.free_var_set (sub_formula ((x ↦ var x) s) p)))
    else x
  in exists_ x' (sub_formula ((x ↦ var x') s) p)


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
      if ∃ y ∈ formula.free_var_set p \ {x}, x ∈ term.all_var_set (s y)
      then (variant x (formula.free_var_set (sub_formula ((x ↦ var x) s) p)))
      else x,
    have s1 : (sub_formula s (forall_ x p)).free_var_set =
      (forall_ x' (sub_formula ((x ↦ var x') s) p)).free_var_set, unfold sub_formula,
    have s2 : (forall_ x' (sub_formula ((x ↦ var x') s) p)).free_var_set =
      (sub_formula ((x ↦ var x') s) p).free_var_set \ {x'}, unfold formula.free_var_set,
    have s3 : (sub_formula ((x ↦ var x') s) p).free_var_set \ {x'} =
      (finset.bUnion p.free_var_set (fun (y : string), (((x ↦ var x') s) y).all_var_set)) \ {x'}, simp only [ih ((x ↦ var x') s)],
    have s4 : (((x ↦ var x') s) x).all_var_set =
      {x'}, unfold function.update, simp only [eq_self_iff_true, dite_eq_ite, if_true], unfold term.all_var_set,
    sorry
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
  holds T m v (sub_formula s p) = holds T m ((eval_term T m v) ∘ s) p :=
begin
  sorry
end

theorem cor_3_8
  (p : formula)
  (s : instantiation)
  (h1 : is_valid p) :
  is_valid (sub_formula s p) :=
begin
  sorry
end
