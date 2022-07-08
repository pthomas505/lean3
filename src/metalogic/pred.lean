/-
References:

https://www.cambridge.org/core/books/handbook-of-practical-logic-and-automated-reasoning/EB6396296813CB562987E8C37AC4520D
https://www.cl.cam.ac.uk/~jrh13/atp/index.html
Harrison, J. (2009).
Handbook of Practical Logic and Automated Reasoning.
Cambridge: Cambridge University Press.
doi:10.1017/CBO9780511576430
-/


import data.finset

set_option pp.parens true


lemma finset.mem_ite
  {α : Type}
  (x : α)
  (a : Prop)
  [decidable a]
  (s t : finset α) :
  x ∈ (if a then s else t) ↔ (a → x ∈ s) ∧ (¬ a → x ∈ t) :=
begin
  split,
  {
    intro h1,
    split,
      { intro h2, simp only [if_pos h2] at h1, exact h1 },
      { intro h2, simp only [if_neg h2] at h1, exact h1 }
  },
  {
    intro h1, cases h1,
    split_ifs,
      { exact h1_left h },
      { exact h1_right h }
  }
end

lemma finset.bUnion_sdiff
  {α β : Type}
  [decidable_eq β]
  (s : finset α)
  (f : α → finset β)
  (t : finset β) :
  (s.bUnion f) \ t = s.bUnion (fun (x : α), f x \ t) :=
begin
  apply finset.ext, intro a,
  simp only [finset.mem_sdiff, finset.mem_bUnion, exists_prop],
  split,
  {
    intro h1, cases h1, apply exists.elim h1_left,
    intros b h2, cases h2, apply exists.intro b,
    split,
      { exact h2_left },
      { exact and.intro h2_right h1_right }
  },
  {
    intro h1, apply exists.elim h1,
    intros b h2, cases h2, cases h2_right,
    split,
      { apply exists.intro b, exact and.intro h2_left h2_right_left },
      { exact h2_right_right }
  }
end

lemma finset.bUnion_filter
  {α β : Type}
  [decidable_eq β]
  (s : finset α)
  (f : α → finset β)
  (p : α → Prop)
  [decidable_pred p] :
  (s.filter p).bUnion f =
    s.bUnion (fun (x : α), if p x then f x else ∅) :=
begin
  apply finset.ext, intro a,
  simp only [finset.mem_ite, imp_iff_not_or, or_and_distrib_right,
    finset.mem_bUnion, finset.mem_filter, exists_prop,
    finset.not_mem_empty, not_not, or_false, not_and_self, false_or],
  split,
  {
    intro h1, apply exists.elim h1, intros b h2, cases h2, cases h2_left,
    apply exists.intro b,
    split,
      { exact h2_left_left },
      { exact and.intro h2_right h2_left_right }
  },
  {
    intro h1, apply exists.elim h1, intros b h2, cases h2, cases h2_right,
    apply exists.intro b,
    split,
      { exact and.intro h2_left h2_right_right },
      { exact h2_right_left }
  }
end

lemma finset.sdiff_singleton_bUnion
  {α β : Type}
  [decidable_eq α] [decidable_eq β]
  (s : finset α)
  (f : α → finset β)
  (x : α)
  (t : finset β)
  (h1 : f x = t) :
  ((s \ {x}).bUnion f) \ t = (s.bUnion f) \ t :=
begin
  rewrite <- h1,
  simp only [finset.bUnion_sdiff, finset.sdiff_eq_filter s,
    finset.bUnion_filter],
  congr, apply funext, intro y, apply finset.ext, intro a,
  simp only [finset.mem_singleton, ite_not, finset.mem_sdiff,
    and.congr_left_iff],
  intro h2,
  split,
  {
    split_ifs,
      { intro h3, simp only [finset.not_mem_empty] at h3, contradiction },
      { intro h3, exact h3 }
  },
  {
    intro h3,
    split_ifs,
      { simp only [finset.not_mem_empty], apply h2, rewrite <- h, exact h3 },
      { exact h3 }
  }
end

lemma finset.bUnion_union
  {α β : Type}
  [decidable_eq α] [decidable_eq β]
  (s t : finset α)
  (f : α → finset β) :
  (s ∪ t).bUnion f = s.bUnion f ∪ t.bUnion f :=
begin
  apply finset.ext, intro a,
  simp only [or_and_distrib_right, exists_or_distrib, finset.mem_bUnion,
    finset.mem_union, exists_prop]
end

lemma finset.bUnion_sdiff_of_forall_disjoint
  {α β : Type}
  [decidable_eq β]
  (s : finset α)
  (f : α → finset β)
  (t : finset β)
  (h1 : ∀ (y : α), y ∈ s → disjoint (f y) t) :
  (s.bUnion f) \ t = s.bUnion f :=
begin
  simp only [finset.sdiff_eq_self_iff_disjoint, finset.disjoint_bUnion_left],
  intro i, exact h1 i
end

lemma finset.ne_imp_sdiff_union_comm
  {α : Type}
  [decidable_eq α]
  (x y : α)
  (s : finset α)
  (h1 : x ≠ y) :
  (s \ {x}) ∪ {y} = (s ∪ {y}) \ {x} :=
begin
  apply finset.ext, intros a,
  simp only [finset.mem_union, finset.mem_sdiff, finset.mem_singleton],
  split,
  {
    intros h2,
    split,
    {
      cases h2,
      { cases h2, apply or.intro_left, exact h2_left },
      { apply or.intro_right, exact h2 }
    },
    {
      cases h2,
      { cases h2, exact h2_right },
      { rewrite h2, rewrite ne_comm at h1, exact h1 }
    }
  },
  {
    intros h2, cases h2,
    cases h2_left,
    { apply or.intro_left, exact and.intro h2_left h2_right },
    { apply or.intro_right, exact h2_left }
  }
end


lemma finset.mem_ne_imp_mem_sdiff
  {α : Type}
  [decidable_eq α]
  (x y : α)
  (s : finset α)
  (h1 : x ∈ s)
  (h2 : x ≠ y) :
  x ∈ s \ {y} :=
begin
  simp only [finset.mem_sdiff, finset.mem_singleton],
  exact and.intro h1 h2
end

lemma finset.mem_sdiff_imp_mem
  {α : Type}
  [decidable_eq α]
  (x y : α)
  (s : finset α)
  (h1 : x ∈ s \ {y}) :
  x ∈ s :=
begin
  simp only [finset.mem_sdiff, finset.mem_singleton] at h1,
  cases h1,
  exact h1_left
end

lemma finset.mem_sdiff_imp_ne
  {α : Type}
  [decidable_eq α]
  (x y : α)
  (s : finset α)
  (h1 : x ∈ s \ {y}) :
  x ≠ y :=
begin
  simp only [finset.mem_sdiff, finset.mem_singleton] at h1,
  cases h1,
  exact h1_right
end

lemma finset.eq_imp_not_mem_sdiff
  {α : Type}
  [decidable_eq α]
  (x y : α)
  (s : finset α)
  (h1 : x = y) :
  x ∉ s \ {y} :=
begin
  simp only [finset.mem_sdiff, finset.mem_singleton],
  push_neg,
  intro, exact h1
end

lemma finset.not_mem_imp_not_mem_sdiff
  {α : Type}
  [decidable_eq α]
  (x y : α)
  (s : finset α)
  (h1 : x ∉ s) :
  x ∉ s \ {y} :=
begin
  simp only [finset.mem_sdiff, finset.mem_singleton],
  push_neg,
  intro h2, by_contradiction, apply h1, exact h2
end

lemma finset.not_mem_sdiff_mem_imp_eq
  {α : Type}
  [decidable_eq α]
  (x y : α)
  (s : finset α)
  (h1 : x ∉ s \ {y})
  (h2 : x ∈ s) :
  x = y :=
begin
  simp only [finset.mem_sdiff, finset.mem_singleton] at h1,
  push_neg at h1,
  exact h1 h2
end

lemma finset.not_mem_sdiff_ne_imp_not_mem
  {α : Type}
  [decidable_eq α]
  (x y : α)
  (s : finset α)
  (h1 : x ∉ s \ {y})
  (h2 : x ≠ y) :
  x ∉ s :=
begin
  simp only [finset.mem_sdiff, finset.mem_singleton] at h1,
  push_neg at h1,
  intro h3, apply h2, exact h1 h3
end


def list.to_fin_fun {α : Type} (s : list α) : fin s.length → α :=
fun (i : fin s.length), s.nth_le i.val i.property


def fin_fun_to_string {α : Type} [has_to_string α]
  (n : ℕ) (f : fin n → α) : string :=
(list.of_fn f).to_string


abbreviation var_symbols := ℕ
abbreviation func_symbols := string
abbreviation pred_symbols := string


/-
var "x" : A variable named "x". Ranges over the domain of each
interpretation.
func 0 "c" [] : A constant named "c".
func n "f" [x1 ... xn] : A function named "f" of n terms (arguments).
-/
inductive term : Type
| var : var_symbols → term
| func (n : ℕ) : func_symbols → (fin n → term) → term

open term

def term.repr : term → string
| (var x) := x.repr
| (func n f t) :=
    f ++ fin_fun_to_string n (fun (i : fin n), (t i).repr)

instance term.has_repr : has_repr term := has_repr.mk term.repr

instance term.inhabited : inhabited term :=
inhabited.mk (var (default : var_symbols))

def pi_decide
  {a b : Prop}
  [decidable a]
  (h : a → decidable b) :
  decidable (a ∧ b) :=
if hp : a then
  by haveI := h hp; exact
  if hq : b then is_true (and.intro hp hq)
  else is_false (assume h : a ∧ b, hq (and.right h))
else is_false (assume h : a ∧ b, hp (and.left h))

instance term.decidable_eq : decidable_eq term
| (var x) (var x') :=
    decidable_of_decidable_of_iff
      (by apply_instance : decidable (x = x')) (by simp only)
| (var x) (func n f t) := is_false (by simp only [not_false_iff])
| (func n f t) (var x) := is_false (by simp only [not_false_iff])
| (func n f t) (func n' f' t') := decidable_of_decidable_of_iff
  (begin
    apply' pi_decide,
    intro h,
    apply' and.decidable,
    rewrite fin.heq_fun_iff h,
    apply' fintype.decidable_forall_fintype,
    intro a,
    apply term.decidable_eq,
  end : decidable (n = n' ∧ f = f' ∧ t == t')) (by simp only)

def mk_const (f : func_symbols) :=
func 0 f list.nil.to_fin_fun

def mk_func (f : func_symbols) (t : list term) :=
func t.length f t.to_fin_fun


/-
pred 0 "a" [] : A propositional variable named "a".
pred n "p" [x1 ... xn] : A predicate variable named "p" of n terms (arguments).
-/
@[derive decidable_eq]
inductive formula : Type
| bottom : formula
| top : formula
| pred (n : ℕ) : pred_symbols → (fin n → term) → formula
| eq_ : term → term → formula
| not : formula → formula
| and : formula → formula → formula
| or : formula → formula → formula
| imp : formula → formula → formula
| iff : formula → formula → formula
| forall_ : var_symbols → formula → formula
| exists_ : var_symbols → formula → formula

open formula

def formula.repr : formula → string
| bottom := "⊥"
| top := "⊤"
| (pred n p t) :=
    p ++ fin_fun_to_string n (fun (i : fin n), (t i).repr)
| (eq_ s t) := sformat!"({s.repr} = {t.repr})"
| (not p) := sformat!"(¬ {p.repr})"
| (and p q) := sformat!"({p.repr} ∧ {q.repr})"
| (or p q) := sformat!"({p.repr} ∨ {q.repr})"
| (imp p q) := sformat!"({p.repr} → {q.repr})"
| (iff p q) := sformat!"({p.repr} ↔ {q.repr})"
| (forall_ x p) := sformat!"(∀ {x.repr}. {p.repr})"
| (exists_ x p) := sformat!"(∃ {x.repr}. {p.repr})"

instance formula.has_repr : has_repr formula := has_repr.mk formula.repr

instance formula.inhabited : inhabited formula :=
inhabited.mk bottom

def mk_prop (p : pred_symbols) :=
pred 0 p list.nil.to_fin_fun

def mk_pred (p : pred_symbols) (t : list term) :=
pred t.length p t.to_fin_fun


-- #eval not (forall_ "x" (mk_pred "P" [mk_func "f" [(var "x")], var "y"]))


/--
D : A nonempty set called the domain of the interpretation. The intention
is that all terms have values in D.

nonempty : A proof that there is at least one element in the domain.

func : (n : ℕ, f : func_symbols) → (fₘ : (t : fin n → D) → x : D)
A mapping of each n-ary function symbol f to a function fₘ.
n : The arity of the function symbol.
f : The function symbol.
fₘ : The function that the function symbol is mapped to.
t : The n terms (arguments) of the function expressed as a finite function.
x : The result of the function. An element in the domain.

pred : (n : ℕ, p : pred_symbols) → (pₘ : (t : fin n → D) → a : Prop)
A mapping of each n-ary predicate symbol p to a predicate pₘ.
n : The arity of the predicate symbol.
p : The predicate symbol.
pₘ : The predicate that the predicate symbol is mapped to.
t : The n terms (arguments) of the predicate expressed as a finite function.
a : The result of the predicate. A proposition.
-/
structure interpretation (D : Type) : Type :=
(nonempty : nonempty D)
(func (n : ℕ) : func_symbols → ((fin n → D) → D))
(pred (n : ℕ) : pred_symbols → ((fin n → D) → Prop))


/-
The type of mappings of variable names to elements of a domain.
-/
def valuation (D : Type) := var_symbols → D

/-
The function mapping each term to an element of a domain by a given
interpretation and valuation.
-/
def eval_term (D : Type) (m : interpretation D) (v : valuation D) : term → D
| (var x) := v x
| (func n f t) := m.func n f (fun (i : fin n), eval_term (t i))


def term.all_var_set : term → finset var_symbols
| (var x) := {x}
| (func n f t) := finset.univ.bUnion (fun (i : fin n), (t i).all_var_set)


theorem thm_1
  (D : Type)
  (m : interpretation D)
  (t : term)
  (v1 v2 : valuation D)
  (h1 : ∀ x ∈ t.all_var_set, v1 x = v2 x) :
  eval_term D m v1 t = eval_term D m v2 t :=
begin
  induction t,
  case term.var : x {
    have s1 : x ∈ (var x).all_var_set, unfold term.all_var_set,
      simp only [finset.mem_singleton],
    calc
          eval_term D m v1 (var x)
        = v1 x : by unfold eval_term
    ... = v2 x : h1 x s1
    ... = eval_term D m v2 (var x) : by unfold eval_term
  },
  case term.func : n f t ih {
    calc
          eval_term D m v1 (func n f t)
        = m.func n f (fun (i : fin n), eval_term D m v1 (t i)) :
          by unfold eval_term
    ... = m.func n f (fun (i : fin n), eval_term D m v2 (t i)) :
          begin
            congr, funext, apply ih,
            intros x h2, apply h1, unfold term.all_var_set,
            simp only [finset.mem_bUnion, finset.mem_univ, exists_true_left],
            exact exists.intro i h2
          end
    ... = eval_term D m v2 (func n f t) : by unfold eval_term
	}
end


def holds (D : Type) (m : interpretation D) : valuation D → formula → Prop
| _ bottom := false
| _ top := true
| v (pred n p t) := m.pred n p (fun (i : fin n), eval_term D m v (t i))
| v (eq_ s t) := eval_term D m v s = eval_term D m v t
| v (not p) := ¬ holds v p
| v (and p q) := holds v p ∧ holds v q
| v (or p q) := holds v p ∨ holds v q
| v (imp p q) := holds v p → holds v q
| v (iff p q) := holds v p ↔ holds v q
| v (forall_ x p) := ∀ a : D, holds (function.update v x a) p
| v (exists_ x p) := ∃ a : D, holds (function.update v x a) p

def formula.free_var_set : formula → finset var_symbols
| bottom := ∅
| top := ∅
| (pred n p t) := finset.univ.bUnion (fun (i : fin n), (t i).all_var_set)
| (eq_ s t) := s.all_var_set ∪ t.all_var_set
| (not p) := p.free_var_set
| (and p q) := p.free_var_set ∪ q.free_var_set
| (or p q) := p.free_var_set ∪ q.free_var_set
| (imp p q) := p.free_var_set ∪ q.free_var_set
| (iff p q) := p.free_var_set ∪ q.free_var_set
| (forall_ x p) := p.free_var_set \ {x}
| (exists_ x p) := p.free_var_set \ {x}

theorem thm_2
  (D : Type)
  (m : interpretation D)
  (v1 v2 : valuation D)
  (p : formula)
  (h1 : ∀ x ∈ p.free_var_set, v1 x = v2 x) :
  holds D m v1 p ↔ holds D m v2 p :=
begin
  induction p generalizing v1 v2,
  case formula.bottom {
    calc
          holds D m v1 bottom
        ↔ false : by unfold holds
    ... ↔ holds D m v2 bottom : by unfold holds
  },
  case formula.top {
    calc
          holds D m v1 top
        ↔ true : by unfold holds
    ... ↔ holds D m v2 top : by unfold holds
  },
  case formula.pred : n x t {
    unfold formula.free_var_set at h1,
    calc
        holds D m v1 (pred n x t)
        ↔ m.pred n x (fun (i : fin n), eval_term D m v1 (t i)) :
          by unfold holds
    ... ↔ m.pred n x (fun (i : fin n), eval_term D m v2 (t i)) :
          begin
            apply iff_of_eq, congr, funext,
            apply thm_1, intros x h2, apply h1,
            simp only [finset.mem_bUnion, finset.mem_univ, exists_true_left],
            exact exists.intro i h2
          end
    ... ↔ holds D m v2 (pred n x t) : by unfold holds
  },
  case formula.eq_ : s t {
    unfold formula.free_var_set at h1,
    calc
        holds D m v1 (eq_ s t)
        ↔ eval_term D m v1 s = eval_term D m v1 t : by unfold holds
    ... ↔ eval_term D m v2 s = eval_term D m v2 t :
          begin
            apply iff_of_eq, congr' 1,
            {
              apply thm_1, intros x h2, apply h1,
              simp only [finset.mem_union],
              apply or.intro_left, exact h2
            },
            {
              apply thm_1, intros x h2, apply h1,
              simp only [finset.mem_union],
              apply or.intro_right, exact h2
            },
          end
    ... ↔ holds D m v2 (eq_ s t) : by unfold holds
  },
  case formula.not : p ih {
    unfold formula.free_var_set at h1,
    have s1 : holds D m v1 p ↔ holds D m v2 p, exact ih v1 v2 h1,
    calc
          holds D m v1 (not p)
        ↔ ¬ holds D m v1 p : by unfold holds
    ... ↔ ¬ holds D m v2 p : by simp only [s1]
    ... ↔ holds D m v2 (not p) : by unfold holds
  },
  case formula.and : p q ih_p ih_q {
    unfold formula.free_var_set at h1,
    simp only [finset.mem_union, or_imp_distrib, forall_and_distrib] at h1,
    cases h1,
    have s1 : holds D m v1 p ↔ holds D m v2 p, exact ih_p v1 v2 h1_left,
    have s2 : holds D m v1 q ↔ holds D m v2 q, exact ih_q v1 v2 h1_right,
    calc
          holds D m v1 (and p q)
        ↔ (holds D m v1 p ∧ holds D m v1 q) : by unfold holds
    ... ↔ (holds D m v2 p ∧ holds D m v2 q) : by simp only [s1, s2]
    ... ↔ holds D m v2 (and p q) : by unfold holds
  },
  case formula.or : p q ih_p ih_q {
    unfold formula.free_var_set at h1,
    simp only [finset.mem_union, or_imp_distrib, forall_and_distrib] at h1,
    cases h1,
    have s1 : holds D m v1 p ↔ holds D m v2 p, exact ih_p v1 v2 h1_left,
    have s2 : holds D m v1 q ↔ holds D m v2 q, exact ih_q v1 v2 h1_right,
    calc
          holds D m v1 (or p q)
        ↔ (holds D m v1 p ∨ holds D m v1 q) : by unfold holds
    ... ↔ (holds D m v2 p ∨ holds D m v2 q) : by simp only [s1, s2]
    ... ↔ holds D m v2 (or p q) : by unfold holds
  },
  case formula.imp : p q ih_p ih_q {
    unfold formula.free_var_set at h1,
    simp only [finset.mem_union, or_imp_distrib, forall_and_distrib] at h1,
    cases h1,
    have s1 : holds D m v1 p ↔ holds D m v2 p, exact ih_p v1 v2 h1_left,
    have s2 : holds D m v1 q ↔ holds D m v2 q, exact ih_q v1 v2 h1_right,
    calc
          holds D m v1 (imp p q)
        ↔ (holds D m v1 p → holds D m v1 q) : by unfold holds
    ... ↔ (holds D m v2 p → holds D m v2 q) : by simp only [s1, s2]
    ... ↔ holds D m v2 (imp p q) : by unfold holds
  },
  case formula.iff : p q ih_p ih_q {
    unfold formula.free_var_set at h1,
    simp only [finset.mem_union, or_imp_distrib, forall_and_distrib] at h1,
    cases h1,
    have s1 : holds D m v1 p ↔ holds D m v2 p, exact ih_p v1 v2 h1_left,
    have s2 : holds D m v1 q ↔ holds D m v2 q, exact ih_q v1 v2 h1_right,
    calc
          holds D m v1 (iff p q)
        ↔ (holds D m v1 p ↔ holds D m v1 q) : by unfold holds
    ... ↔ (holds D m v2 p ↔ holds D m v2 q) : by simp only [s1, s2]
    ... ↔ holds D m v2 (iff p q) : by unfold holds
  },
  case formula.forall_ : x p ih {
    unfold formula.free_var_set at h1,
    simp only [finset.mem_sdiff, finset.mem_singleton] at h1,
    calc
          holds D m v1 (forall_ x p)
        ↔ ∀ a : D, holds D m (function.update v1 x a) p : by unfold holds
    ... ↔ ∀ a : D, holds D m (function.update v2 x a) p :
          begin
            apply forall_congr, intro a, apply ih, intros y h2,
            by_cases h3 : y = x,
            { rewrite h3, simp only [function.update_same] },
            {
              simp only [function.update_noteq h3], apply h1,
              exact and.intro h2 h3
            }
          end
    ... ↔ holds D m v2 (forall_ x p) : by unfold holds
  },
  case formula.exists_ : x p ih {
    unfold formula.free_var_set at h1,
    simp only [finset.mem_sdiff, finset.mem_singleton] at h1,
    calc
          holds D m v1 (exists_ x p)
        ↔ ∃ a : D, holds D m (function.update v1 x a) p : by unfold holds
    ... ↔ ∃ a : D, holds D m (function.update v2 x a) p :
          begin
            apply exists_congr, intro a, apply ih, intros y h2,
            by_cases h3 : y = x,
            { rewrite h3, simp only [function.update_same] },
            {
              simp only [function.update_noteq h3], apply h1,
              exact and.intro h2 h3
            }
          end
    ... ↔ holds D m v2 (exists_ x p) : by unfold holds
  }
end


def is_sentence (p : formula) : Prop :=
p.free_var_set = ∅


theorem thm_3
  (D : Type)
  (m : interpretation D)
  (v1 v2 : valuation D)
  (p : formula)
  (h1 : is_sentence p) :
  holds D m v1 p ↔ holds D m v2 p :=
begin
  unfold is_sentence at h1,
  have s1 : ∀ x ∈ p.free_var_set, v1 x = v2 x,
    rewrite h1,
    simp only [finset.not_mem_empty, forall_false_left, implies_true_iff],
  exact thm_2 D m v1 v2 p s1
end


def is_valid (p : formula) : Prop :=
∀ D : Type, ∀ m : interpretation D, ∀ v : valuation D, holds D m v p


/-
satisfies D m p = m satisfies p.
-/
def satisfies (D : Type) (m : interpretation D) (p : formula) : Prop :=
∀ v : valuation D, holds D m v p

/-
satisfies_set D m s = m satisfies s.
-/
def satisfies_set
  (D : Type) (m : interpretation D) (s : finset formula) : Prop :=
∀ p ∈ s, satisfies D m p


def is_satisfiable (p : formula) : Prop :=
∃ D : Type, ∃ m : interpretation D, satisfies D m p

def is_satisfiable_set (s : finset formula) : Prop :=
∃ D : Type, ∃ m : interpretation D, ∀ p ∈ s, satisfies D m p


/-
holds_in D m p = p holds in m.
-/
def holds_in (D : Type) (m : interpretation D) (p : formula) : Prop :=
satisfies D m p

/-
set_holds_in D m s = s holds in m.
-/
def set_holds_in
  (D : Type) (m : interpretation D) (s : finset formula) : Prop :=
satisfies_set D m s


example
	(p : formula)
	(h1 : is_sentence p) :
	is_valid p ↔ ¬ (is_satisfiable (not p)) :=
begin
  have s1 :
    (∀ (D : Type) (m : interpretation D) (v : valuation D),
      holds D m v p) →
    ∀ (D : Type) (m : interpretation D), ∃ (v : valuation D),
      holds D m v p,
    intros h2 D m,
    let v := fun (_ : var_symbols), m.nonempty.some,
    exact exists.intro v (h2 D m v),
  have s2 :
    (∀ (D : Type) (m : interpretation D), ∃ (v : valuation D),
      holds D m v p) →
    ∀ (D : Type) (m : interpretation D) (v : valuation D),
      holds D m v p,
    intros h2 D m v1,
    apply exists.elim, exact h2 D m,
    intros v2, exact iff.elim_right (thm_3 D m v1 v2 p h1),
  calc
        is_valid p
      ↔ ∀ (D : Type) (m : interpretation D) (v : valuation D),
          holds D m v p : by unfold is_valid
  ... ↔ ∀ (D : Type) (m : interpretation D), ∃ (v : valuation D),
          holds D m v p : iff.intro s1 s2
  ... ↔ ¬ ∃ (D : Type) (m : interpretation D), ∀ (v : valuation D),
          ¬ holds D m v p : begin push_neg, refl end
  ... ↔ ¬ ∃ (D : Type) (m : interpretation D), ∀ (v : valuation D),
          holds D m v (not p) : by unfold holds
  ... ↔ ¬ ∃ (D : Type) (m : interpretation D), satisfies D m (not p) :
        by unfold satisfies
  ... ↔ ¬ is_satisfiable (not p) : by unfold is_satisfiable
end


/-
is_model_of D m Γ = m is a model of Γ
-/
def is_model_of
  (D : Type) (m : interpretation D) (Γ : finset formula) : Prop :=
satisfies_set D m Γ


/-
Γ ⊨ p = p holds in all models of Γ.
-/
notation Γ `⊨` p := ∀ (D : Type) (m : interpretation D),
  (is_model_of D m Γ) → (holds_in D m p)


example
	(p : formula) :
	(is_valid p) ↔ (∅ ⊨ p) :=
begin
  split,
  {
    unfold is_valid, unfold holds_in, unfold satisfies, intros h1 D m h2,
    exact h1 D m
  },
  {
    unfold is_valid, unfold is_model_of, unfold satisfies_set,
    unfold holds_in, unfold satisfies,
    simp only [finset.not_mem_empty, forall_false_left, implies_true_iff,
    forall_true_left, imp_self]
  }
end


example
	(Γ : finset formula) :
	¬ (is_satisfiable_set Γ) ↔ (Γ ⊨ bottom) :=
begin
  unfold is_model_of, unfold is_satisfiable_set, unfold satisfies_set,
  unfold holds_in, unfold satisfies,
  split,
  {
    intros h1 D m h2 v, unfold holds, apply h1, apply exists.intro D,
    exact exists.intro m h2
  },
  {
    intros h1, push_neg, intros D m, by_contradiction, push_neg at h,
    exact h1 D m h (fun (_ : var_symbols), m.nonempty.some)
  }
end


example
	(D : Type)
	(m : interpretation D)
	(p : formula) :
	(∀ (x : var_symbols) (v : valuation D) (a : D),
    holds D m (function.update v x a) p) ↔
      (∀ v : valuation D, holds D m v p) :=
begin
  split,
  intros h1 v,
  rewrite <- function.update_eq_self default v, exact h1 default v (v default),
  intros h1 x v a, exact h1 (function.update v x a)
end


/-
A substitution mapping.
A mapping of each variable name to a term.
-/
def instantiation := var_symbols → term


-- uniform simultaneous replacement of the variables in a term by terms

def term_sub_var_term (var_to_term : instantiation) : term → term
| (var x) := var_to_term x
| (func n f t) := func n f (fun (i : fin n), term_sub_var_term (t i))

theorem thm_4
  (var_to_term : instantiation)
  (t : term) :
  (term_sub_var_term var_to_term t).all_var_set =
    t.all_var_set.bUnion (fun (y : var_symbols), (var_to_term y).all_var_set) :=
begin
  induction t,
  case term.var : x {
    calc
          (term_sub_var_term var_to_term (var x)).all_var_set
        = (var_to_term x).all_var_set : by unfold term_sub_var_term
    ... = ({x} : finset var_symbols).bUnion
            (fun (y : var_symbols), (var_to_term y).all_var_set) :
          by simp only [finset.singleton_bUnion]
    ... = (var x).all_var_set.bUnion
            (fun (y : var_symbols), (var_to_term y).all_var_set) :
          by unfold term.all_var_set
  },
  case term.func : n f t ih {
    simp only at ih,
    calc
          (term_sub_var_term var_to_term (func n f t)).all_var_set
        = (func n f
            (fun (i : fin n), term_sub_var_term var_to_term (t i))).all_var_set :
          by unfold term_sub_var_term
    ... = finset.univ.bUnion
            (fun (i : fin n), (term_sub_var_term var_to_term (t i)).all_var_set) :
          by unfold term.all_var_set
    ... = finset.univ.bUnion
            (fun (i : fin n), (t i).all_var_set.bUnion
              (fun (y : var_symbols), (var_to_term y).all_var_set)) :
          by simp only [ih]
    ... = (finset.univ.bUnion (fun (i : fin n), (t i).all_var_set)).bUnion
            (fun (y : var_symbols), (var_to_term y).all_var_set) :
          begin
            symmetry, apply finset.bUnion_bUnion
          end
    ... = (func n f t).all_var_set.bUnion
            (fun (y : var_symbols), (var_to_term y).all_var_set) :
          by unfold term.all_var_set
  }
end

theorem thm_5
  (D : Type)
  (m : interpretation D)
  (v : valuation D)
  (var_to_term : instantiation)
  (t : term) :
  eval_term D m v (term_sub_var_term var_to_term t) =
    eval_term D m ((eval_term D m v) ∘ var_to_term) t :=
begin
  induction t,
  case term.var : x {
    calc
          eval_term D m v (term_sub_var_term var_to_term (var x))
        = eval_term D m v (var_to_term x) : by unfold term_sub_var_term
    ... = ((eval_term D m v) ∘ var_to_term) x : by unfold function.comp
    ... = eval_term D m ((eval_term D m v) ∘ var_to_term) (var x) :
          by unfold eval_term
  },
  case term.func : n f t ih {
    calc
          eval_term D m v (term_sub_var_term var_to_term (func n f t))
        = eval_term D m v
            (func n f (fun (i : fin n), term_sub_var_term var_to_term (t i))) :
          by unfold term_sub_var_term
    ... = m.func n f
            (fun (i : fin n), eval_term D m v (term_sub_var_term var_to_term (t i))) :
          by unfold eval_term
    ... = m.func n f
            (fun (i : fin n), eval_term D m ((eval_term D m v) ∘ var_to_term) (t i)) :
          begin
            congr, apply funext, exact ih
          end
    ... = eval_term D m ((eval_term D m v) ∘ var_to_term) (func n f t) :
          by unfold eval_term
  }
end


-- uniform simultaneous replacement of the variables in a formula by terms

def variant (x : var_symbols) (s : finset var_symbols) : var_symbols :=
if h : x ∈ s
then s.max' (exists.intro x h) + 1
else x

lemma variant_not_mem
  (x : var_symbols)
  (s : finset var_symbols) :
  variant x s ∉ s :=
begin
  unfold variant, split_ifs,
  {
    intro con,
    have s1 : s.max' _ + 1 ≤ s.max' _, exact s.le_max' (s.max' _ + 1) con,
    have s2 : ¬ s.max' _ < s.max' _ + 1, exact s1.not_lt,
    apply s2, apply nat.lt_succ_self
  },
  { assumption }
end

def formula_sub_var_term : instantiation → formula → formula
| _ bottom := bottom
| _ top := top
| var_to_term (pred n p t) :=
    pred n p (fun (i : fin n), term_sub_var_term var_to_term (t i))
| var_to_term (eq_ s t) :=
    eq_ (term_sub_var_term var_to_term s) (term_sub_var_term var_to_term t)
| var_to_term (not p) :=
    not (formula_sub_var_term var_to_term p)
| var_to_term (and p q) :=
    and (formula_sub_var_term var_to_term p) (formula_sub_var_term var_to_term q)
| var_to_term (or p q) :=
    or (formula_sub_var_term var_to_term p) (formula_sub_var_term var_to_term q)
| var_to_term (imp p q) :=
    imp (formula_sub_var_term var_to_term p) (formula_sub_var_term var_to_term q)
| var_to_term (iff p q) :=
    iff (formula_sub_var_term var_to_term p) (formula_sub_var_term var_to_term q)
| var_to_term (forall_ x p) :=
  let x' :=
    if ∃ y ∈ p.free_var_set \ {x}, x ∈ (var_to_term y).all_var_set
    then variant x (formula_sub_var_term (function.update var_to_term x (var x)) p).free_var_set
    else x
  in forall_ x' (formula_sub_var_term (function.update var_to_term x (var x')) p)
| var_to_term (exists_ x p) :=
  let x' :=
    if ∃ y ∈ p.free_var_set \ {x}, x ∈ (var_to_term y).all_var_set
    then variant x (formula_sub_var_term (function.update var_to_term x (var x)) p).free_var_set
    else x
  in exists_ x' (formula_sub_var_term (function.update var_to_term x (var x')) p)


theorem thm_6
  (var_to_term : instantiation)
  (p : formula)
  (x : var_symbols)
  (h1 : ∀ var_to_term : instantiation, (formula_sub_var_term var_to_term p).free_var_set =
          p.free_var_set.bUnion (fun (y : var_symbols), (var_to_term y).all_var_set)) :
  let x' :=
      if ∃ y ∈ p.free_var_set \ {x}, x ∈ (var_to_term y).all_var_set
      then variant x (formula_sub_var_term (function.update var_to_term x (var x)) p).free_var_set
      else x
  in
  x' ∉ (p.free_var_set \ {x}).bUnion (fun (y : var_symbols), (var_to_term y).all_var_set) :=
begin
  intro x',
  by_cases h2 : x ∈ (p.free_var_set \ {x}).bUnion
    (fun (y : var_symbols), (var_to_term y).all_var_set),
  {
    have s1 : (p.free_var_set \ {x}).bUnion (fun y : var_symbols, (var_to_term y).all_var_set) ⊆
                (formula_sub_var_term (function.update var_to_term x (var x)) p).free_var_set,
      calc
            (p.free_var_set \ {x}).bUnion (fun (y : var_symbols), (var_to_term y).all_var_set) =
              (p.free_var_set \ {x}).bUnion
                (fun (y : var_symbols), ((function.update var_to_term x (var x)) y).all_var_set) :
            begin
              symmetry, apply finset.bUnion_congr, refl, intros a h1, congr,
              simp only [finset.mem_sdiff, finset.mem_singleton] at h1,
              cases h1,
              exact function.update_noteq h1_right (var x) var_to_term
            end
      ... ⊆ p.free_var_set.bUnion
              (fun (y : var_symbols), ((function.update var_to_term x (var x)) y).all_var_set) : 
            begin
              apply finset.bUnion_subset_bUnion_of_subset_left,
              apply finset.sdiff_subset
            end
      ... = (formula_sub_var_term (function.update var_to_term x (var x)) p).free_var_set :
            begin
              symmetry, exact h1 (function.update var_to_term x (var x))
            end,
    have s2 :
      x' = variant x (formula_sub_var_term (function.update var_to_term x (var x)) p).free_var_set,
        simp only [finset.mem_bUnion] at h2, exact if_pos h2,
    have s3 :
      x' ∉ (formula_sub_var_term (function.update var_to_term x (var x)) p).free_var_set,
        rewrite s2, apply variant_not_mem,
    exact finset.not_mem_mono s1 s3
  },
  {
    have s1 : x' = x, simp only [finset.mem_bUnion] at h2, exact if_neg h2,
    rewrite s1, exact h2
  }
end


theorem thm_7
  (var_to_term : instantiation)
  (p : formula) :
  (formula_sub_var_term var_to_term p).free_var_set =
    p.free_var_set.bUnion (fun (y : var_symbols), (var_to_term y).all_var_set) :=
begin
  induction p generalizing var_to_term,
  case formula.bottom {
    unfold formula_sub_var_term, unfold formula.free_var_set,
    simp only [finset.bUnion_empty]
  },
  case formula.top {
    unfold formula_sub_var_term, unfold formula.free_var_set,
    simp only [finset.bUnion_empty]
  },
  case formula.pred : n x t {
    calc
          (formula_sub_var_term var_to_term (pred n x t)).free_var_set =
            (pred n x (fun (i : fin n), term_sub_var_term var_to_term (t i))).free_var_set :
          by unfold formula_sub_var_term
    ... = finset.univ.bUnion (fun (i : fin n), (term_sub_var_term var_to_term (t i)).all_var_set) :
          by unfold formula.free_var_set
    ... = finset.univ.bUnion
            (fun (i : fin n), ((t i).all_var_set.bUnion
              (fun (y : var_symbols), (var_to_term y).all_var_set))) :
          by simp only [thm_4]
    ... = (finset.univ.bUnion (fun (i : fin n), (t i).all_var_set)).bUnion
            (fun (y : var_symbols), (var_to_term y).all_var_set) :
          begin
            apply finset.ext, intros a,
            simp only [finset.mem_bUnion, finset.mem_univ, exists_prop,
            exists_true_left], split,
            {
              intros h1, apply exists.elim h1, intros a2 h2,
              apply exists.elim h2, intros a3 h3, cases h3,
              apply exists.intro a3, split,
              apply exists.intro a2, exact h3_left, exact h3_right
            },
            {
              intro h1, apply exists.elim h1, intros a2 h2, cases h2,
              apply exists.elim h2_left, intros a3 h3, apply exists.intro a3,
              apply exists.intro a2, exact and.intro h3 h2_right
            }
          end
    ... = (pred n x t).free_var_set.bUnion
            (fun (y : var_symbols), (var_to_term y).all_var_set) :
          by unfold formula.free_var_set
  },
  case formula.eq_ : s t {
    calc
          (formula_sub_var_term var_to_term (eq_ s t)).free_var_set =
            (eq_ (term_sub_var_term var_to_term s) (term_sub_var_term var_to_term t)).free_var_set :
          by unfold formula_sub_var_term
    ... = (term_sub_var_term var_to_term s).all_var_set ∪
            (term_sub_var_term var_to_term t).all_var_set :
          by unfold formula.free_var_set
    ... = (s.all_var_set.bUnion (fun (y : var_symbols), (var_to_term y).all_var_set) ∪
            t.all_var_set.bUnion (fun (y : var_symbols), (var_to_term y).all_var_set)) :
          by simp only [thm_4]
    ... = (s.all_var_set ∪ t.all_var_set).bUnion
            (fun (y : var_symbols), (var_to_term y).all_var_set) :
          by simp only [finset.bUnion_union]
    ... = (eq_ s t).free_var_set.bUnion (fun (y : var_symbols), (var_to_term y).all_var_set) :
          by unfold formula.free_var_set
  },
  case formula.not : p ih {
    calc
          (formula_sub_var_term var_to_term (not p)).free_var_set =
            (not (formula_sub_var_term var_to_term p)).free_var_set :
          by unfold formula_sub_var_term
    ... = (formula_sub_var_term var_to_term p).free_var_set :
          by unfold formula.free_var_set
    ... = p.free_var_set.bUnion (fun (y : var_symbols), (var_to_term y).all_var_set) :
          ih var_to_term
    ... = (not p).free_var_set.bUnion (fun (y : var_symbols), (var_to_term y).all_var_set) :
          by unfold formula.free_var_set
  },
  case formula.and : p q ih_p ih_q {
    calc
          (formula_sub_var_term var_to_term (and p q)).free_var_set =
            (and (formula_sub_var_term var_to_term p)
              (formula_sub_var_term var_to_term q)).free_var_set :
          by unfold formula_sub_var_term
    ... = (formula_sub_var_term var_to_term p).free_var_set ∪
            (formula_sub_var_term var_to_term q).free_var_set :
          by unfold formula.free_var_set
    ... = p.free_var_set.bUnion (fun (y : var_symbols), (var_to_term y).all_var_set) ∪
            q.free_var_set.bUnion (fun (y : var_symbols), (var_to_term y).all_var_set) :
          by simp only [ih_p, ih_q]
    ... = (p.free_var_set ∪ q.free_var_set).bUnion
            (fun (y : var_symbols), (var_to_term y).all_var_set) :
          begin
            apply finset.ext, intros a,
            simp only [finset.mem_union, finset.mem_bUnion, exists_prop],
            split,
            {
              intros h1, cases h1,
              {
                apply exists.elim h1, intros a2 h2, cases h2,
                apply exists.intro a2, split,
                apply or.intro_left, exact h2_left,
                exact h2_right
              },
              {
                apply exists.elim h1, intros a2 h2, cases h2,
                apply exists.intro a2, split,
                apply or.intro_right, exact h2_left,
                exact h2_right
              }
            },
            {
              intros h1, apply exists.elim h1, intros a2 h2, cases h2,
              cases h2_left,
              {
                apply or.intro_left, apply exists.intro a2,
                exact and.intro h2_left h2_right
              },
              {
                apply or.intro_right, apply exists.intro a2,
                exact and.intro h2_left h2_right
              }
            }
          end
    ... = (and p q).free_var_set.bUnion (fun (y : var_symbols), (var_to_term y).all_var_set) :
          by unfold formula.free_var_set
  },
  case formula.or : p q ih_p ih_q {
    calc
          (formula_sub_var_term var_to_term (and p q)).free_var_set =
            (and (formula_sub_var_term var_to_term p)
              (formula_sub_var_term var_to_term q)).free_var_set :
          by unfold formula_sub_var_term
    ... = (formula_sub_var_term var_to_term p).free_var_set ∪
            (formula_sub_var_term var_to_term q).free_var_set :
          by unfold formula.free_var_set
    ... = p.free_var_set.bUnion (fun (y : var_symbols), (var_to_term y).all_var_set) ∪
            q.free_var_set.bUnion (fun (y : var_symbols), (var_to_term y).all_var_set) :
          by simp only [ih_p, ih_q]
    ... = (p.free_var_set ∪ q.free_var_set).bUnion
            (fun (y : var_symbols), (var_to_term y).all_var_set) :
          begin
            apply finset.ext, intros a,
            simp only [finset.mem_union, finset.mem_bUnion, exists_prop],
            split,
            {
              intros h1, cases h1,
              {
                apply exists.elim h1, intros a2 h2, cases h2,
                apply exists.intro a2, split,
                apply or.intro_left, exact h2_left,
                exact h2_right
              },
              {
                apply exists.elim h1, intros a2 h2, cases h2,
                apply exists.intro a2, split,
                apply or.intro_right, exact h2_left,
                exact h2_right
              }
            },
            {
              intros h1, apply exists.elim h1, intros a2 h2, cases h2,
              cases h2_left,
              {
                apply or.intro_left, apply exists.intro a2,
                exact and.intro h2_left h2_right
              },
              {
                apply or.intro_right, apply exists.intro a2,
                exact and.intro h2_left h2_right
              }
            }
          end
    ... = (and p q).free_var_set.bUnion (fun (y : var_symbols), (var_to_term y).all_var_set) :
          by unfold formula.free_var_set
  },
  case formula.imp : p q ih_p ih_q {
    calc
          (formula_sub_var_term var_to_term (and p q)).free_var_set =
            (and (formula_sub_var_term var_to_term p)
              (formula_sub_var_term var_to_term q)).free_var_set :
          by unfold formula_sub_var_term
    ... = (formula_sub_var_term var_to_term p).free_var_set ∪
            (formula_sub_var_term var_to_term q).free_var_set :
          by unfold formula.free_var_set
    ... = p.free_var_set.bUnion (fun (y : var_symbols), (var_to_term y).all_var_set) ∪
            q.free_var_set.bUnion (fun (y : var_symbols), (var_to_term y).all_var_set) :
          by simp only [ih_p, ih_q]
    ... = (p.free_var_set ∪ q.free_var_set).bUnion
            (fun (y : var_symbols), (var_to_term y).all_var_set) :
          begin
            apply finset.ext, intros a,
            simp only [finset.mem_union, finset.mem_bUnion, exists_prop],
            split,
            {
              intros h1, cases h1,
              {
                apply exists.elim h1, intros a2 h2, cases h2,
                apply exists.intro a2, split,
                apply or.intro_left, exact h2_left,
                exact h2_right
              },
              {
                apply exists.elim h1, intros a2 h2, cases h2,
                apply exists.intro a2, split,
                apply or.intro_right, exact h2_left,
                exact h2_right
              }
            },
            {
              intros h1, apply exists.elim h1, intros a2 h2, cases h2,
              cases h2_left,
              {
                apply or.intro_left, apply exists.intro a2,
                exact and.intro h2_left h2_right
              },
              {
                apply or.intro_right, apply exists.intro a2,
                exact and.intro h2_left h2_right
              }
            }
          end
    ... = (and p q).free_var_set.bUnion (fun (y : var_symbols), (var_to_term y).all_var_set) :
          by unfold formula.free_var_set
  },
  case formula.iff : p q ih_p ih_q {
    calc
          (formula_sub_var_term var_to_term (and p q)).free_var_set =
            (and (formula_sub_var_term var_to_term p)
              (formula_sub_var_term var_to_term q)).free_var_set :
          by unfold formula_sub_var_term
    ... = (formula_sub_var_term var_to_term p).free_var_set ∪
            (formula_sub_var_term var_to_term q).free_var_set :
          by unfold formula.free_var_set
    ... = p.free_var_set.bUnion (fun (y : var_symbols), (var_to_term y).all_var_set) ∪
            q.free_var_set.bUnion (fun (y : var_symbols), (var_to_term y).all_var_set) :
          by simp only [ih_p, ih_q]
    ... = (p.free_var_set ∪ q.free_var_set).bUnion
            (fun (y : var_symbols), (var_to_term y).all_var_set) :
          begin
            apply finset.ext, intros a,
            simp only [finset.mem_union, finset.mem_bUnion, exists_prop],
            split,
            {
              intros h1, cases h1,
              {
                apply exists.elim h1, intros a2 h2, cases h2,
                apply exists.intro a2, split,
                apply or.intro_left, exact h2_left,
                exact h2_right
              },
              {
                apply exists.elim h1, intros a2 h2, cases h2,
                apply exists.intro a2, split,
                apply or.intro_right, exact h2_left,
                exact h2_right
              }
            },
            {
              intros h1, apply exists.elim h1, intros a2 h2, cases h2,
              cases h2_left,
              {
                apply or.intro_left, apply exists.intro a2,
                exact and.intro h2_left h2_right
              },
              {
                apply or.intro_right, apply exists.intro a2,
                exact and.intro h2_left h2_right
              }
            }
          end
    ... = (and p q).free_var_set.bUnion (fun (y : var_symbols), (var_to_term y).all_var_set) :
          by unfold formula.free_var_set
  },
  case formula.forall_ : x p ih {
    let x' :=
      if ∃ y ∈ p.free_var_set \ {x}, x ∈ (var_to_term y).all_var_set
      then variant x (formula_sub_var_term (function.update var_to_term x (var x)) p).free_var_set
      else x,
    calc
          (formula_sub_var_term var_to_term (forall_ x p)).free_var_set
        = (forall_ x' (formula_sub_var_term
            (function.update var_to_term x (var x')) p)).free_var_set :
          by unfold formula_sub_var_term
    ... = (formula_sub_var_term
            (function.update var_to_term x (var x')) p).free_var_set \ {x'} :
          by unfold formula.free_var_set
    ... = (p.free_var_set.bUnion
            (fun (y : var_symbols),
              ((function.update var_to_term x (var x')) y).all_var_set)) \ {x'} :
          by simp only [ih (function.update var_to_term x (var x'))]
    ... = ((p.free_var_set \ {x}).bUnion
            (fun (y : var_symbols),
              ((function.update var_to_term x (var x')) y).all_var_set)) \ {x'} :
          begin
            rewrite finset.sdiff_singleton_bUnion,
            simp only [function.update_same], unfold term.all_var_set
          end
    ... = ((p.free_var_set \ {x}).bUnion
            (fun (y : var_symbols), (var_to_term y).all_var_set)) \ {x'} :
          begin
            congr' 1, apply finset.bUnion_congr, refl, intros a h1, congr,
            apply function.update_noteq,
            simp only [finset.mem_sdiff, finset.mem_singleton] at h1,
            cases h1, exact h1_right
          end
    ... = (p.free_var_set \ {x}).bUnion (fun (y : var_symbols), (var_to_term y).all_var_set) :
          begin
            apply finset.sdiff_singleton_not_mem_eq_self,
            exact thm_6 var_to_term p x ih
          end
  },
  case formula.exists_ : x p ih {
    let x' :=
      if ∃ y ∈ p.free_var_set \ {x}, x ∈ (var_to_term y).all_var_set
      then variant x (formula_sub_var_term (function.update var_to_term x (var x)) p).free_var_set
      else x,
    calc
          (formula_sub_var_term var_to_term (forall_ x p)).free_var_set
        = (forall_ x' (formula_sub_var_term
            (function.update var_to_term x (var x')) p)).free_var_set :
          by unfold formula_sub_var_term
    ... = (formula_sub_var_term
            (function.update var_to_term x (var x')) p).free_var_set \ {x'} :
          by unfold formula.free_var_set
    ... = (p.free_var_set.bUnion
            (fun (y : var_symbols),
              ((function.update var_to_term x (var x')) y).all_var_set)) \ {x'} :
          by simp only [ih (function.update var_to_term x (var x'))]
    ... = ((p.free_var_set \ {x}).bUnion
            (fun (y : var_symbols),
              ((function.update var_to_term x (var x')) y).all_var_set)) \ {x'} :
          begin
            rewrite finset.sdiff_singleton_bUnion,
            simp only [function.update_same], unfold term.all_var_set
          end
    ... = ((p.free_var_set \ {x}).bUnion
            (fun (y : var_symbols), (var_to_term y).all_var_set)) \ {x'} :
          begin
            congr' 1, apply finset.bUnion_congr, refl, intros a h1, congr,
            apply function.update_noteq,
            simp only [finset.mem_sdiff, finset.mem_singleton] at h1,
            cases h1, exact h1_right
          end
    ... = (p.free_var_set \ {x}).bUnion (fun (y : var_symbols), (var_to_term y).all_var_set) :
          begin
            apply finset.sdiff_singleton_not_mem_eq_self,
            exact thm_6 var_to_term p x ih
          end
  },
end

theorem thm_8
  (D : Type)
  (m : interpretation D)
  (v : valuation D)
  (var_to_term : instantiation)
  (p : formula) :
  holds D m v (formula_sub_var_term var_to_term p) ↔
    holds D m ((eval_term D m v) ∘ var_to_term) p :=
begin
  induction p generalizing var_to_term v,
  case formula.bottom {
    calc
          holds D m v (formula_sub_var_term var_to_term bottom) ↔
            holds D m v bottom : by unfold formula_sub_var_term
    ... ↔ false : by unfold holds
    ... ↔ holds D m (eval_term D m v ∘ var_to_term) bottom : by unfold holds
  },
  case formula.top {
    calc
          holds D m v (formula_sub_var_term var_to_term top) ↔
            holds D m v top : by unfold formula_sub_var_term
    ... ↔ true : by unfold holds
    ... ↔ holds D m (eval_term D m v ∘ var_to_term) top : by unfold holds
  },
  case formula.pred : n p t {
    calc
          holds D m v (formula_sub_var_term var_to_term (pred n p t)) ↔
            holds D m v (pred n p (fun (i : fin n), term_sub_var_term var_to_term (t i))) :
          by unfold formula_sub_var_term
    ... ↔ m.pred n p (fun (i : fin n), eval_term D m v (term_sub_var_term var_to_term (t i))) :
          by unfold holds
    ... ↔ m.pred n p (fun (i : fin n), eval_term D m ((eval_term D m v) ∘ var_to_term) (t i)) :
          by simp only [thm_5]
    ... ↔ holds D m ((eval_term D m v) ∘ var_to_term) (pred n p t) : by unfold holds
  },
  case formula.eq_ : s t {
    calc
          holds D m v (formula_sub_var_term var_to_term (eq_ s t)) ↔
            holds D m v (eq_ (term_sub_var_term var_to_term s) (term_sub_var_term var_to_term t)) :
          by unfold formula_sub_var_term
    ... ↔ (eval_term D m v (term_sub_var_term var_to_term s) =
            eval_term D m v (term_sub_var_term var_to_term t)) :
          by unfold holds
    ... ↔ (eval_term D m (eval_term D m v ∘ var_to_term) s =
            eval_term D m (eval_term D m v ∘ var_to_term) t) : by simp only [thm_5]
    ... ↔ holds D m (eval_term D m v ∘ var_to_term) (eq_ s t) : by unfold holds
  },
  case formula.not : p ih {
    calc
          holds D m v (formula_sub_var_term var_to_term (not p)) ↔
            holds D m v (not (formula_sub_var_term var_to_term p)) :
          by unfold formula_sub_var_term
    ... ↔ ¬ holds D m v (formula_sub_var_term var_to_term p) : by unfold holds
    ... ↔ ¬ holds D m ((eval_term D m v) ∘ var_to_term) p : by rewrite ih var_to_term v
    ... ↔ holds D m ((eval_term D m v) ∘ var_to_term) (not p) : by unfold holds
  },
  case formula.and : p q ih_p ih_q {
    calc
          holds D m v (formula_sub_var_term var_to_term (and p q)) ↔
            holds D m v (and (formula_sub_var_term var_to_term p)
              (formula_sub_var_term var_to_term q)) :
          by unfold formula_sub_var_term
    ... ↔ (holds D m v (formula_sub_var_term var_to_term p)) ∧
            (holds D m v (formula_sub_var_term var_to_term q)) : by unfold holds
    ... ↔ (holds D m ((eval_term D m v) ∘ var_to_term) p) ∧
            (holds D m ((eval_term D m v) ∘ var_to_term) q) :
          begin
            rewrite ih_p var_to_term v, rewrite ih_q var_to_term v
          end
    ... ↔ holds D m ((eval_term D m v) ∘ var_to_term) (and p q) : by unfold holds
  },
  case formula.or : p q ih_p ih_q {
    calc
          holds D m v (formula_sub_var_term var_to_term (or p q)) ↔
            holds D m v (or (formula_sub_var_term var_to_term p)
              (formula_sub_var_term var_to_term q)) :
          by unfold formula_sub_var_term
    ... ↔ (holds D m v (formula_sub_var_term var_to_term p)) ∨
            (holds D m v (formula_sub_var_term var_to_term q)) : by unfold holds
    ... ↔ (holds D m ((eval_term D m v) ∘ var_to_term) p) ∨
            (holds D m ((eval_term D m v) ∘ var_to_term) q) :
          begin
            rewrite ih_p var_to_term v, rewrite ih_q var_to_term v
          end
    ... ↔ holds D m ((eval_term D m v) ∘ var_to_term) (or p q) : by unfold holds
  },
  case formula.imp : p q ih_p ih_q {
    calc
          holds D m v (formula_sub_var_term var_to_term (imp p q)) ↔
            holds D m v (imp (formula_sub_var_term var_to_term p)
              (formula_sub_var_term var_to_term q)) :
          by unfold formula_sub_var_term
    ... ↔ (holds D m v (formula_sub_var_term var_to_term p)) →
            (holds D m v (formula_sub_var_term var_to_term q)) : by unfold holds
    ... ↔ (holds D m ((eval_term D m v) ∘ var_to_term) p) →
            (holds D m ((eval_term D m v) ∘ var_to_term) q) :
          begin
            rewrite ih_p var_to_term v, rewrite ih_q var_to_term v
          end
    ... ↔ holds D m ((eval_term D m v) ∘ var_to_term) (imp p q) : by unfold holds
  },
  case formula.iff : p q ih_p ih_q {
    calc
          holds D m v (formula_sub_var_term var_to_term (iff p q)) ↔
            holds D m v (iff (formula_sub_var_term var_to_term p)
              (formula_sub_var_term var_to_term q)) :
          by unfold formula_sub_var_term
    ... ↔ ((holds D m v (formula_sub_var_term var_to_term p)) ↔
            (holds D m v (formula_sub_var_term var_to_term q))) : by unfold holds
    ... ↔ ((holds D m ((eval_term D m v) ∘ var_to_term) p) ↔
            (holds D m ((eval_term D m v) ∘ var_to_term) q)) :
          begin
            rewrite ih_p var_to_term v, rewrite ih_q var_to_term v
          end
    ... ↔ holds D m ((eval_term D m v) ∘ var_to_term) (iff p q) : by unfold holds
  },
  case formula.forall_ : x p ih {
    let x' :=
      if ∃ y ∈ p.free_var_set \ {x}, x ∈ (var_to_term y).all_var_set
      then variant x (formula_sub_var_term (function.update var_to_term x (var x)) p).free_var_set
      else x,
    have s1 : ∀ (a : D) (z ∈ p.free_var_set),
      ((eval_term D m (function.update v x' a)) ∘ (function.update var_to_term x (var x'))) z =
        (function.update ((eval_term D m v) ∘ var_to_term) x a) z,
      intros a z h1,
      by_cases h2 : z = x, {
        calc
              ((eval_term D m (function.update v x' a)) ∘
                (function.update var_to_term x (var x'))) z =
                  ((eval_term D m (function.update v x' a)) ∘
                    (function.update var_to_term x (var x'))) x : by rewrite h2
        ... = (eval_term D m (function.update v x' a))
                ((function.update var_to_term x (var x')) x) :
              by simp only [function.comp_app]
        ... = (eval_term D m (function.update v x' a)) (var x') :
              by simp only [function.update_same]
        ... = (function.update v x' a) x' : by unfold eval_term
        ... = a : by simp only [function.update_same]
        ... = (function.update ((eval_term D m v) ∘ var_to_term) x a) x :
              by simp only [function.update_same]
        ... = (function.update ((eval_term D m v) ∘ var_to_term) x a) z :
              by rewrite h2
      },
      {
        have s2 : z ∈ p.free_var_set \ {x},
          simp only [finset.mem_sdiff, finset.mem_singleton],
          exact and.intro h1 h2,
        have s3 : x' ∉ (p.free_var_set \ {x}).bUnion
                    (fun (y : var_symbols), (var_to_term y).all_var_set),
          apply thm_6 var_to_term p x, intro var_to_term, exact thm_7 var_to_term p,
        have s4 : (var_to_term z).all_var_set ⊆ (p.free_var_set \ {x}).bUnion
                    (fun (y : var_symbols), (var_to_term y).all_var_set),
          exact finset.subset_bUnion_of_mem (fun (y : var_symbols), (var_to_term y).all_var_set) s2,
        have s5 : x' ∉ (var_to_term z).all_var_set, exact finset.not_mem_mono s4 s3,
        have s6 : ∀ (x : var_symbols), x ∈ (var_to_term z).all_var_set → x ≠ x',
          intros y h3, by_contradiction, apply s5, rewrite <- h, exact h3,
        calc
              ((eval_term D m (function.update v x' a)) ∘
                (function.update var_to_term x (var x'))) z =
                  (eval_term D m (function.update v x' a))
                    ((function.update var_to_term x (var x')) z) :
              by simp only [function.comp_app]
        ... = (eval_term D m (function.update v x' a)) (var_to_term z) :
              by simp only [function.update_noteq h2]
        ... = eval_term D m v (var_to_term z) :
              begin
                apply thm_1 D m (var_to_term z) (function.update v x' a) v,
                intros x h3,
                apply function.update_noteq, exact s6 x h3
              end
        ... = ((eval_term D m v) ∘ var_to_term) z : by simp only [eq_self_iff_true]
        ... = (function.update ((eval_term D m v) ∘ var_to_term) x a) z :
              begin
                symmetry, apply function.update_noteq h2
              end
      },
    calc
          holds D m v
            (formula_sub_var_term var_to_term (forall_ x p))
              ↔ holds D m v
                (forall_ x' (formula_sub_var_term (function.update var_to_term x (var x')) p)) :
          by unfold formula_sub_var_term
    ... ↔ ∀ (a : D), holds D m (function.update v x' a)
            (formula_sub_var_term (function.update var_to_term x (var x')) p) :
          by unfold holds
    ... ↔ (∀ (a : D), (holds D m
            ((eval_term D m
              (function.update v x' a)) ∘ (function.update var_to_term x (var x'))) p)) :
          begin
            apply forall_congr, intros a,
            exact ih (function.update var_to_term x (var x')) (function.update v x' a),
          end
    ... ↔ (∀ (a : D), holds D m (function.update ((eval_term D m v) ∘ var_to_term) x a) p) :
          begin
            apply forall_congr, intros a,
            rewrite (thm_2 D m
              ((eval_term D m (function.update v x' a)) ∘ (function.update var_to_term x (var x')))
              (function.update ((eval_term D m v) ∘ var_to_term) x a)
              p (s1 a)),
          end
    ... ↔ holds D m (eval_term D m v ∘ var_to_term) (forall_ x p) : by unfold holds
  },
  case formula.exists_ : x p ih {
    let x' :=
      if ∃ y ∈ p.free_var_set \ {x}, x ∈ (var_to_term y).all_var_set
      then variant x (formula_sub_var_term (function.update var_to_term x (var x)) p).free_var_set
      else x,
    have s1 : ∀ (a : D) (z ∈ p.free_var_set),
      ((eval_term D m (function.update v x' a)) ∘ (function.update var_to_term x (var x'))) z =
        (function.update ((eval_term D m v) ∘ var_to_term) x a) z,
      intros a z h1,
      by_cases h2 : z = x, {
        calc
              ((eval_term D m (function.update v x' a)) ∘
                (function.update var_to_term x (var x'))) z =
                  ((eval_term D m (function.update v x' a)) ∘
                    (function.update var_to_term x (var x'))) x : by rewrite h2
        ... = (eval_term D m
                (function.update v x' a)) ((function.update var_to_term x (var x')) x) :
              by simp only [function.comp_app]
        ... = (eval_term D m (function.update v x' a)) (var x') :
              by simp only [function.update_same]
        ... = (function.update v x' a) x' : by unfold eval_term
        ... = a : by simp only [function.update_same]
        ... = (function.update ((eval_term D m v) ∘ var_to_term) x a) x :
              by simp only [function.update_same]
        ... = (function.update ((eval_term D m v) ∘ var_to_term) x a) z :
              by rewrite h2
      },
      {
        have s2 : z ∈ p.free_var_set \ {x},
          simp only [finset.mem_sdiff, finset.mem_singleton],
          exact and.intro h1 h2,
        have s3 : x' ∉ (p.free_var_set \ {x}).bUnion
                    (fun (y : var_symbols), (var_to_term y).all_var_set),
          apply thm_6 var_to_term p x, intro var_to_term, exact thm_7 var_to_term p,
        have s4 : (var_to_term z).all_var_set ⊆ (p.free_var_set \ {x}).bUnion
                    (fun (y : var_symbols), (var_to_term y).all_var_set),
          exact finset.subset_bUnion_of_mem (fun (y : var_symbols), (var_to_term y).all_var_set) s2,
        have s5 : x' ∉ (var_to_term z).all_var_set, exact finset.not_mem_mono s4 s3,
        have s6 : ∀ (x : var_symbols), x ∈ (var_to_term z).all_var_set → x ≠ x',
          intros y h3, by_contradiction, apply s5, rewrite <- h, exact h3,
        calc
              ((eval_term D m (function.update v x' a)) ∘
                (function.update var_to_term x (var x'))) z =
                  (eval_term D m (function.update v x' a))
                    ((function.update var_to_term x (var x')) z) :
              by simp only [function.comp_app]
        ... = (eval_term D m (function.update v x' a)) (var_to_term z) :
              by simp only [function.update_noteq h2]
        ... = eval_term D m v (var_to_term z) :
              begin
                apply thm_1 D m (var_to_term z) (function.update v x' a) v,
                intros x h3,
                apply function.update_noteq, exact s6 x h3
              end
        ... = ((eval_term D m v) ∘ var_to_term) z : by simp only [eq_self_iff_true]
        ... = (function.update ((eval_term D m v) ∘ var_to_term) x a) z :
              begin
                symmetry, apply function.update_noteq h2
              end
      },
    calc
          holds D m v
            (formula_sub_var_term var_to_term (exists_ x p))
              ↔ holds D m v
                (exists_ x' (formula_sub_var_term (function.update var_to_term x (var x')) p)) :
          by unfold formula_sub_var_term
    ... ↔ ∃ (a : D), holds D m (function.update v x' a)
            (formula_sub_var_term (function.update var_to_term x (var x')) p) :
          by unfold holds
    ... ↔ (∃ (a : D), (holds D m
            ((eval_term D m
              (function.update v x' a)) ∘ (function.update var_to_term x (var x'))) p)) :
          begin
            apply exists_congr, intros a,
            exact ih (function.update var_to_term x (var x')) (function.update v x' a),
          end
    ... ↔ (∃ (a : D), holds D m (function.update ((eval_term D m v) ∘ var_to_term) x a) p) :
          begin
            apply exists_congr, intros a,
            rewrite (thm_2 D m
              ((eval_term D m (function.update v x' a)) ∘ (function.update var_to_term x (var x')))
              (function.update ((eval_term D m v) ∘ var_to_term) x a)
              p (s1 a)),
          end
    ... ↔ holds D m (eval_term D m v ∘ var_to_term) (exists_ x p) : by unfold holds
  }
end

theorem thm_9
  (var_to_term : instantiation)
  (p : formula)
  (h1 : is_valid p) :
  is_valid (formula_sub_var_term var_to_term p) :=
begin
  unfold is_valid at *,
  intros D m v,
  simp only [thm_8], apply h1
end


-- alpha equivalence

def replace_term (y z : var_symbols) (binders : finset var_symbols) : term → term
| (var x) := if x ∉ binders ∧ y = x then var z else var x
| (func n f t) := func n f (fun (i : fin n), replace_term (t i))

def replace (x y : var_symbols) : finset var_symbols → formula → formula
| binders bottom := bottom
| binders top := top
| binders (pred n p t) :=
    pred n p (fun (i : fin n), replace_term x y binders (t i))
| binders (eq_ s t) :=
    eq_ (replace_term x y binders s) (replace_term x y binders t)
| binders (not p) := not (replace binders p)
| binders (and p q) := and (replace binders p) (replace binders q)
| binders (or p q) := or (replace binders p) (replace binders q)
| binders (imp p q) := imp (replace binders p) (replace binders q)
| binders (iff p q) := iff (replace binders p) (replace binders q)
| binders (forall_ x p) := forall_ x (replace (binders ∪ {x}) p)
| binders (exists_ x p) := exists_ x (replace (binders ∪ {x}) p)

def formula.bind_var_set : formula → finset var_symbols
| bottom := ∅
| top := ∅
| (pred n p t) := ∅
| (eq_ s t) := ∅
| (not p) := p.bind_var_set
| (and p q) := p.bind_var_set ∪ q.bind_var_set
| (or p q) := p.bind_var_set ∪ q.bind_var_set
| (imp p q) := p.bind_var_set ∪ q.bind_var_set
| (iff p q) := p.bind_var_set ∪ q.bind_var_set
| (forall_ x p) := p.bind_var_set ∪ {x}
| (exists_ x p) := p.bind_var_set ∪ {x}

inductive alpha_eqv : formula → formula → Prop
| rename_forall (p : formula) (x y : var_symbols) :
  y ∉ p.free_var_set → y ∉ p.bind_var_set →
    alpha_eqv (forall_ x p) (forall_ y (replace x y ∅ p))
| rename_exists (p : formula) (x y : var_symbols) :
  y ∉ p.free_var_set → y ∉ p.bind_var_set →
    alpha_eqv (exists_ x p) (exists_ y (replace x y ∅ p))
| compat_not (p p' : formula) :
  alpha_eqv p p' → alpha_eqv (not p) (not p')
| compat_and (p p' q q' : formula) :
  alpha_eqv p p' → alpha_eqv q q' → alpha_eqv (and p q) (and p' q')
| compat_or (p p' q q' : formula) :
  alpha_eqv p p' → alpha_eqv q q' → alpha_eqv (or p q) (or p' q')
| compat_imp (p p' q q' : formula) :
  alpha_eqv p p' → alpha_eqv q q' → alpha_eqv (imp p q) (imp p' q')
| compat_iff (p p' q q' : formula) :
  alpha_eqv p p' → alpha_eqv q q' → alpha_eqv (iff p q) (iff p' q')
| compat_forall (p q : formula) (z : var_symbols) :
  alpha_eqv p q → alpha_eqv (forall_ z p) (forall_ z q)
| compat_exists (p q : formula) (z : var_symbols) :
  alpha_eqv p q → alpha_eqv (exists_ z p) (exists_ z q)
| refl (p : formula) :
  alpha_eqv p p
| symm (p p' : formula) :
  alpha_eqv p p' → alpha_eqv p' p
| trans (p p' p'' : formula) :
  alpha_eqv p p' → alpha_eqv p' p'' → alpha_eqv p p''

lemma replace_term_id
  (y z : var_symbols)
  (s : finset var_symbols)
  (t : term)
  (h1 : y ∈ s) :
  replace_term y z s t = t :=
begin
  induction t,
  case term.var : x
  {
    unfold replace_term,
    split_ifs,
    { cases h, subst h_right, exfalso, apply h_left, exact h1 },
    { refl }
  },
  case term.func : n f t ih
  {
    unfold replace_term,
    simp only at ih,
    congr, funext, exact ih i
  },
end

lemma replace_id
  (x y : var_symbols)
  (s : finset var_symbols)
  (p : formula)
  (h1 : x ∈ s) :
  replace x y s p = p :=
begin
  induction p generalizing s,
  case formula.bottom
  { unfold replace },
  case formula.top
  { unfold replace },
  case formula.pred : n p t
  { unfold replace, congr, funext, apply replace_term_id, exact h1 },
  case formula.eq_ : s t
  { unfold replace, congr, apply replace_term_id, exact h1,
    apply replace_term_id, exact h1, },
  case formula.not : p p_ih
  { unfold replace, rewrite p_ih s h1 },
  case formula.and : p q p_ih q_ih
  { unfold replace, rewrite p_ih s h1, rewrite q_ih s h1 },
  case formula.or : p q p_ih q_ih
  { unfold replace, rewrite p_ih s h1, rewrite q_ih s h1 },
  case formula.imp : p q p_ih q_ih
  { unfold replace, rewrite p_ih s h1, rewrite q_ih s h1 },
  case formula.iff : p q p_ih q_ih
  { unfold replace, rewrite p_ih s h1, rewrite q_ih s h1 },
  case formula.forall_ : z p p_ih
  {
    unfold replace, rewrite p_ih,
    simp only [finset.mem_union, finset.mem_singleton],
    apply or.intro_left, exact h1,
  },
  case formula.exists_ : x p p_ih
  {
    unfold replace, rewrite p_ih,
    simp only [finset.mem_union, finset.mem_singleton],
    apply or.intro_left, exact h1
  },
end

lemma eval_replace_term
  (D : Type)
  (m : interpretation D)
  (v : valuation D)
  (a : D)
  (x y : var_symbols)
  (s : finset var_symbols)
  (t : term)
  (h1 : x ∉ s)
  (h2 : y ∉ t.all_var_set) :
  eval_term D m (function.update v x a) t =
    eval_term D m (function.update v y a) (replace_term x y s t) :=
begin
  induction t,
  case term.var : z
  {
    unfold term.all_var_set at h2, simp only [finset.mem_singleton] at h2,
    unfold replace_term,
    by_cases x = z,
    {
      rewrite <- h, simp only [eq_self_iff_true, and_true, ite_not],
      simp only [if_neg h1], unfold eval_term, simp only [function.update_same]
    },
    {
      have s1 : ¬ (z ∉ s ∧ x = z), push_neg, intro, exact h,
      simp only [if_neg s1], unfold eval_term,
      rewrite <- ne.def at h2, rewrite ne_comm at h2,
      rewrite <- ne.def at h, rewrite ne_comm at h,
      simp only [function.update_noteq h2, function.update_noteq h]
    }
  },
  case term.func : n f t ih
  {
    unfold term.all_var_set at h2,
    simp only [finset.mem_bUnion, finset.mem_univ, exists_true_left, not_exists] at h2,
    unfold replace_term, unfold eval_term, congr, funext,
    simp only at ih, apply ih, apply h2
  },
end

lemma replace_sdiff_singleton_term
  (x y z : var_symbols)
  (s : finset var_symbols)
  (t : term)
  (h1 : x ∉ s) :
  replace_term x y s t = replace_term x y (s \ {z}) t :=
begin
  induction t,
  case term.var : u
  {
    unfold replace_term,
    by_cases x = u,
    {
      have s1 : u ∉ s ∧ x = u, rewrite <- h, split, exact h1, refl,
      have s2 : u ∉ s \ {z} ∧ x = u, subst h, split,
      apply finset.not_mem_sdiff_of_not_mem_left h1, refl,
      simp only [if_pos s1, if_pos s2]
    },
    {
      have s1 : ¬ (u ∉ s ∧ x = u), push_neg, intro, exact h,
      have s2 : ¬ (u ∉ s \ {z} ∧ x = u), push_neg, intro, exact h,
      simp only [if_neg s1, if_neg s2]
    }
  },
  case term.func : n f t ih
  {
    unfold replace_term, congr, funext, simp only at ih, apply ih
  },
end

lemma replace_sdiff_singleton
  (x y z : var_symbols)
  (p : formula)
  (s : finset var_symbols)
  (h1 : x ∉ s) :
  replace x y s p = replace x y (s \ {z}) p :=
begin
  induction p generalizing s,
  case formula.bottom
  { unfold replace },
  case formula.top
  { unfold replace },
  case formula.pred : n p t
  {
    unfold replace, congr, funext,
    apply replace_sdiff_singleton_term, exact h1
  },
  case formula.eq_ : s t
  {
    unfold replace, congr' 1,
    apply replace_sdiff_singleton_term, exact h1,
    apply replace_sdiff_singleton_term, exact h1,
  },
  case formula.not : p p_ih
  {
    unfold replace, rewrite p_ih s h1,
  },
  case formula.and : p q p_ih q_ih
  {
    unfold replace,
    rewrite p_ih s h1, rewrite q_ih s h1,
  },
  case formula.or : p q p_ih q_ih
  {
    unfold replace,
    rewrite p_ih s h1, rewrite q_ih s h1,
  },
  case formula.imp : p q p_ih q_ih
  {
    unfold replace,
    rewrite p_ih s h1, rewrite q_ih s h1,
  },
  case formula.iff : p q p_ih q_ih
  {
    unfold replace,
    rewrite p_ih s h1, rewrite q_ih s h1,
  },
  case formula.forall_ : u p p_ih
  {
    unfold replace, simp only [finset.empty_union, eq_self_iff_true, true_and],
    by_cases h : z = u,
    {
      rewrite h, simp only [finset.sdiff_union_self_eq_union],
    },
    {
      by_cases h' : x = u,
      {
        have s1 : x ∈ s ∪ {u}, simp only [finset.mem_union, finset.mem_singleton], apply or.intro_right, exact h',
        have s2 : x ∈ s \ {z} ∪ {u}, simp only [finset.mem_union, finset.mem_sdiff, finset.mem_singleton],
          apply or.intro_right, exact h',
        rewrite replace_id x y (s ∪ {u}) p s1,
        rewrite replace_id x y ((s \ {z}) ∪ {u}) p s2
      },
      {
        have s1 : ((s \ {z}) ∪ {u}) = (s ∪ {u}) \ {z}, exact finset.ne_imp_sdiff_union_comm z u s h,
        rewrite s1, apply p_ih,
        simp only [finset.mem_union, finset.mem_singleton], push_neg, exact and.intro h1 h'
      }
    }
  },
  case formula.exists_ : u p p_ih
  {
    unfold replace, simp only [finset.empty_union, eq_self_iff_true, true_and],
    by_cases h : z = u,
    {
      rewrite h, simp only [finset.sdiff_union_self_eq_union],
    },
    {
      by_cases h' : x = u,
      {
        have s1 : x ∈ s ∪ {u}, simp only [finset.mem_union, finset.mem_singleton], apply or.intro_right, exact h',
        have s2 : x ∈ s \ {z} ∪ {u}, simp only [finset.mem_union, finset.mem_sdiff, finset.mem_singleton],
          apply or.intro_right, exact h',
        rewrite replace_id x y (s ∪ {u}) p s1,
        rewrite replace_id x y ((s \ {z}) ∪ {u}) p s2
      },
      {
        have s1 : ((s \ {z}) ∪ {u}) = (s ∪ {u}) \ {z}, exact finset.ne_imp_sdiff_union_comm z u s h,
        rewrite s1, apply p_ih,
        simp only [finset.mem_union, finset.mem_singleton], push_neg, exact and.intro h1 h'
      }
    }
  },
end

lemma replace_empty_holds
  (D : Type)
  (m : interpretation D)
  (v : valuation D)
  (x y : var_symbols)
  (p : formula)
  (a : D)
  (h1 : y ∉ p.free_var_set)
  (h2 : y ∉ p.bind_var_set) :
  holds D m (function.update v x a) p ↔
    holds D m (function.update v y a) (replace x y ∅ p) :=
begin
  induction p generalizing v,
  case formula.bottom
  { unfold replace, unfold holds },
  case formula.top
  { unfold replace, unfold holds },
  case formula.pred : n p t
  {
    unfold replace, unfold holds,
    unfold formula.free_var_set at h1, simp at h1,
    apply iff_of_eq, congr, funext, apply eval_replace_term,
    simp only [finset.not_mem_empty, not_false_iff], exact h1 i
  },
  case formula.eq_ : s t {
    unfold replace, unfold holds,
    unfold formula.free_var_set at h1, simp at h1,
    push_neg at h1, cases h1,
    apply iff_of_eq, congr' 1,
    funext, apply eval_replace_term,
    simp only [finset.not_mem_empty, not_false_iff], exact h1_left,
    funext, apply eval_replace_term,
    simp only [finset.not_mem_empty, not_false_iff], exact h1_right,
  },
  case formula.not : p p_ih
  { unfold replace, unfold holds, rewrite p_ih h1 h2 },
  case formula.and : p q p_ih q_ih
  {
    unfold formula.free_var_set at h1, simp only [finset.mem_union] at h1, push_neg at h1, cases h1,
    unfold formula.bind_var_set at h2, simp only [finset.mem_union] at h2, push_neg at h2, cases h2,
    unfold replace, unfold holds,
    rewrite p_ih h1_left h2_left,
    rewrite q_ih h1_right h2_right
  },
  case formula.or : p q p_ih q_ih
  {
    unfold formula.free_var_set at h1, simp only [finset.mem_union] at h1, push_neg at h1, cases h1,
    unfold formula.bind_var_set at h2, simp only [finset.mem_union] at h2, push_neg at h2, cases h2,
    unfold replace, unfold holds,
    rewrite p_ih h1_left h2_left,
    rewrite q_ih h1_right h2_right
  },
  case formula.imp : p q p_ih q_ih
  {
    unfold formula.free_var_set at h1, simp only [finset.mem_union] at h1, push_neg at h1, cases h1,
    unfold formula.bind_var_set at h2, simp only [finset.mem_union] at h2, push_neg at h2, cases h2,
    unfold replace, unfold holds,
    rewrite p_ih h1_left h2_left,
    rewrite q_ih h1_right h2_right
  },
  case formula.iff : p q p_ih q_ih
  {
    unfold formula.free_var_set at h1, simp only [finset.mem_union] at h1, push_neg at h1, cases h1,
    unfold formula.bind_var_set at h2, simp only [finset.mem_union] at h2, push_neg at h2, cases h2,
    unfold replace, unfold holds,
    rewrite p_ih h1_left h2_left,
    rewrite q_ih h1_right h2_right
  },
  case formula.forall_ : z p p_ih
  {
    unfold formula.free_var_set at h1,
    unfold formula.bind_var_set at h2, simp only [finset.mem_union, finset.mem_singleton] at h2, push_neg at h2, cases h2,
    have s1 : y ∉ p.free_var_set, exact finset.not_mem_sdiff_ne_imp_not_mem _ _ _ h1 h2_right,
    unfold replace, unfold holds,
    simp only [finset.empty_union],
    apply forall_congr, intros a',
    by_cases h : x = z,
    {
      have s2 : ∀ u : var_symbols, u ∈ p.free_var_set →
        function.update (function.update v x a) z a' u = function.update (function.update v y a) z a' u,
          intros u h3,
          by_cases h' : u = z,
          {
            rewrite h', simp only [function.update_same]
          },
          {
            simp only [function.update_noteq h'],
            rewrite h, simp only [function.update_noteq h'],
            have s3 : u ≠ y, intro h4, apply s1, rewrite <- h4, exact h3,
            simp only [function.update_noteq s3]
          },
      rewrite replace_id,
      apply thm_2, exact s2, simp only [finset.mem_singleton], exact h
    },
    {
      have s2 : x ∉ {z}, simp only [finset.mem_singleton], exact h,
      rewrite replace_sdiff_singleton x y z p {z} s2, simp only [finset.sdiff_self], simp only at p_ih,
      have s3 : function.update (function.update v x a) z a' = function.update (function.update v z a') x a,
        apply function.update_comm h,
      have s4 : function.update (function.update v y a) z a' = function.update (function.update v z a') y a,
        apply function.update_comm h2_right,
      rewrite s3, rewrite s4,
      exact p_ih s1 h2_left (function.update v z a')
    }
  },
  case formula.exists_ : z p p_ih
  {
    unfold formula.free_var_set at h1,
    unfold formula.bind_var_set at h2, simp only [finset.mem_union, finset.mem_singleton] at h2, push_neg at h2, cases h2,
    have s1 : y ∉ p.free_var_set, exact finset.not_mem_sdiff_ne_imp_not_mem _ _ _ h1 h2_right,
    unfold replace, unfold holds,
    simp only [finset.empty_union],
    apply exists_congr, intros a',
    by_cases h : x = z,
    {
      have s2 : ∀ u : var_symbols, u ∈ p.free_var_set →
        function.update (function.update v x a) z a' u = function.update (function.update v y a) z a' u,
          intros u h3,
          by_cases h' : u = z,
          {
            rewrite h', simp only [function.update_same]
          },
          {
            simp only [function.update_noteq h'],
            rewrite h, simp only [function.update_noteq h'],
            have s3 : u ≠ y, intro h4, apply s1, rewrite <- h4, exact h3,
            simp only [function.update_noteq s3]
          },
      rewrite replace_id,
      apply thm_2, exact s2, simp only [finset.mem_singleton], exact h
    },
    {
      have s2 : x ∉ {z}, simp only [finset.mem_singleton], exact h,
      rewrite replace_sdiff_singleton x y z p {z} s2, simp only [finset.sdiff_self], simp only at p_ih,
      have s3 : function.update (function.update v x a) z a' = function.update (function.update v z a') x a,
        apply function.update_comm h,
      have s4 : function.update (function.update v y a) z a' = function.update (function.update v z a') y a,
        apply function.update_comm h2_right,
      rewrite s3, rewrite s4,
      exact p_ih s1 h2_left (function.update v z a')
    }
  },
end

theorem holds_iff_alpha_eqv_holds
  (D : Type)
  (m : interpretation D)
  (v : valuation D)
  (p p' : formula)
  (h1 : alpha_eqv p p') :
  holds D m v p ↔ holds D m v p' :=
begin
  induction h1 generalizing v,
  case alpha_eqv.rename_forall : h1_p h1_x h1_y h1_1 h1_2
  {
    unfold holds, apply forall_congr, intros a, apply replace_empty_holds, exact h1_1, exact h1_2,
  },
  case alpha_eqv.rename_exists : h1_p h1_x h1_y h1_1 h1_2
  {
    unfold holds, apply exists_congr, intros a, apply replace_empty_holds, exact h1_1, exact h1_2,
  },
  case alpha_eqv.compat_not : h1_p h1_p' h1_1 h1_ih
  {
    unfold holds, rewrite h1_ih
  },
  case alpha_eqv.compat_and : h1_p h1_p' h1_q h1_q' h1_p_1 h1_q_1 h1_ih_p h1_ih_q
  {
    unfold holds, rewrite h1_ih_p, rewrite h1_ih_q
  },
  case alpha_eqv.compat_or : h1_p h1_p' h1_q h1_q' h1_p_1 h1_q_1 h1_ih_p h1_ih_q
  {
    unfold holds, rewrite h1_ih_p, rewrite h1_ih_q
  },
  case alpha_eqv.compat_imp : h1_p h1_p' h1_q h1_q' h1_p_1 h1_q_1 h1_ih_p h1_ih_q
  {
    unfold holds, rewrite h1_ih_p, rewrite h1_ih_q
  },
  case alpha_eqv.compat_iff : h1_p h1_p' h1_q h1_q' h1_p_1 h1_q_1 h1_ih_p h1_ih_q
  {
    unfold holds, rewrite h1_ih_p, rewrite h1_ih_q
  },
  case alpha_eqv.compat_forall : h1_p h1_q h1_z h1_1 h1_ih
  {
    unfold holds, apply forall_congr, intros a, rewrite h1_ih (function.update v h1_z a)
  },
  case alpha_eqv.compat_exists : h1_p h1_q h1_z h1_1 h1_ih
  {
    unfold holds, apply exists_congr, intros a, rewrite h1_ih (function.update v h1_z a)
  },
  case alpha_eqv.refl : h1
  { refl },
  case alpha_eqv.symm : h1_p h1_p' h1_1 h1_ih
  { symmetry, exact h1_ih v },
  case alpha_eqv.trans : h1_p h1_p' h1_p'' h1_1 h1_2 h1_ih_1 h1_ih_2
  { rewrite h1_ih_1, rewrite h1_ih_2 }
end


def is_alpha_eqv_var : list (var_symbols × var_symbols) → var_symbols → var_symbols → Prop
| [] x y := x = y
| ((a, b) :: m) x y :=
    if x = a
    then b = y
    else b ≠ y ∧ is_alpha_eqv_var m x y

def is_alpha_eqv_term : list (var_symbols × var_symbols) → term → term → Prop
| m (var x) (var y) := is_alpha_eqv_var m x y
| m (func n p t) (func n' p' t') :=
    if h : n = n'
    then begin subst h; exact ∀ i, is_alpha_eqv_term m (t i) (t' i) end
    else false
| _ _ _ := false

def is_alpha_eqv : list (var_symbols × var_symbols) → formula → formula → Prop
| m bottom bottom := true
| m top top := true
| m (pred n p t) (pred n' p' t') :=
  if h : n = n'
  then begin subst h; exact ∀ i, is_alpha_eqv_term m (t i) (t' i) end
  else false
| m (not p) (not p') := is_alpha_eqv m p p'
| m (and p q) (and p' q') := is_alpha_eqv m p p' ∧ is_alpha_eqv m q q'
| m (or p q) (or p' q') := is_alpha_eqv m p p' ∧ is_alpha_eqv m q q'
| m (imp p q) (imp p' q') := is_alpha_eqv m p p' ∧ is_alpha_eqv m q q'
| m (iff p q) (iff p' q') := is_alpha_eqv m p p' ∧ is_alpha_eqv m q q'
| m (forall_ x p) (forall_ x' p') := is_alpha_eqv ((x,x')::m) p p'
| m (exists_ x p) (exists_ x' p') := is_alpha_eqv ((x,x')::m) p p'
| _ _ _ := false


-- axioms of propositional logic

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


-- axioms of predicate logic

theorem is_valid_gen
  (p : formula)
  (x : var_symbols)
  (h1 : is_valid p) :
  is_valid (forall_ x p) :=
begin
  unfold is_valid at *, unfold holds at *,
  intros D m v a,
  apply h1
end

theorem is_valid_pred_1
  (p q : formula)
  (x : var_symbols) :
  is_valid ((forall_ x (p.imp q)).imp ((forall_ x p).imp (forall_ x q))) :=
begin
  unfold is_valid, unfold holds,
  intros D m v h1 h2 a,
  apply h1 a, exact h2 a
end

def sub_single_var (x : var_symbols) (t : term) : instantiation :=
  function.update (fun v : var_symbols, var v) x t

theorem is_valid_pred_2
  (p : formula)
  (x : var_symbols)
  (t : term) :
  let s := sub_single_var x t in
  is_valid ((forall_ x p).imp (formula_sub_var_term s p)) :=
begin
  intro s,
  unfold is_valid, unfold holds,
  intros D m v h2,
    rewrite thm_8 D m v s p,
  have s1 : ((eval_term D m v) ∘ (sub_single_var x t)) =
    (function.update v x (eval_term D m v t)),
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
  (x : var_symbols)
  (h1 : x ∉ p.free_var_set) :
  is_valid (p.imp (forall_ x p)) :=
begin
  unfold is_valid, unfold holds,
  intros D m v h2 a,
  have s1 : ∀ x' ∈ p.free_var_set, (function.update v x a) x' = v x', intros x' h4, apply function.update_noteq,
    by_contradiction, apply h1, rewrite <- h, exact h4,
  rewrite @thm_2 D m (function.update v x a) v p s1, exact h2
end


inductive proof : Type
| mk (p : formula) : is_valid p → proof

meta def proof.repr : proof → string
| (proof.mk p _) := sformat!"⊢ {p.repr}"
meta instance : has_repr proof := ⟨proof.repr⟩

structure local_context_t : Type :=
(term_list : list term)
(formula_list : list formula)
(proof_list : list proof)

def local_context_t.append_term
  (context : local_context_t)
  (x : term) :
  local_context_t :=
let term_list := context.term_list ++ [x] in
local_context_t.mk term_list context.formula_list context.proof_list

def local_context_t.get_nth_term
  (context : local_context_t)
  (index : ℕ) :
  option term :=
list.nth context.term_list index

def list.get_nth_sublist
  {α : Type}
  (l : list α) :
  list ℕ → option (list α)
| [] := return []
| (index :: index_list) := do
x <- list.nth l index,
xs <- list.get_nth_sublist index_list,
return (x :: xs)

def local_context_t.get_nth_term_list
  (context : local_context_t)
  (index_list : list ℕ) :
  option (list term) :=
list.get_nth_sublist context.term_list index_list

def local_context_t.append_formula
  (context : local_context_t)
  (x : formula) :
  local_context_t :=
let formula_list := context.formula_list ++ [x] in
local_context_t.mk context.term_list formula_list context.proof_list

def local_context_t.get_nth_formula
  (context : local_context_t)
  (index : ℕ) :
  option formula :=
list.nth context.formula_list index

def local_context_t.append_proof
  (context : local_context_t)
  (x : proof) :
  local_context_t :=
let proof_list := context.proof_list ++ [x] in
local_context_t.mk context.term_list context.formula_list proof_list

def local_context_t.get_nth_proof
  (context : local_context_t)
  (index : ℕ) :
  option proof :=
list.nth context.proof_list index

structure global_context_t : Type :=
(proof_list : list proof)

def global_context_t.append_proof
  (context : global_context_t)
  (x : proof) :
  global_context_t :=
let proof_list := list.append context.proof_list [x] in
global_context_t.mk proof_list

def global_context_t.get_nth_proof
  (context : global_context_t)
  (index : ℕ) :
  option proof :=
list.nth context.proof_list index


def dguard (p : Prop) [decidable p] : option (plift p) :=
if h : p then pure (plift.up h) else failure


inductive step : Type
| var_is_term : var_symbols → step
| func_is_term : func_symbols → list ℕ → step
| bottom_is_formula : step
| top_is_formula : step
| pred_is_formula : pred_symbols → list ℕ → step
| eq_is_formula : ℕ → ℕ → step
| not_is_formula : ℕ → step
| and_is_formula : ℕ → ℕ → step
| or_is_formula : ℕ → ℕ → step
| imp_is_formula : ℕ → ℕ → step
| iff_is_formula : ℕ → ℕ → step
| mp : ℕ → ℕ → ℕ → ℕ → step
| prop_1 : ℕ → ℕ → step
| prop_2 : ℕ → ℕ → ℕ → step
| prop_3 : ℕ → ℕ → step
| gen : ℕ → ℕ → var_symbols → step
| pred_1 : ℕ → ℕ → var_symbols → step
| pred_2 : ℕ → var_symbols → ℕ → step
| pred_3 : ℕ → var_symbols → step

open step

def check_step :
global_context_t → local_context_t → step → option local_context_t

-- Syntax

| _ local_context (var_is_term x) := do
  return (local_context.append_term (var x))

| _ local_context (func_is_term f index_list) := do
  term_list <- local_context.get_nth_term_list index_list,
  return (local_context.append_term (mk_func f term_list))

| _ local_context bottom_is_formula := do
  return (local_context.append_formula bottom)

| _ local_context top_is_formula := do
  return (local_context.append_formula top)

| _ local_context (pred_is_formula r index_list) := do
  term_list <- local_context.get_nth_term_list index_list,
  return (local_context.append_formula (mk_pred r term_list))

| _ local_context (eq_is_formula lhs_index rhs_index) := do
  lhs <- local_context.get_nth_term lhs_index,
  rhs <- local_context.get_nth_term rhs_index,
  return (local_context.append_formula (eq_ lhs rhs))

| _ local_context (not_is_formula p_index) := do
  p <- local_context.get_nth_formula p_index,
  return (local_context.append_formula (not p))

| _ local_context (and_is_formula p_index q_index) := do
  p <- local_context.get_nth_formula p_index,
  q <- local_context.get_nth_formula q_index,
  return (local_context.append_formula (and p q))

| _ local_context (or_is_formula p_index q_index) := do
  p <- local_context.get_nth_formula p_index,
  q <- local_context.get_nth_formula q_index,
  return (local_context.append_formula (or p q))

| _ local_context (imp_is_formula p_index q_index) := do
  p <- local_context.get_nth_formula p_index,
  q <- local_context.get_nth_formula q_index,
  return (local_context.append_formula (imp p q))

| _ local_context (iff_is_formula p_index q_index) := do
  p <- local_context.get_nth_formula p_index,
  q <- local_context.get_nth_formula q_index,
  return (local_context.append_formula (iff p q))

-- Semantics

-- modus ponens
-- |- p & |- (p -> q) => |- q
/-
If p and q are syntactically valid formulas and p and p -> q are
semantically valid formulas then q is a semantically valid formula.
-/
| _ local_context (mp p_index q_index h1_index h2_index) := do
  p <- local_context.get_nth_formula p_index,
  q <- local_context.get_nth_formula q_index,
  -- ha : is_valid a
  (proof.mk a ha) <- local_context.get_nth_proof h1_index,
  -- hbc : is_valid (b → c)
  (proof.mk (imp b c) hbc) <- local_context.get_nth_proof h2_index | none,
  -- hap : a = p
  (plift.up hap) <- dguard (a = p),
  -- hbp : b = p
  (plift.up hbp) <- dguard (b = p),
  -- hcq : c = q
  (plift.up hcq) <- dguard (c = q),
  let t1 : is_valid q :=
  begin
    have s1 : is_valid p, rewrite <- hap, exact ha,
    have s2 : is_valid (imp p q), rewrite <- hbp, rewrite <- hcq, exact hbc,
    exact is_valid_mp p q s1 s2,
  end,
  return (local_context.append_proof (proof.mk q t1))

-- |- (p -> (q -> p))
/-
If p and q are syntactically valid formulas then (p -> (q -> p)) 
is a semantically valid formula.
-/
| _ local_context (prop_1 p_index q_index) := do
  p <- local_context.get_nth_formula p_index,
  q <- local_context.get_nth_formula q_index,
  let f := (p.imp (q.imp p)),
  let t1 : is_valid f := is_valid_prop_1 p q,
  return (local_context.append_proof (proof.mk f t1))

-- |- ((p -> (q -> r)) -> ((p -> q) -> (p -> r)))
/-
If p and q and r are syntactically valid formulas then
((p -> (q -> r)) -> ((p -> q) -> (p -> r)))
is a semantically valid formula.
-/
| _ local_context (prop_2 p_index q_index r_index) := do
  p <- local_context.get_nth_formula p_index,
  q <- local_context.get_nth_formula q_index,
  r <- local_context.get_nth_formula r_index,
  let f := ((p.imp (q.imp r)).imp ((p.imp q).imp (p.imp r))),
  let t1 : is_valid f := is_valid_prop_2 p q r,
  return (local_context.append_proof (proof.mk f t1))

-- |- ((~p -> ~q) -> (q -> p))
/-
If p and q are syntactically valid formulas then
((~p -> ~q) -> (q -> p)) is a semantically valid formula.
-/
| _ local_context (prop_3 p_index q_index) := do
  p <- local_context.get_nth_formula p_index,
  q <- local_context.get_nth_formula q_index,
  let f := (((not p).imp (not q)).imp (q.imp p)),
  let t1 : is_valid f := is_valid_prop_3 p q,
  return (local_context.append_proof (proof.mk f t1))

| _ local_context (gen p_index hp_index x) := do
  p <- local_context.get_nth_formula p_index,
  proof.mk a ha <- local_context.get_nth_proof hp_index,
  (plift.up hap) <- dguard (a = p),
  let t1 : is_valid (forall_ x p) :=
  begin
    rewrite <- hap, exact is_valid_gen a x ha,
  end,
  return (local_context.append_proof (proof.mk (forall_ x p) t1))

| _ local_context (pred_1 p_index q_index x) := do
  p <- local_context.get_nth_formula p_index,
  q <- local_context.get_nth_formula q_index,
  let f := ((forall_ x (p.imp q)).imp ((forall_ x p).imp (forall_ x q))),
  let t1 : is_valid f := is_valid_pred_1 p q x,
  return (local_context.append_proof (proof.mk f t1))

| _ local_context (pred_2 p_index x t_index) := do
  p <- local_context.get_nth_formula p_index,
  t <- local_context.get_nth_term t_index,
  let s := sub_single_var x t,
  let f := (forall_ x p).imp (formula_sub_var_term s p),
  let t1 : is_valid f := is_valid_pred_2 p x t,
  return (local_context.append_proof (proof.mk f t1))

| _ local_context (pred_3 p_index x) := do
  p <- local_context.get_nth_formula p_index,
  (plift.up h1) <- dguard (x ∉ p.free_var_set),
  let f := (p.imp (forall_ x p)),
  let t1 : is_valid f := is_valid_pred_3 p x h1,
  return (local_context.append_proof (proof.mk f t1))


def check_step_list :
global_context_t → local_context_t → list step → option global_context_t
| global_context local_context [] := do
  last_proof <- list.last' local_context.proof_list,
  return (global_context.append_proof last_proof)
| global_context local_context (step :: step_list) := do
  local_context' <- check_step global_context local_context step,
  check_step_list global_context local_context' step_list


-- example
def ex := do
  global_context <- check_step_list (global_context_t.mk []) (local_context_t.mk [] [] [])
  [
    pred_is_formula "P" [],  -- f0 = p
    imp_is_formula 0 0,   -- f1 = p -> p
    imp_is_formula 1 0,   -- f2 = (p -> p) -> p
    imp_is_formula 0 2,   -- f3 = p -> ((p -> p) -> p)
    imp_is_formula 0 1,   -- f4 = p -> (p -> p)
    imp_is_formula 4 1,   -- f5 = (p -> (p -> p)) -> (p -> p)
    imp_is_formula 3 5,   -- f6 = (p -> ((p -> p) -> p)) -> ((p -> (p -> p)) -> (p -> p))
    prop_2 0 1 0, -- p0 = |- (p -> ((p -> p) -> p)) -> ((p -> (p -> p)) -> (p -> p))
    prop_1 0 1,   -- p1 = |- p -> ((p -> p) -> p)
    mp 3 5 1 0,   -- p2 = |- (p -> (p -> p)) -> (p -> p)
    prop_1 0 0,   -- p3 = |- p -> (p -> p)
    mp 4 1 3 2    -- p4 = |- p -> p
  ],
  return global_context


-- uniform simultaneous replacement of the predicates in a formula by formulas

def formula.all_pred_set : formula → finset (ℕ × pred_symbols)
| bottom := ∅
| top := ∅
| (pred n p t) := {(n, p)}
| (eq_ s t) := ∅
| (not p) := p.all_pred_set
| (and p q) := p.all_pred_set ∪ q.all_pred_set
| (or p q) := p.all_pred_set ∪ q.all_pred_set
| (imp p q) := p.all_pred_set ∪ q.all_pred_set
| (iff p q) := p.all_pred_set ∪ q.all_pred_set
| (forall_ x p) := p.all_pred_set
| (exists_ x p) := p.all_pred_set

def formula_sub_pred_formula
  (pred_to_formula : (ℕ × string) → formula) :
  instantiation → formula → formula
| _ bottom := bottom
| _ top := top
| var_to_term (pred n x terms) :=
    formula_sub_var_term var_to_term (pred_to_formula (n, x))
| var_to_term (eq_ s t) :=
    eq_ (term_sub_var_term var_to_term s) (term_sub_var_term var_to_term t)
| var_to_term (not p) :=
    not (formula_sub_pred_formula var_to_term p)
| var_to_term (and p q) :=
    and (formula_sub_pred_formula var_to_term p) (formula_sub_pred_formula var_to_term q)
| var_to_term (or p q) :=
    or (formula_sub_pred_formula var_to_term p) (formula_sub_pred_formula var_to_term q)
| var_to_term (imp p q) :=
    imp (formula_sub_pred_formula var_to_term p) (formula_sub_pred_formula var_to_term q)
| var_to_term (iff p q) :=
    iff (formula_sub_pred_formula var_to_term p) (formula_sub_pred_formula var_to_term q)
| var_to_term (forall_ x p) :=
  let x' :=
  if x ∈ p.all_pred_set.bUnion (fun r, (pred_to_formula r).free_var_set)
  then variant x (formula_sub_pred_formula (function.update var_to_term x (var x)) p).free_var_set
  else x in
  forall_ x' (formula_sub_pred_formula (function.update var_to_term x (var x')) p)
| var_to_term (exists_ x p) :=
  let x' :=
  if x ∈ p.all_pred_set.bUnion (fun r, (pred_to_formula r).free_var_set)
  then variant x (formula_sub_pred_formula (function.update var_to_term x (var x)) p).free_var_set
  else x in
  exists_ x' (formula_sub_pred_formula (function.update var_to_term x (var x')) p)


theorem thm_10
  (t : term) :
  term_sub_var_term var t = t :=
begin
  induction t,
  case term.var : x
  { unfold term_sub_var_term },
  case term.func : n f t ih
  { unfold term_sub_var_term, congr, funext, exact ih i },
end

theorem thm_11
  (p : formula) :
  formula_sub_var_term var p = p :=
begin
  induction p,
  case formula.bottom
  { unfold formula_sub_var_term },
  case formula.top
  { unfold formula_sub_var_term },
  case formula.pred : n p t
  { unfold formula_sub_var_term, congr, funext, exact thm_10 (t i) },
  case formula.eq_ : s t
  { unfold formula_sub_var_term, congr, exact thm_10 s, exact thm_10 t },
  case formula.not : p p_ih
  { unfold formula_sub_var_term, congr, exact p_ih },
  case formula.and : p q p_ih q_ih
  { unfold formula_sub_var_term, congr, exact p_ih, exact q_ih },
  case formula.or : p q p_ih q_ih
  { unfold formula_sub_var_term, congr, exact p_ih, exact q_ih },
  case formula.imp : p q p_ih q_ih
  { unfold formula_sub_var_term, congr, exact p_ih, exact q_ih },
  case formula.iff : p q p_ih q_ih
  { unfold formula_sub_var_term, congr, exact p_ih, exact q_ih },
  case formula.forall_ : x p p_ih
  {
    unfold formula_sub_var_term,
    simp, split,
    intros y h1 h2 h3, unfold term.all_var_set at h3, simp at h3,
    subst h3, contradiction,
    unfold term.all_var_set, simp, exact p_ih
  },
  case formula.exists_ : x p p_ih
  {
    unfold formula_sub_var_term,
    simp, split,
    intros y h1 h2 h3, unfold term.all_var_set at h3, simp at h3,
    subst h3, contradiction,
    unfold term.all_var_set, simp, exact p_ih
  },
end


def interpretation.sub
  {D : Type}
  (m : interpretation D)
  (v : valuation D)
  (pred_to_formula : (ℕ × string) → formula) :
  interpretation D :=
    interpretation.mk m.nonempty m.func
      (fun (n : ℕ) (x : pred_symbols) (t : fin n → D), holds D m v (pred_to_formula (n, x)))

example
  (D : Type)
  (m : interpretation D)
  (v1 v2 : valuation D)
  (p : formula)
  (pred_to_formula : (ℕ × string) → formula)
  (hv : ∀ (r ∈ p.all_pred_set) (x ∈ (pred_to_formula r).free_var_set), v1 x = v2 x) :
  holds D m v1 (formula_sub_pred_formula pred_to_formula var p)
    ↔ holds D (m.sub v2 pred_to_formula) v1 p :=
begin
  induction p generalizing v1,
  case formula.bottom : v1 hv
  { unfold formula_sub_pred_formula, unfold holds },
  case formula.top : v1 hv
  { unfold formula_sub_pred_formula, unfold holds },
  case formula.pred : n p t v1 hv
  {
    unfold formula.all_pred_set at hv,
    unfold formula_sub_pred_formula, unfold holds,
    unfold interpretation.sub,
    simp only [thm_11],
    apply thm_2, intros x h1, apply hv (n, p),
    simp only [finset.mem_singleton], exact h1
  },
  case formula.eq_ : s t v1 hv
  {
    admit
  },
  case formula.not : p p_ih v1 hv
  {
    unfold formula_sub_pred_formula, unfold holds,
    apply not_congr, apply p_ih, exact hv,
  },
  case formula.and : p q p_ih q_ih v1 hv
  {
    unfold formula.all_pred_set at hv,
    unfold formula_sub_pred_formula, unfold holds,
    apply and_congr,
    {
      apply p_ih, intros r h1 x h2,
      apply hv r, simp only [finset.mem_union],
      apply or.intro_left, exact h1, exact h2
    },
    {
      apply q_ih, intros r h1 x h2,
      apply hv r, simp only [finset.mem_union],
      apply or.intro_right, exact h1, exact h2
    }
  },
  case formula.or : p q p_ih q_ih v1 hv
  { admit },
  case formula.imp : p q p_ih q_ih v1 hv
  { admit },
  case formula.iff : p q p_ih q_ih v1 hv
  { admit },
  case formula.forall_ : x p p_ih v1 hv
  {
    unfold formula.all_pred_set at hv,
    unfold formula_sub_pred_formula,
    unfold holds,
    apply forall_congr, intros a,
    admit,
  },
  case formula.exists_ : x p p_ih v1 hv
  { admit },
end
