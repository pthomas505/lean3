/-
References:

https://www.cambridge.org/core/books/handbook-of-practical-logic-and-automated-reasoning/EB6396296813CB562987E8C37AC4520D
https://www.cl.cam.ac.uk/~jrh13/atp/index.html
Harrison, J. (2009).
Handbook of Practical Logic and Automated Reasoning.
Cambridge: Cambridge University Press.
doi:10.1017/CBO9780511576430
-/


import data.finset data.finmap data.list.alist


lemma finset.mem_ite
  {α : Type}
  (x : α)
  (p : Prop)
  [decidable p]
  (s s' : finset α) :
  x ∈ (if p then s else s') ↔ (p → x ∈ s) ∧ (¬ p → x ∈ s') :=
begin
  split,
  {
    intro h1,
    split,
      { intro h2, simp only [if_pos h2] at h1, exact h1, },
      { intro h2, simp only [if_neg h2] at h1, exact h1, },
  },
  {
    intro h1, cases h1,
    split_ifs,
      { exact h1_left h, },
      { exact h1_right h, },
  },
end

lemma finset.bUnion_sdiff
  {α β : Type}
  [decidable_eq α] [decidable_eq β]
  (s : finset α)
  (t : α → finset β)
  (s' : finset β) :
  (finset.bUnion s t) \ s' = finset.bUnion s (fun x : α, t x \ s') :=
begin
  apply finset.ext, intro a,
  simp only [finset.mem_sdiff, finset.mem_bUnion, exists_prop],
  split,
  {
    intro h1, cases h1, apply exists.elim h1_left,
    intros b h2, cases h2, apply exists.intro b,
    split,
      { exact h2_left, },
      { exact and.intro h2_right h1_right, },
  },
  {
    intro h1, apply exists.elim h1,
    intros b h2, cases h2, cases h2_right,
    split,
      { apply exists.intro b, exact and.intro h2_left h2_right_left, },
      { exact h2_right_right, },
  },
end

lemma finset.bUnion_filter
  {α β : Type}
  [decidable_eq α] [decidable_eq β]
  (s : finset α)
  (t : α → finset β)
  (p : α → Prop)
  [decidable_pred p] :
  finset.bUnion (finset.filter p s) t =
    finset.bUnion s (fun x, if p x then t x else ∅) :=
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
      { exact h2_left_left, },
      { exact and.intro h2_right h2_left_right, },
  },
  {
    intro h1, apply exists.elim h1, intros b h2, cases h2, cases h2_right,
    apply exists.intro b,
    split,
      { exact and.intro h2_left h2_right_right, },
      { exact h2_right_left },
  },
end

lemma finset.sdiff_singleton_bUnion
  {α β : Type}
  [decidable_eq α] [decidable_eq β]
  (s : finset α)
  (t : α → finset β)
  (x : α)
  (s' : finset β)
  (h1 : t x = s') :
  (finset.bUnion (s \ {x}) t) \ s' = (finset.bUnion s t) \ s' :=
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
      { intro h3, simp only [finset.not_mem_empty] at h3, contradiction, },
      { intro h3, exact h3, },
  },
  {
    intro h3,
    split_ifs,
      { simp only [finset.not_mem_empty], apply h2, rewrite <- h, exact h3, },
      { exact h3, },
  },
end

lemma finset.bUnion_union
  {α β : Type}
  [decidable_eq α] [decidable_eq β]
  (s s' : finset α)
  (t : α → finset β) :
  finset.bUnion (s ∪ s') t = finset.bUnion s t ∪ finset.bUnion s' t :=
begin
  apply finset.ext, intro a,
  simp only [or_and_distrib_right, exists_or_distrib, finset.mem_bUnion,
    finset.mem_union, exists_prop]
end

lemma finset.bUnion_sdiff_of_forall_disjoint
  {α β : Type}
  [decidable_eq β]
  (s : finset α)
  (t : α → finset β)
  (s' : finset β)
  (h1 : ∀ y : α, y ∈ s → disjoint (t y) s') :
  (finset.bUnion s t) \ s' = finset.bUnion s t :=
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
      { cases h2, apply or.intro_left, exact h2_left, },
      { apply or.intro_right, exact h2 }
    },
    {
      cases h2,
      { cases h2, exact h2_right, },
      { rewrite h2, rewrite ne_comm at h1, exact h1, }
    }
  },
  {
    intros h2, cases h2,
    cases h2_left,
    { apply or.intro_left, exact and.intro h2_left h2_right, },
    { apply or.intro_right, exact h2_left, }
  }
end


lemma finset.mem_ne_imp_mem_sdiff
  {α : Type}
  [decidable_eq α]
  {x y : α}
  {s : finset α}
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
  {x y : α}
  {s : finset α}
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
  {x y : α}
  {s : finset α}
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
  {x y : α}
  {s : finset α}
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
  {x y : α}
  {s : finset α}
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
  {x y : α}
  {s : finset α}
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
  {x y : α}
  {s : finset α}
  (h1 : x ∉ s \ {y})
  (h2 : x ≠ y) :
  x ∉ s :=
begin
  simp only [finset.mem_sdiff, finset.mem_singleton] at h1,
  push_neg at h1,
  intro h3, apply h2, exact h1 h3
end


def list.to_fin_fun {T : Type} (l : list T) : fin l.length → T :=
fun i : fin l.length, list.nth_le l i.val i.property


meta def fin_fun_to_string {T : Type} [has_to_string T]
  {n : ℕ} (f : fin n → T) : string :=
list.to_string (list.of_fn f)


abbreviation var_symbols := ℕ
abbreviation func_symbols := string
abbreviation pred_symbols := string


/-
var "x" : An object variable named "x". Ranges over the domain of each
interpretation.
func 0 "c" [] : A constant named "c".
func n "f" [x1 ... xn] : A function named "f" of n terms (arguments).
-/
inductive term : Type
| var : var_symbols → term
| func (n : ℕ) : func_symbols → (fin n → term) → term

open term

meta def term.repr : term → string
| (var x) := x.repr
| (func n f terms) :=
    f.quote ++ fin_fun_to_string (fun i : fin n, (terms i).repr)

meta instance : has_repr term := has_repr.mk term.repr

def mk_const (symbol : func_symbols) :=
func 0 symbol list.nil.to_fin_fun

def mk_func (symbol : func_symbols) (terms : list term) :=
func terms.length symbol terms.to_fin_fun


def pi_decide {p q : Prop} [decidable p] (h : p → decidable q) : decidable (p ∧ q) :=
if hp : p then
  by haveI := h hp; exact
  if hq : q then is_true ⟨hp, hq⟩
  else is_false (assume h : p ∧ q, hq (and.right h))
else is_false (assume h : p ∧ q, hp (and.left h))

instance : decidable_eq term
| (var s₁) (var s₂) :=
    decidable_of_decidable_of_iff (by apply_instance : decidable (s₁ = s₂)) (by simp)
| (var s) (func n s' t) := is_false (by simp)
| (func n s' t) (var s) := is_false (by simp)
| (func n₁ s₁ t₁) (func n₂ s₂ t₂) := decidable_of_decidable_of_iff
  (begin
    apply' pi_decide,
    intro h,
    apply' and.decidable,
    rw fin.heq_fun_iff h,
    apply' fintype.decidable_forall_fintype,
    intro a,
    apply term.decidable_eq,
  end : decidable $ n₁ = n₂ ∧ s₁ = s₂ ∧ t₁ == t₂) (by simp)

/-
pred 0 "P" [] : A propositional variable named "P".
pred n "P" [x1 ... xn] : A predicate variable named "P" of n terms (arguments).
-/
@[derive decidable_eq]
inductive formula : Type
| bottom : formula
| top : formula
| pred (n : ℕ) : pred_symbols → (fin n → term) → formula
| eq : term → term → formula
| not : formula → formula
| and : formula → formula → formula
| or : formula → formula → formula
| imp : formula → formula → formula
| iff : formula → formula → formula
| forall_ : var_symbols → formula → formula
| exists_ : var_symbols → formula → formula

open formula

meta def formula.repr : formula → string
| bottom := "⊥"
| top := "⊤"
| (pred n x terms) :=
    x.quote ++ fin_fun_to_string (fun i : fin n, (terms i).repr)
| (eq s t) := sformat!"({s.repr} = {t.repr})"
| (not p) := sformat!"(¬ {p.repr})"
| (and p q) := sformat!"({p.repr} ∧ {q.repr})"
| (or p q) := sformat!"({p.repr} ∨ {q.repr})"
| (imp p q) := sformat!"({p.repr} → {q.repr})"
| (iff p q) := sformat!"({p.repr} ↔ {q.repr})"
| (forall_ x p) := sformat!"(∀ {x.repr}. {p.repr})"
| (exists_ x p) := sformat!"(∃ {x.repr}. {p.repr})"

meta instance : has_repr formula := has_repr.mk formula.repr

def mk_prop (symbol : pred_symbols) :=
pred 0 symbol list.nil.to_fin_fun

def mk_pred (symbol : pred_symbols) (terms : list term) :=
pred terms.length symbol terms.to_fin_fun


-- #eval not (forall_ "x" (mk_pred "P" [mk_func "f" [(var "x")], var "y"]))


/-
domain: A nonempty set D called the domain of the interpretation.
The intention is that all terms have values in D.

nonempty: A proof that there is at least one element in the domain.

func: (n : ℕ, f : string) → (f_{M} : (terms : fin n → domain) → v : domain)
A mapping of each n-ary function symbol f to a function f_{M}.
n : The arity of the function symbol.
f : The function symbol.
f_{M} : The function that the function symbol is mapped to.
terms : fin n → domain : The n terms (arguments) of the function expressed as
a finite function.
v : domain : The result of the function. An element in the domain.

pred: (n : ℕ, P : string) → (P_{M} : (terms : fin n → domain) → v : Prop)
A mapping of each n-ary predicate symbol P to a predicate P_{M}.
n : The arity of the predicate symbol.
P : The predicate symbol.
P_{M} : The predicate that the predicate symbol is mapped to.
terms : fin n → domain : The n terms (arguments) of the predicate expressed
as a finite function.
v : Prop : The result of the predicate. True or false.
-/
structure interpretation (domain : Type) : Type :=
(nonempty : nonempty domain)
(func (n : ℕ) : func_symbols → (fin n → domain) → domain)
(pred (n : ℕ) : pred_symbols → (fin n → domain) → Prop)


/-
The type of mappings of object variable names to elements of a domain.
-/
def valuation (D : Type) := var_symbols → D

/-
The function mapping each term to an element of a domain by a given
interpretation and valuation.
-/
def eval_term (D : Type) (m : interpretation D) (v : valuation D) : term → D
| (var x) := v x
| (func n f terms) := m.func n f (fun i : fin n, eval_term (terms i))


def term.all_var_set : term → finset var_symbols
| (var x) := {x}
| (func n f terms) :=
    finset.bUnion finset.univ (fun i : fin n, (terms i).all_var_set)


theorem thm_1
  {D : Type}
  {m : interpretation D}
  {t : term}
  (v v' : valuation D)
  (h1 : ∀ x ∈ t.all_var_set, v x = v' x) :
  eval_term D m v t = eval_term D m v' t :=
begin
  induction t,
  case term.var : x {
    have s1 : x ∈ (var x).all_var_set, unfold term.all_var_set,
      simp only [finset.mem_singleton],
    calc
          eval_term D m v (var x)
        = v x : by unfold eval_term
    ... = v' x : h1 x s1
    ... = eval_term D m v' (var x) : by unfold eval_term
  },
  case term.func : n f terms ih {
    calc
          eval_term D m v (func n f terms)
        = m.func n f (fun i : fin n, eval_term D m v (terms i)) :
            by unfold eval_term
    ... = m.func n f (fun i : fin n, eval_term D m v' (terms i)) :
      begin
        congr, funext, apply ih,
        intros x h2, apply h1, unfold term.all_var_set,
        simp only [finset.mem_bUnion, finset.mem_univ, exists_true_left],
        exact exists.intro i h2
      end
    ... = eval_term D m v' (func n f terms) : by unfold eval_term
	}
end


--notation a' ` ↦ `:25 v := fun f, function.update f a' v


def holds (D : Type) (m : interpretation D) : valuation D → formula → Prop
| _ bottom := false
| _ top := true
| v (pred n x terms) := m.pred n x (fun i : fin n, eval_term D m v (terms i))
| v (eq s t) := eval_term D m v s = eval_term D m v t
| v (not p) := ¬ holds v p
| v (and p q) := holds v p ∧ holds v q
| v (or p q) := holds v p ∨ holds v q
| v (imp p q) := holds v p → holds v q
| v (iff p q) := holds v p ↔ holds v q
| v (forall_ x p) := ∀ a : D, holds (function.update v x a) p
| v (exists_ x p) := ∃ a : D, holds (function.update v x a) p


def formula.all_var_set : formula → finset var_symbols
| bottom := ∅
| top := ∅
| (pred n x terms) :=
    finset.bUnion finset.univ (fun i : fin n, (terms i).all_var_set)
| (eq s t) := s.all_var_set ∪ t.all_var_set
| (not p) := p.all_var_set
| (and p q) := p.all_var_set ∪ q.all_var_set
| (or p q) := p.all_var_set ∪ q.all_var_set
| (imp p q) := p.all_var_set ∪ q.all_var_set
| (iff p q) := p.all_var_set ∪ q.all_var_set
| (forall_ x p) := p.all_var_set ∪ {x}
| (exists_ x p) := p.all_var_set ∪ {x}

def formula.all_pred_set : formula → finset (ℕ × pred_symbols)
| bottom := ∅
| top := ∅
| (pred n x terms) := {(n, x)}
| (eq _ _) := ∅
| (not p) := p.all_pred_set
| (and p q) := p.all_pred_set ∪ q.all_pred_set
| (or p q) := p.all_pred_set ∪ q.all_pred_set
| (imp p q) := p.all_pred_set ∪ q.all_pred_set
| (iff p q) := p.all_pred_set ∪ q.all_pred_set
| (forall_ x p) := p.all_pred_set
| (exists_ x p) := p.all_pred_set

def formula.free_var_set : formula → finset var_symbols
| bottom := ∅
| top := ∅
| (pred n x terms) :=
    finset.bUnion finset.univ (fun i : fin n, (terms i).all_var_set)
| (eq s t) := s.all_var_set ∪ t.all_var_set
| (not p) := p.free_var_set
| (and p q) := p.free_var_set ∪ q.free_var_set
| (or p q) := p.free_var_set ∪ q.free_var_set
| (imp p q) := p.free_var_set ∪ q.free_var_set
| (iff p q) := p.free_var_set ∪ q.free_var_set
| (forall_ x p) := p.free_var_set \ {x}
| (exists_ x p) := p.free_var_set \ {x}

def formula.bind_var_set : formula → finset var_symbols
| bottom := ∅
| top := ∅
| (pred n x terms) := ∅
| (eq _ _) := ∅
| (not p) := p.bind_var_set
| (and p q) := p.bind_var_set ∪ q.bind_var_set
| (or p q) := p.bind_var_set ∪ q.bind_var_set
| (imp p q) := p.bind_var_set ∪ q.bind_var_set
| (iff p q) := p.bind_var_set ∪ q.bind_var_set
| (forall_ x p) := p.bind_var_set ∪ {x}
| (exists_ x p) := p.bind_var_set ∪ {x}


theorem thm_2
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
  case formula.pred : n x terms {
    unfold formula.free_var_set at h1,
    calc
        holds D m v (pred n x terms)
        ↔ m.pred n x (fun i : fin n, eval_term D m v (terms i)) :
      by unfold holds
    ... ↔ m.pred n x (fun i : fin n, eval_term D m v' (terms i)) :
      begin
        apply iff_of_eq, congr, funext,
        apply thm_1, intros x h, apply h1,
        simp only [finset.mem_bUnion, finset.mem_univ, exists_true_left],
        exact exists.intro i h
      end
    ... ↔ holds D m v' (pred n x terms) : by unfold holds
  },
  case formula.eq : s t {
    unfold formula.free_var_set at h1,
    calc
        holds D m v (eq s t)
        ↔ eval_term D m v s = eval_term D m v t : by unfold holds
    ... ↔ eval_term D m v' s = eval_term D m v' t :
      begin
        apply iff_of_eq, congr' 1,
        {
          apply thm_1, intros x h, apply h1,
          simp only [finset.mem_union],
          apply or.intro_left, exact h,
        },
        {
          apply thm_1, intros x h, apply h1,
          simp only [finset.mem_union],
          apply or.intro_right, exact h,
        },
      end
    ... ↔ holds D m v' (eq s t) : by unfold holds
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
    unfold formula.free_var_set at h1,
    simp only [finset.mem_union, or_imp_distrib, forall_and_distrib] at h1,
    cases h1,
    have s1 : holds D m v p ↔ holds D m v' p, exact ih_p v v' h1_left,
    have s2 : holds D m v q ↔ holds D m v' q, exact ih_q v v' h1_right,
    calc
          holds D m v (and p q)
        ↔ (holds D m v p ∧ holds D m v q) : by unfold holds
    ... ↔ (holds D m v' p ∧ holds D m v' q) : by simp only [s1, s2]
    ... ↔ holds D m v' (and p q) : by unfold holds
  },
  case formula.or : p q ih_p ih_q {
    unfold formula.free_var_set at h1,
    simp only [finset.mem_union, or_imp_distrib, forall_and_distrib] at h1,
    cases h1,
    have s1 : holds D m v p ↔ holds D m v' p, exact ih_p v v' h1_left,
    have s2 : holds D m v q ↔ holds D m v' q, exact ih_q v v' h1_right,
    calc
          holds D m v (or p q)
        ↔ (holds D m v p ∨ holds D m v q) : by unfold holds
    ... ↔ (holds D m v' p ∨ holds D m v' q) : by simp only [s1, s2]
    ... ↔ holds D m v' (or p q) : by unfold holds
  },
  case formula.imp : p q ih_p ih_q {
    unfold formula.free_var_set at h1,
    simp only [finset.mem_union, or_imp_distrib, forall_and_distrib] at h1,
    cases h1,
    have s1 : holds D m v p ↔ holds D m v' p, exact ih_p v v' h1_left,
    have s2 : holds D m v q ↔ holds D m v' q, exact ih_q v v' h1_right,
    calc
          holds D m v (imp p q)
        ↔ (holds D m v p → holds D m v q) : by unfold holds
    ... ↔ (holds D m v' p → holds D m v' q) : by simp only [s1, s2]
    ... ↔ holds D m v' (imp p q) : by unfold holds
  },
  case formula.iff : p q ih_p ih_q {
    unfold formula.free_var_set at h1,
    simp only [finset.mem_union, or_imp_distrib, forall_and_distrib] at h1,
    cases h1,
    have s1 : holds D m v p ↔ holds D m v' p, exact ih_p v v' h1_left,
    have s2 : holds D m v q ↔ holds D m v' q, exact ih_q v v' h1_right,
    calc
          holds D m v (iff p q)
        ↔ (holds D m v p ↔ holds D m v q) : by unfold holds
    ... ↔ (holds D m v' p ↔ holds D m v' q) : by simp only [s1, s2]
    ... ↔ holds D m v' (iff p q) : by unfold holds
  },
  case formula.forall_ : x p ih {
    unfold formula.free_var_set at h1,
    simp only [finset.mem_sdiff, finset.mem_singleton] at h1,
    calc
          holds D m v (forall_ x p)
        ↔ ∀ a : D, holds D m (function.update v x a) p : by unfold holds
    ... ↔ ∀ a : D, holds D m (function.update v' x a) p :
      begin
        apply forall_congr, intro a, apply ih, intros y h3,
        by_cases y = x,
        rewrite h, simp only [function.update_same],
        simp only [function.update_noteq h], apply h1, exact and.intro h3 h
      end
    ... ↔ holds D m v' (forall_ x p) : by unfold holds
  },
  case formula.exists_ : x p ih {
    unfold formula.free_var_set at h1,
    simp only [finset.mem_sdiff, finset.mem_singleton] at h1,
    calc
          holds D m v (exists_ x p)
        ↔ ∃ a : D, holds D m (function.update v x a) p : by unfold holds
    ... ↔ ∃ a : D, holds D m (function.update v' x a) p :
      begin
        apply exists_congr, intro a, apply ih, intros y h3,
        by_cases y = x,
        rewrite h, simp only [function.update_same],
        simp only [function.update_noteq h], apply h1, exact and.intro h3 h
      end
    ... ↔ holds D m v' (exists_ x p) : by unfold holds
  }
end


def is_sentence (p : formula) : Prop :=
p.free_var_set = ∅


theorem thm_3
  {p : formula}
  {D : Type}
  {m : interpretation D}
  (v v' : valuation D)
  (h1 : is_sentence p) :
  holds D m v p ↔ holds D m v' p :=
begin
  unfold is_sentence at h1,
  have s1 : ∀ x ∈ p.free_var_set, v x = v' x,
    rewrite h1,
    simp only [finset.not_mem_empty, forall_false_left, implies_true_iff],
  exact thm_2 v v' s1
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
def satisfies_set (D : Type)
  (m : interpretation D) (s : finset formula) : Prop :=
∀ p ∈ s, satisfies D m p


def is_satisfiable (p : formula) : Prop :=
∃ D : Type, ∃ m : interpretation D, satisfies D m p

def is_satisfiable_set (s : finset formula) : Prop :=
∃ D : Type, ∃ m : interpretation D, ∀ p ∈ s, satisfies D m p


/-
holds_in p D m = p holds in m.
-/
def holds_in (p : formula) (D : Type) (m : interpretation D) : Prop :=
satisfies D m p

/-
set_holds_in S D m = S holds in m.
-/
def set_holds_in (s : finset formula) (D : Type)
  (m : interpretation D) : Prop :=
satisfies_set D m s


example
	(p : formula)
	(h1 : is_sentence p) :
	is_valid p ↔ ¬ (is_satisfiable (not p)) :=
begin
  have s1 : (∀ (D : Type) (m : interpretation D) (v : valuation D),
      holds D m v p) →
    ∀ (D : Type) (m : interpretation D), ∃ (v : valuation D),
      holds D m v p,
    intros h2 D m,
    let v := fun _ : var_symbols, m.nonempty.some,
    exact exists.intro v (h2 D m v),
  have s2 : (∀ (D : Type) (m : interpretation D), ∃ (v : valuation D),
      holds D m v p) →
    ∀ (D : Type) (m : interpretation D) (v : valuation D),
      holds D m v p,
    intros h2 D m v,
    apply exists.elim, exact h2 D m,
    intros v', exact iff.elim_right (thm_3 v v' h1),
  calc
        is_valid p
      ↔ ∀ (D : Type) (m : interpretation D) (v : valuation D),
          holds D m v p : by unfold is_valid
  ... ↔ ∀ (D : Type) (m : interpretation D), ∃ (v : valuation D),
          holds D m v p : iff.intro s1 s2
  ... ↔ ¬∃ (D : Type) (m : interpretation D), ∀ (v : valuation D),
          ¬holds D m v p : begin push_neg, refl end
  ... ↔ ¬∃ (D : Type) (m : interpretation D), ∀ (v : valuation D),
          holds D m v (not p) : by unfold holds
  ... ↔ ¬∃ (D : Type) (m : interpretation D), satisfies D m (not p) :
          by unfold satisfies
  ... ↔ ¬is_satisfiable (not p) : by unfold is_satisfiable
end


/-
is_model_of D m Γ = m is a model of Γ
-/
def is_model_of (D : Type) (m : interpretation D) (Γ : finset formula) :=
satisfies_set D m Γ


/-
Γ ⊨ p = p holds in all models of Γ.
-/
notation Γ `⊨` p := ∀ D : Type, ∀ m : interpretation D,
  (is_model_of D m Γ) → (holds_in p D m)


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
    exact h1 D m h (fun _ : var_symbols, m.nonempty.some)
  }
end


example
	(D : Type)
	(m : interpretation D)
	(p : formula) :
	(∀ x : var_symbols, ∀ v : valuation D, ∀ a : D,
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

def term.sub_var_term (s : instantiation) : term → term
| (var x) := s x
| (func n name terms) :=
    func n name (fun i : fin n, term.sub_var_term (terms i))

theorem thm_4
  (t : term)
  (s : instantiation) :
  (term.sub_var_term s t).all_var_set =
    finset.bUnion t.all_var_set (fun y : var_symbols, (s y).all_var_set) :=
begin
  induction t,
  case term.var : x {
    calc
          (term.sub_var_term s (var x)).all_var_set
        = (s x).all_var_set : by unfold term.sub_var_term
    ... = finset.bUnion {x} (fun y : var_symbols, (s y).all_var_set) :
          by simp only [finset.singleton_bUnion]
    ... = finset.bUnion (var x).all_var_set (fun y : var_symbols, (s y).all_var_set) :
          by unfold term.all_var_set
  },
  case term.func : n f terms ih {
    simp at ih,
    calc
          (term.sub_var_term s (func n f terms)).all_var_set
        = (func n f
            (fun i : fin n, term.sub_var_term s (terms i))).all_var_set :
          by unfold term.sub_var_term
    ... = finset.bUnion finset.univ
            (fun i : fin n, (term.sub_var_term s (terms i)).all_var_set) :
          by unfold term.all_var_set
    ... = finset.bUnion finset.univ
            (fun i : fin n, finset.bUnion
              (terms i).all_var_set
              (fun y : var_symbols, (s y).all_var_set)) :
          by simp only [ih]
    ... = finset.bUnion
            (finset.bUnion finset.univ (fun i : fin n, (terms i).all_var_set))
            (fun y : var_symbols, (s y).all_var_set) :
          begin symmetry, apply finset.bUnion_bUnion end
    ... = finset.bUnion
            (func n f terms).all_var_set
            (fun y : var_symbols, (s y).all_var_set) : by unfold term.all_var_set
  }
end

lemma thm_5
  (D : Type)
  (t : term)
  (s : instantiation)
  (m : interpretation D)
  (v : valuation D) :
  eval_term D m v (term.sub_var_term s t) =
    eval_term D m ((eval_term D m v) ∘ s) t :=
begin
  induction t,
  case term.var : x {
    calc
          eval_term D m v (term.sub_var_term s (var x))
        = eval_term D m v (s x) : by unfold term.sub_var_term
    ... = ((eval_term D m v) ∘ s) x : by unfold function.comp
    ... = eval_term D m ((eval_term D m v) ∘ s) (var x) : by unfold eval_term
  },
  case term.func : n f terms ih {
    have ih' : ∀ (i : fin n), eval_term D m v (term.sub_var_term s (terms i)) =
      eval_term D m ((eval_term D m v) ∘ s) (terms i), exact ih,
    calc
          eval_term D m v (term.sub_var_term s (func n f terms))
        = eval_term D m v (func n f (fun i, term.sub_var_term s (terms i))) :
          by unfold term.sub_var_term
    ... = m.func n f (fun i, eval_term D m v (term.sub_var_term s (terms i))) :
          by unfold eval_term
    ... = m.func n f (fun i, eval_term D m ((eval_term D m v) ∘ s) (terms i)) :
          begin congr, apply funext, exact ih' end
    ... = eval_term D m ((eval_term D m v) ∘ s) (func n f terms) :
          by unfold eval_term
  }
end


-- uniform simultaneous replacement of the variables in a formula by terms

def formula.sub_var_term (s : instantiation) : formula → formula
| bottom := bottom
| top := top
| (pred n x terms) := pred n x (fun i : fin n, term.sub_var_term s (terms i))
| (eq u v) := eq (term.sub_var_term s u) (term.sub_var_term s v)
| (not p) := not (formula.sub_var_term p)
| (and p q) := and (formula.sub_var_term p) (formula.sub_var_term q)
| (or p q) := or (formula.sub_var_term p) (formula.sub_var_term q)
| (imp p q) := imp (formula.sub_var_term p) (formula.sub_var_term q)
| (iff p q) := iff (formula.sub_var_term p) (formula.sub_var_term q)
| (forall_ x p) := forall_ x (formula.sub_var_term p)
| (exists_ x p) := exists_ x (formula.sub_var_term p)

def formula.sub_var_term_is_def (s : instantiation) : formula → Prop
| bottom := true
| top := true
| (pred _ _ _) := true
| (eq u v) := true
| (not p) := formula.sub_var_term_is_def p
| (and p q) := formula.sub_var_term_is_def p ∧ formula.sub_var_term_is_def q
| (or p q) := formula.sub_var_term_is_def p ∧ formula.sub_var_term_is_def q
| (imp p q) := formula.sub_var_term_is_def p ∧ formula.sub_var_term_is_def q
| (iff p q) := formula.sub_var_term_is_def p ∧ formula.sub_var_term_is_def q
| (forall_ x p) := s x = var x ∧
    formula.sub_var_term_is_def p ∧
      ∀ y ∈ p.free_var_set \ {x}, x ∉ (s y).all_var_set
| (exists_ x p) := s x = var x ∧
    formula.sub_var_term_is_def p ∧
      ∀ y ∈ p.free_var_set \ {x}, x ∉ (s y).all_var_set


example
  (p : formula)
  (s : instantiation)
  (h1 : formula.sub_var_term_is_def s p) :
  (formula.sub_var_term s p).free_var_set =
    finset.bUnion p.free_var_set (fun y : var_symbols, (s y).all_var_set) :=
begin
  induction p generalizing s,
  case formula.bottom {
    calc
          (formula.sub_var_term s bottom).free_var_set
        = bottom.free_var_set : by unfold formula.sub_var_term
    ... = ∅ : by unfold formula.free_var_set
    ... = finset.bUnion ∅ (fun y : var_symbols, (s y).all_var_set) :
          by simp only [finset.bUnion_empty]
    ... = finset.bUnion bottom.free_var_set (fun y : var_symbols, (s y).all_var_set) :
          by unfold formula.free_var_set
  },
  case formula.top {
    calc
          (formula.sub_var_term s top).free_var_set
        = top.free_var_set : by unfold formula.sub_var_term
    ... = ∅ : by unfold formula.free_var_set
    ... = finset.bUnion ∅ (fun y : var_symbols, (s y).all_var_set) :
          by simp only [finset.bUnion_empty]
    ... = finset.bUnion top.free_var_set
            (fun y : var_symbols, (s y).all_var_set) :
          by unfold formula.free_var_set
  },
  case formula.pred : n x terms {
    calc
          (formula.sub_var_term s (pred n x terms)).free_var_set
        = (pred n x
            (fun i : fin n, term.sub_var_term s (terms i))).free_var_set :
          by unfold formula.sub_var_term
    ... = finset.bUnion finset.univ
          (fun i : fin n, (term.sub_var_term s (terms i)).all_var_set) :
          by unfold formula.free_var_set
    ... = finset.bUnion finset.univ
          (fun i : fin n,
            (finset.bUnion
              (terms i).all_var_set
              (fun y : var_symbols, (s y).all_var_set))) :
          begin congr, funext, apply thm_4 end
    ... = finset.bUnion
            (finset.bUnion finset.univ (fun i : fin n, (terms i).all_var_set))
            (fun y : var_symbols, (s y).all_var_set) :
          begin symmetry, apply finset.bUnion_bUnion end
    ... = finset.bUnion
            (pred n x terms).free_var_set
            (fun y : var_symbols, (s y).all_var_set) :
          by unfold formula.free_var_set
  },
  case formula.eq : u v {
    unfold formula.sub_var_term,
    unfold formula.free_var_set,
    rewrite finset.bUnion_union,
    rewrite thm_4, rewrite thm_4,
  },
  case formula.not : p ih {
    calc
          (formula.sub_var_term s (not p)).free_var_set
        = (not (formula.sub_var_term s p)).free_var_set :
          by unfold formula.sub_var_term
    ... = (formula.sub_var_term s p).free_var_set :
          by unfold formula.free_var_set
    ... = finset.bUnion p.free_var_set (fun y : var_symbols, (s y).all_var_set) :
          begin unfold formula.sub_var_term_is_def at h1, exact ih s h1 end
    ... = finset.bUnion (not p).free_var_set (fun y : var_symbols, (s y).all_var_set) :
          by unfold formula.free_var_set
  },
  case formula.and : p q ih_p ih_q {
    calc
          (formula.sub_var_term s (and p q)).free_var_set
        = (and
            (formula.sub_var_term s p)
            (formula.sub_var_term s q)).free_var_set :
            by unfold formula.sub_var_term
    ... = (formula.sub_var_term s p).free_var_set ∪
            (formula.sub_var_term s q).free_var_set :
            by unfold formula.free_var_set
    ... = finset.bUnion p.free_var_set (fun y : var_symbols, (s y).all_var_set) ∪
            finset.bUnion q.free_var_set (fun y : var_symbols, (s y).all_var_set) :
          begin
            unfold formula.sub_var_term_is_def at h1, cases h1,
            congr, exact ih_p s h1_left, exact ih_q s h1_right,
          end
    ... = finset.bUnion
            (p.free_var_set ∪ q.free_var_set)
            (fun y : var_symbols, (s y).all_var_set) :
            by simp [finset.bUnion_union, finset.union_comm]
    ... = finset.bUnion (and p q).free_var_set (fun y : var_symbols, (s y).all_var_set) : by unfold formula.free_var_set
  },
  case formula.or : p q ih_p ih_q {
    calc
          (formula.sub_var_term s (or p q)).free_var_set
        = (or (formula.sub_var_term s p) (formula.sub_var_term s q)).free_var_set : by unfold formula.sub_var_term
    ... = (formula.sub_var_term s p).free_var_set ∪ (formula.sub_var_term s q).free_var_set : by unfold formula.free_var_set
    ... = finset.bUnion p.free_var_set (fun y : var_symbols, (s y).all_var_set) ∪
            finset.bUnion q.free_var_set (fun y : var_symbols, (s y).all_var_set) :
          begin
            unfold formula.sub_var_term_is_def at h1, cases h1,
            congr, exact ih_p s h1_left, exact ih_q s h1_right,
          end
    ... = finset.bUnion (p.free_var_set ∪ q.free_var_set) (fun y : var_symbols, (s y).all_var_set) : by simp [finset.bUnion_union, finset.union_comm]
    ... = finset.bUnion (or p q).free_var_set (fun y : var_symbols, (s y).all_var_set) : by unfold formula.free_var_set
  },
  case formula.imp : p q ih_p ih_q {
    calc
          (formula.sub_var_term s (imp p q)).free_var_set
        = (imp (formula.sub_var_term s p) (formula.sub_var_term s q)).free_var_set : by unfold formula.sub_var_term
    ... = (formula.sub_var_term s p).free_var_set ∪ (formula.sub_var_term s q).free_var_set : by unfold formula.free_var_set
    ... = finset.bUnion p.free_var_set (fun y : var_symbols, (s y).all_var_set) ∪
            finset.bUnion q.free_var_set (fun y : var_symbols, (s y).all_var_set) :
          begin
            unfold formula.sub_var_term_is_def at h1, cases h1,
            congr, exact ih_p s h1_left, exact ih_q s h1_right,
          end
    ... = finset.bUnion (p.free_var_set ∪ q.free_var_set) (fun y : var_symbols, (s y).all_var_set) : by simp [finset.bUnion_union, finset.union_comm]
    ... = finset.bUnion (imp p q).free_var_set (fun y : var_symbols, (s y).all_var_set) : by unfold formula.free_var_set
  },
  case formula.iff : p q ih_p ih_q {
    calc
          (formula.sub_var_term s (iff p q)).free_var_set
        = (iff (formula.sub_var_term s p) (formula.sub_var_term s q)).free_var_set : by unfold formula.sub_var_term
    ... = (formula.sub_var_term s p).free_var_set ∪ (formula.sub_var_term s q).free_var_set : by unfold formula.free_var_set
    ... = finset.bUnion p.free_var_set (fun y : var_symbols, (s y).all_var_set) ∪
            finset.bUnion q.free_var_set (fun y : var_symbols, (s y).all_var_set) :
          begin
            unfold formula.sub_var_term_is_def at h1, cases h1,
            congr, exact ih_p s h1_left, exact ih_q s h1_right,
          end
    ... = finset.bUnion (p.free_var_set ∪ q.free_var_set) (fun y : var_symbols, (s y).all_var_set) : by simp [finset.bUnion_union, finset.union_comm]
    ... = finset.bUnion (iff p q).free_var_set (fun y : var_symbols, (s y).all_var_set) : by unfold formula.free_var_set
  },
  case formula.forall_ : x p ih {
    unfold formula.sub_var_term_is_def at h1, cases h1, cases h1_right,
    calc
          (formula.sub_var_term s (forall_ x p)).free_var_set
        = (forall_ x (formula.sub_var_term s p)).free_var_set :
            by unfold formula.sub_var_term
    ... = (formula.sub_var_term s p).free_var_set \ {x} :
            by unfold formula.free_var_set
    ... = (finset.bUnion p.free_var_set (fun y : var_symbols, (s y).all_var_set)) \ {x} : by rewrite ih s h1_right_left
    ... = (finset.bUnion (p.free_var_set \ {x}) (fun (y : var_symbols), (s y).all_var_set)) \ {x} :
            begin symmetry, apply finset.sdiff_singleton_bUnion, rewrite h1_left, unfold term.all_var_set end
    ... = finset.bUnion (p.free_var_set \ {x}) (fun (y : var_symbols), (s y).all_var_set) :
            begin
              apply finset.bUnion_sdiff_of_forall_disjoint,
              simp only [finset.disjoint_singleton_right], apply h1_right_right
            end
    ... = finset.bUnion (forall_ x p).free_var_set (fun y : var_symbols, (s y).all_var_set) : by unfold formula.free_var_set
  },
  case formula.exists_ : x p ih {
    unfold formula.sub_var_term_is_def at h1, cases h1, cases h1_right,
    calc
          (formula.sub_var_term s (exists_ x p)).free_var_set
        = (exists_ x (formula.sub_var_term s p)).free_var_set :
            by unfold formula.sub_var_term
    ... = (formula.sub_var_term s p).free_var_set \ {x} :
            by unfold formula.free_var_set
    ... = (finset.bUnion p.free_var_set (fun y : var_symbols, (s y).all_var_set)) \ {x} : by rewrite ih s h1_right_left
    ... = (finset.bUnion (p.free_var_set \ {x}) (fun (y : var_symbols), (s y).all_var_set)) \ {x} :
            begin symmetry, apply finset.sdiff_singleton_bUnion, rewrite h1_left, unfold term.all_var_set end
    ... = finset.bUnion (p.free_var_set \ {x}) (fun (y : var_symbols), (s y).all_var_set) :
            begin
              apply finset.bUnion_sdiff_of_forall_disjoint,
              simp only [finset.disjoint_singleton_right], apply h1_right_right
            end
    ... = finset.bUnion (exists_ x p).free_var_set (fun y : var_symbols, (s y).all_var_set) : by unfold formula.free_var_set
  }
end


theorem thm_6
  {D : Type}
  {m : interpretation D}
  (v : valuation D)
  (s : instantiation)
  (p : formula)
  (h1 : formula.sub_var_term_is_def s p) :
  holds D m v (formula.sub_var_term s p) ↔ holds D m ((eval_term D m v) ∘ s) p :=
begin
  induction p generalizing s v,
  case formula.bottom {
    calc
    holds D m v (formula.sub_var_term s bottom) ↔
      holds D m v bottom : by unfold formula.sub_var_term
    ... ↔ false : by unfold holds
    ... ↔ holds D m (eval_term D m v ∘ s) bottom : by unfold holds
  },
  case formula.top {
    calc
    holds D m v (formula.sub_var_term s top) ↔
      holds D m v top : by unfold formula.sub_var_term
    ... ↔ true : by unfold holds
    ... ↔ holds D m (eval_term D m v ∘ s) top : by unfold holds
  },
  case formula.pred : n x terms {
    calc
    holds D m v (formula.sub_var_term s (pred n x terms)) ↔
      holds D m v (pred n x (fun i : fin n, term.sub_var_term s (terms i))) : by unfold formula.sub_var_term
    ... ↔ m.pred n x (fun i : fin n, eval_term D m v (term.sub_var_term s (terms i))) : by unfold holds
    ... ↔ m.pred n x (fun i : fin n, eval_term D m ((eval_term D m v) ∘ s) (terms i)) : by simp only [thm_5]
    ... ↔ holds D m ((eval_term D m v) ∘ s) (pred n x terms) : by unfold holds
  },
  case formula.eq : u v {
    unfold formula.sub_var_term,
    unfold holds,
    simp only [thm_5],
  },
  case formula.not : p ih {
    calc
    holds D m v (formula.sub_var_term s (not p)) ↔ holds D m v (not (formula.sub_var_term s p)) : by unfold formula.sub_var_term
    ... ↔ ¬ holds D m v (formula.sub_var_term s p) : by unfold holds
    ... ↔ ¬ holds D m ((eval_term D m v) ∘ s) p : begin unfold formula.sub_var_term_is_def at h1, rewrite ih s v h1 end
    ... ↔ holds D m ((eval_term D m v) ∘ s) (not p) : by unfold holds
  },
  case formula.and : p q ih_p ih_q {
    calc
    holds D m v (formula.sub_var_term s (and p q)) ↔ holds D m v (and (formula.sub_var_term s p) (formula.sub_var_term s q)) : by unfold formula.sub_var_term
    ... ↔ (holds D m v (formula.sub_var_term s p)) ∧ (holds D m v (formula.sub_var_term s q)) : by unfold holds
    ... ↔ (holds D m ((eval_term D m v) ∘ s) p) ∧ (holds D m ((eval_term D m v) ∘ s) q) :
        begin unfold formula.sub_var_term_is_def at h1, cases h1, rewrite ih_p s v h1_left, rewrite ih_q s v h1_right end
    ... ↔ holds D m ((eval_term D m v) ∘ s) (and p q) : by unfold holds
  },
  case formula.or : p q ih_p ih_q {
    calc
    holds D m v (formula.sub_var_term s (or p q)) ↔ holds D m v (or (formula.sub_var_term s p) (formula.sub_var_term s q)) : by unfold formula.sub_var_term
    ... ↔ (holds D m v (formula.sub_var_term s p)) ∨ (holds D m v (formula.sub_var_term s q)) : by unfold holds
    ... ↔ (holds D m ((eval_term D m v) ∘ s) p) ∨ (holds D m ((eval_term D m v) ∘ s) q) :
        begin unfold formula.sub_var_term_is_def at h1, cases h1, rewrite ih_p s v h1_left, rewrite ih_q s v h1_right end
    ... ↔ holds D m ((eval_term D m v) ∘ s) (or p q) : by unfold holds
  },
  case formula.imp : p q ih_p ih_q {
    calc
    holds D m v (formula.sub_var_term s (imp p q)) ↔ holds D m v (imp (formula.sub_var_term s p) (formula.sub_var_term s q)) : by unfold formula.sub_var_term
    ... ↔ (holds D m v (formula.sub_var_term s p)) → (holds D m v (formula.sub_var_term s q)) : by unfold holds
    ... ↔ (holds D m ((eval_term D m v) ∘ s) p) → (holds D m ((eval_term D m v) ∘ s) q) :
        begin unfold formula.sub_var_term_is_def at h1, cases h1, rewrite ih_p s v h1_left, rewrite ih_q s v h1_right end
    ... ↔ holds D m ((eval_term D m v) ∘ s) (imp p q) : by unfold holds
  },
  case formula.iff : p q ih_p ih_q {
    calc
    holds D m v (formula.sub_var_term s (iff p q)) ↔ holds D m v (iff (formula.sub_var_term s p) (formula.sub_var_term s q)) : by unfold formula.sub_var_term
    ... ↔ ((holds D m v (formula.sub_var_term s p)) ↔ (holds D m v (formula.sub_var_term s q))) : by unfold holds
    ... ↔ ((holds D m ((eval_term D m v) ∘ s) p) ↔ (holds D m ((eval_term D m v) ∘ s) q)) :
        begin unfold formula.sub_var_term_is_def at h1, cases h1, rewrite ih_p s v h1_left, rewrite ih_q s v h1_right end
    ... ↔ holds D m ((eval_term D m v) ∘ s) (iff p q) : by unfold holds
  },
  case formula.forall_ : x p ih {
    begin
      unfold formula.sub_var_term_is_def at h1, cases h1, cases h1_right,
      calc
            holds D m v (formula.sub_var_term s (forall_ x p))
          ↔ holds D m v (forall_ x (formula.sub_var_term s p)) : by unfold formula.sub_var_term
      ... ↔ (∀ a : D, holds D m (function.update v x a) (formula.sub_var_term s p)) : by unfold holds
      ... ↔ (∀ a : D, holds D m (eval_term D m (function.update v x a) ∘ s) p) :
            begin
              apply forall_congr, intros a,
              exact ih s (function.update v x a) h1_right_left
            end
      ... ↔ (∀ a : D, holds D m (function.update (eval_term D m v ∘ s) x a) p) :
            begin
              apply forall_congr, intro a,
              apply thm_2, intros z h2,
              by_cases z = x,
              {
                calc
                      (eval_term D m (function.update v x a) ∘ s) z
                    = (eval_term D m (function.update v x a) ∘ s) x : by rewrite h
                ... = eval_term D m (function.update v x a) (s x) : by unfold function.comp
                ... = eval_term D m (function.update v x a) (var x) : by rewrite h1_left
                ... = (function.update v x a) x : by unfold eval_term
                ... = a : by simp only [function.update_same]
                ... = (function.update (eval_term D m v ∘ s) x a) x : by simp only [function.update_same]
                ... = (function.update (eval_term D m v ∘ s) x a) z : by rewrite h
              },
              {
                calc
                      (eval_term D m (function.update v x a) ∘ s) z
                    = eval_term D m (function.update v x a) (s z) : by unfold function.comp
                ... = eval_term D m v (s z) :
                      begin
                        apply thm_1, intros y h3,
                        apply function.update_noteq, intros h4, apply h1_right_right z,
                        simp only [finset.mem_sdiff, finset.mem_singleton], exact and.intro h2 h,
                        rewrite h4 at h3, exact h3
                      end
                ... = (eval_term D m v ∘ s) z : by unfold function.comp
                ... = (function.update (eval_term D m v ∘ s) x a) z : by simp only [function.update_noteq h]
              }
            end
      ... ↔ holds D m (eval_term D m v ∘ s) (forall_ x p) : by unfold holds
    end
  },
  case formula.exists_ : x p ih {
    begin
      unfold formula.sub_var_term_is_def at h1, cases h1, cases h1_right,
      calc
            holds D m v (formula.sub_var_term s (exists_ x p))
          ↔ holds D m v (exists_ x (formula.sub_var_term s p)) : by unfold formula.sub_var_term
      ... ↔ (∃ a : D, holds D m (function.update v x a) (formula.sub_var_term s p)) : by unfold holds
      ... ↔ (∃ a : D, holds D m (eval_term D m (function.update v x a) ∘ s) p) :
            begin
              apply exists_congr, intro a,
              exact ih s (function.update v x a) h1_right_left
            end
      ... ↔ (∃ a : D, holds D m (function.update (eval_term D m v ∘ s) x a) p) :
            begin
              apply exists_congr, intros a,
              apply thm_2, intros z h2,
              by_cases z = x,
              {
                calc
                      (eval_term D m (function.update v x a) ∘ s) z
                    = (eval_term D m (function.update v x a) ∘ s) x : by rewrite h
                ... = eval_term D m (function.update v x a) (s x) : by unfold function.comp
                ... = eval_term D m (function.update v x a) (var x) : by rewrite h1_left
                ... = (function.update v x a) x : by unfold eval_term
                ... = a : by simp only [function.update_same]
                ... = (function.update (eval_term D m v ∘ s) x a) x : by simp only [function.update_same]
                ... = (function.update (eval_term D m v ∘ s) x a) z : by rewrite h
              },
              {
                calc
                      (eval_term D m (function.update v x a) ∘ s) z
                    = eval_term D m (function.update v x a) (s z) : by unfold function.comp
                ... = eval_term D m v (s z) :
                      begin
                        apply thm_1, intros y h3,
                        apply function.update_noteq, intros h4, apply h1_right_right z,
                        simp only [finset.mem_sdiff, finset.mem_singleton], exact and.intro h2 h,
                        rewrite h4 at h3, exact h3
                      end
                ... = (eval_term D m v ∘ s) z : by unfold function.comp
                ... = (function.update (eval_term D m v ∘ s) x a) z : by simp only [function.update_noteq h]
              }
            end
      ... ↔ holds D m (eval_term D m v ∘ s) (exists_ x p) : by unfold holds
    end
  }
end


theorem valid_imp_sub_var_term_valid
  (p : formula)
  (s : instantiation)
  (h1 : formula.sub_var_term_is_def s p)
  (h2 : is_valid p) :
  is_valid (formula.sub_var_term s p) :=
begin
  unfold is_valid at *,
  intros D m v,
  simp only [thm_6 v s p h1], apply h2
end


-- uniform simultaneous replacement of the atoms in a formula by formulas

def formula.sub_atom_formula (s : (ℕ × string) → formula) : formula → formula
| bottom := bottom
| top := top
| (pred n x terms) := s (n, x)
| (eq u v) := eq u v
| (not p) := not (formula.sub_atom_formula p)
| (and p q) := and (formula.sub_atom_formula p) (formula.sub_atom_formula q)
| (or p q) := or (formula.sub_atom_formula p) (formula.sub_atom_formula q)
| (imp p q) := imp (formula.sub_atom_formula p) (formula.sub_atom_formula q)
| (iff p q) := iff (formula.sub_atom_formula p) (formula.sub_atom_formula q)
| (forall_ x p) := forall_ x (formula.sub_atom_formula p)
| (exists_ x p) := exists_ x (formula.sub_atom_formula p)

def formula.sub_atom_formula_is_def (s : (ℕ × string) → formula) : formula → Prop
| bottom := true
| top := true
| (pred _ _ _) := true
| (eq u v) := true
| (not p) := formula.sub_atom_formula_is_def p
| (and p q) := formula.sub_atom_formula_is_def p ∧
    formula.sub_atom_formula_is_def q
| (or p q) := formula.sub_atom_formula_is_def p ∧
    formula.sub_atom_formula_is_def q
| (imp p q) := formula.sub_atom_formula_is_def p ∧
    formula.sub_atom_formula_is_def q
| (iff p q) := formula.sub_atom_formula_is_def p ∧
    formula.sub_atom_formula_is_def q
| (forall_ x p) := formula.sub_atom_formula_is_def p ∧
    ∀ y ∈ p.all_pred_set, x ∉ (s y).free_var_set
| (exists_ x p) := formula.sub_atom_formula_is_def p ∧
    ∀ y ∈ p.all_pred_set, x ∉ (s y).free_var_set

def interpretation.sub
  {D : Type}
  (m : interpretation D)
  (v : valuation D)
  (f : (ℕ × string) → formula) : interpretation D :=
    interpretation.mk m.nonempty m.func
      (fun n : ℕ, fun x : string, fun terms : fin n → D, holds D m v (f (n, x)))

lemma formula.sub_atom_formula_holds
  (D : Type)
  (m : interpretation D)
  (v v' : valuation D)
  (p : formula)
  (s : (ℕ × string) → formula)
  (hv : ∀ (y ∈ p.all_pred_set) (x ∈ (s y).free_var_set), v x = v' x)
  (h1 : formula.sub_atom_formula_is_def s p) :
  holds D m v (formula.sub_atom_formula s p)
    ↔ holds D (m.sub v' s) v p :=
begin
  induction p generalizing v,
  case formula.bottom : v hv
  { unfold interpretation.sub, unfold formula.sub_atom_formula, unfold holds },
  case formula.top : v hv
  { unfold interpretation.sub, unfold formula.sub_atom_formula, unfold holds },
  case formula.pred : n p terms v hv
  {
    simp only [interpretation.sub], unfold formula.sub_atom_formula, unfold holds,
    simp [formula.all_pred_set] at hv,
    apply thm_2,
    intros x h2, apply hv n p, refl, refl, exact h2
  },
  case formula.eq : t t'
  {
    simp only [interpretation.sub],
    unfold formula.sub_atom_formula,
    unfold holds, 
    admit,
  },
  case formula.not : p p_ih v hv
  {
    unfold formula.sub_atom_formula_is_def at h1,
    unfold formula.sub_atom_formula, unfold holds,
    apply not_congr, apply p_ih h1 _ hv
  },
  case formula.and : p q p_ih q_ih
  {
    unfold formula.sub_atom_formula_is_def at h1, cases h1,
    unfold formula.sub_atom_formula, unfold holds,
    simp [formula.all_pred_set, or_imp_distrib, forall_and_distrib] at hv,
    apply and_congr,
    apply p_ih h1_left,
    intros y h2 x h3, apply hv.1 y.1 y.2,
    simp only [prod.mk.eta], exact h2, simp only [prod.mk.eta], exact h3,
    apply q_ih h1_right,
    intros y h2 x h3, apply hv.2 y.1 y.2,
    simp only [prod.mk.eta], exact h2, simp only [prod.mk.eta], exact h3
  },
  case formula.or : p q p_ih q_ih
  {
    unfold formula.sub_atom_formula_is_def at h1, cases h1,
    unfold formula.sub_atom_formula, unfold holds,
    simp [formula.all_pred_set, or_imp_distrib, forall_and_distrib] at hv,
    apply or_congr,
    apply p_ih h1_left,
    intros y h2 x h3, apply hv.1 y.1 y.2,
    simp only [prod.mk.eta], exact h2, simp only [prod.mk.eta], exact h3,
    apply q_ih h1_right,
    intros y h2 x h3, apply hv.2 y.1 y.2,
    simp only [prod.mk.eta], exact h2, simp only [prod.mk.eta], exact h3
  },
  case formula.imp : p q p_ih q_ih
  {
    unfold formula.sub_atom_formula_is_def at h1, cases h1,
    unfold formula.sub_atom_formula, unfold holds,
    simp [formula.all_pred_set, or_imp_distrib, forall_and_distrib] at hv,
    apply imp_congr,
    apply p_ih h1_left,
    intros y h2 x h3, apply hv.1 y.1 y.2,
    simp only [prod.mk.eta], exact h2, simp only [prod.mk.eta], exact h3,
    apply q_ih h1_right,
    intros y h2 x h3, apply hv.2 y.1 y.2,
    simp only [prod.mk.eta], exact h2, simp only [prod.mk.eta], exact h3
  },
  case formula.iff : p q p_ih q_ih
  {
    unfold formula.sub_atom_formula_is_def at h1, cases h1,
    unfold formula.sub_atom_formula, unfold holds,
    simp [formula.all_pred_set, or_imp_distrib, forall_and_distrib] at hv,
    apply iff_congr,
    apply p_ih h1_left,
    intros y h2 x h3, apply hv.1 y.1 y.2,
    simp only [prod.mk.eta], exact h2, simp only [prod.mk.eta], exact h3,
    apply q_ih h1_right,
    intros y h2 x h3, apply hv.2 y.1 y.2,
    simp only [prod.mk.eta], exact h2, simp only [prod.mk.eta], exact h3
  },
  case formula.forall_ : y p p_ih v hv
  {
    unfold formula.sub_atom_formula_is_def at h1, cases h1,
    unfold formula.sub_atom_formula, unfold holds,
    apply forall_congr, intros a,
    refine p_ih h1_left _ (λ y hy x hx, _),
    rw [function.update_noteq], exact hv _ hy _ hx,
    rintro rfl, exact h1_right _ hy hx
  },
  case formula.exists_ : y p p_ih v hv
  {
    unfold formula.sub_atom_formula_is_def at h1, cases h1,
    unfold formula.sub_atom_formula, unfold holds,
    apply exists_congr, intros a,
    refine p_ih h1_left _ (λ y hy x hx, _),
    rw [function.update_noteq], exact hv _ hy _ hx,
    rintro rfl, exact h1_right _ hy hx
  },
end

example
  (p : formula)
  (s : (ℕ × string) → formula)
  (h1 : formula.sub_atom_formula_is_def s p)
  (h2 : is_valid p) :
  is_valid (formula.sub_atom_formula s p) :=
begin
  unfold is_valid at *,
  intros D m v,
  rewrite formula.sub_atom_formula_holds D m v v,
  apply h2,
  intros y h3 x h4, refl,
  exact h1
end


-- uniform simultaneous replacement of a single variable in a term by a term

def term.sub_single_var_term (t : term) (x : var_symbols) : term → term
| (var y) := if x = y then t else var y
| (func n f terms) := func n f (fun i : fin n, term.sub_single_var_term (terms i))

-- uniform simultaneous replacement of a single variable in a formula by a term

def formula.sub_single_var_term (t : term) (x : var_symbols) : formula → formula
| bottom := bottom
| top := top
| (pred n p terms) :=
    pred n p (fun i : fin n, term.sub_single_var_term t x (terms i))
| (eq u v) := eq (term.sub_single_var_term t x u) (term.sub_single_var_term t x v)
| (not p) := not (formula.sub_single_var_term p)
| (and p q) := and (formula.sub_single_var_term p) (formula.sub_single_var_term q)
| (or p q) := or (formula.sub_single_var_term p) (formula.sub_single_var_term q)
| (imp p q) := imp (formula.sub_single_var_term p) (formula.sub_single_var_term q)
| (iff p q) := iff (formula.sub_single_var_term p) (formula.sub_single_var_term q)
| (forall_ y p) := if x ≠ y ∧ y ∉ t.all_var_set then forall_ y (formula.sub_single_var_term p) else forall_ y p
| (exists_ y p) := if x ≠ y ∧ y ∉ t.all_var_set then exists_ y (formula.sub_single_var_term p) else exists_ y p


-- alpha equivalence

def replace_term (x y : var_symbols) (xs : finset var_symbols) : term → term
| (var x') := if x' ∉ xs ∧ x = x' then var y else var x'
| (func n f terms) := func n f (fun i : fin n, replace_term (terms i))

def replace (x y : var_symbols) : finset var_symbols → formula → formula
| xs bottom := bottom
| xs top := top
| xs (pred n p terms) := pred n p (fun i : fin n, replace_term x y xs (terms i))
| xs (eq u v) := eq (replace_term x y xs u) (replace_term x y xs v)
| xs (not p) := not (replace xs p)
| xs (and p q) := and (replace xs p) (replace xs q)
| xs (or p q) := or (replace xs p) (replace xs q)
| xs (imp p q) := imp (replace xs p) (replace xs q)
| xs (iff p q) := iff (replace xs p) (replace xs q)
| xs (forall_ x p) := forall_ x (replace (xs ∪ {x}) p)
| xs (exists_ x p) := exists_ x (replace (xs ∪ {x}) p)

inductive alpha_eqv : formula → formula → Prop
| rename_forall (p : formula) (x y : var_symbols) :
  y ∉ p.free_var_set → y ∉ p.bind_var_set → alpha_eqv (forall_ x p) (forall_ y (replace x y ∅ p))
| rename_exists (p : formula) (x y : var_symbols) :
  y ∉ p.free_var_set → y ∉ p.bind_var_set → alpha_eqv (exists_ x p) (exists_ y (replace x y ∅ p))
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
  (x y : var_symbols)
  (xs : finset var_symbols)
  (t : term)
  (h1 : x ∈ xs) :
  replace_term x y xs t = t :=
begin
  induction t,
  case term.var : z
  {
    unfold replace_term,
    by_cases x = z,
    {
      subst h,
      simp only [eq_self_iff_true, and_true, ite_not, ite_eq_left_iff],
      contradiction
    },
    {
      simp only [ite_eq_right_iff, and_imp],
      intros h2 h3,
      contradiction
    }
  },
  case term.func : n f terms ih
  {
    unfold replace_term,
    simp only at ih,
    congr, funext, exact ih i
  },
end

lemma replace_id
  (x y : var_symbols)
  (xs : finset var_symbols)
  (p : formula)
  (h1 : x ∈ xs) :
  replace x y xs p = p :=
begin
  induction p generalizing xs,
  case formula.bottom
  { unfold replace },
  case formula.top
  { unfold replace },
  case formula.pred : n p terms
  { unfold replace, congr, funext, apply replace_term_id, exact h1 },
  case formula.eq : s t
  { unfold replace, congr, apply replace_term_id, exact h1,
    apply replace_term_id, exact h1, },
  case formula.not : p p_ih
  { unfold replace, rewrite p_ih xs h1 },
  case formula.and : p q p_ih q_ih
  { unfold replace, rewrite p_ih xs h1, rewrite q_ih xs h1 },
  case formula.or : p q p_ih q_ih
  { unfold replace, rewrite p_ih xs h1, rewrite q_ih xs h1 },
  case formula.imp : p q p_ih q_ih
  { unfold replace, rewrite p_ih xs h1, rewrite q_ih xs h1 },
  case formula.iff : p q p_ih q_ih
  { unfold replace, rewrite p_ih xs h1, rewrite q_ih xs h1 },
  case formula.forall_ : z p p_ih
  {
    unfold replace, rewrite p_ih, simp only [finset.mem_union, finset.mem_singleton],
    apply or.intro_left, exact h1,
  },
  case formula.exists_ : x p p_ih
  {
    unfold replace, rewrite p_ih, simp only [finset.mem_union, finset.mem_singleton],
    apply or.intro_left, exact h1
  },
end

lemma eval_replace_term
  (D : Type)
  (m : interpretation D)
  (v : valuation D)
  (a : D)
  (x y : var_symbols)
  (xs : finset var_symbols)
  (t : term)
  (h1 : x ∉ xs)
  (h2 : y ∉ t.all_var_set) :
  eval_term D m (function.update v x a) t =
    eval_term D m (function.update v y a) (replace_term x y xs t) :=
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
      have s1 : ¬ (z ∉ xs ∧ x = z), push_neg, intro, exact h,
      simp only [if_neg s1], unfold eval_term,
      rewrite <- ne.def at h2, rewrite ne_comm at h2,
      rewrite <- ne.def at h, rewrite ne_comm at h,
      simp only [function.update_noteq h2, function.update_noteq h]
    }
  },
  case term.func : n f terms ih
  {
    unfold term.all_var_set at h2,
    simp only [finset.mem_bUnion, finset.mem_univ, exists_true_left, not_exists] at h2,
    unfold replace_term, unfold eval_term, congr, funext,
    simp only at ih, apply ih, apply h2
  },
end

lemma replace_sdiff_singleton_term
  (x y z : var_symbols)
  (xs : finset var_symbols)
  (t : term)
  (h1 : x ∉ xs) :
  replace_term x y xs t = replace_term x y (xs \ {z}) t :=
begin
  induction t,
  case term.var : u
  {
    unfold replace_term,
    by_cases x = u,
    {
      have s1 : u ∉ xs ∧ x = u, rewrite <- h, split, exact h1, refl,
      have s2 : u ∉ xs \ {z} ∧ x = u, subst h, split,
      apply finset.not_mem_sdiff_of_not_mem_left h1, refl,
      simp only [if_pos s1, if_pos s2]
    },
    {
      have s1 : ¬ (u ∉ xs ∧ x = u), push_neg, intro, exact h,
      have s2 : ¬ (u ∉ xs \ {z} ∧ x = u), push_neg, intro, exact h,
      simp only [if_neg s1, if_neg s2]
    }
  },
  case term.func : n f terms ih
  {
    unfold replace_term, congr, funext, simp only at ih, apply ih
  },
end

lemma replace_sdiff_singleton
  (x y z : var_symbols)
  (p : formula)
  (xs : finset var_symbols)
  (h1 : x ∉ xs) :
  replace x y xs p = replace x y (xs \ {z}) p :=
begin
  induction p generalizing xs,
  case formula.bottom
  { unfold replace },
  case formula.top
  { unfold replace },
  case formula.pred : n p terms
  {
    unfold replace, congr, funext,
    apply replace_sdiff_singleton_term, exact h1
  },
  case formula.eq : s t
  {
    unfold replace, congr' 1,
    apply replace_sdiff_singleton_term, exact h1,
    apply replace_sdiff_singleton_term, exact h1,
  },
  case formula.not : p p_ih
  {
    unfold replace, rewrite p_ih xs h1,
  },
  case formula.and : p q p_ih q_ih
  {
    unfold replace,
    rewrite p_ih xs h1, rewrite q_ih xs h1,
  },
  case formula.or : p q p_ih q_ih
  {
    unfold replace,
    rewrite p_ih xs h1, rewrite q_ih xs h1,
  },
  case formula.imp : p q p_ih q_ih
  {
    unfold replace,
    rewrite p_ih xs h1, rewrite q_ih xs h1,
  },
  case formula.iff : p q p_ih q_ih
  {
    unfold replace,
    rewrite p_ih xs h1, rewrite q_ih xs h1,
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
        have s1 : x ∈ xs ∪ {u}, simp only [finset.mem_union, finset.mem_singleton], apply or.intro_right, exact h',
        have s2 : x ∈ xs \ {z} ∪ {u}, simp only [finset.mem_union, finset.mem_sdiff, finset.mem_singleton],
          apply or.intro_right, exact h',
        rewrite replace_id x y (xs ∪ {u}) p s1,
        rewrite replace_id x y ((xs \ {z}) ∪ {u}) p s2
      },
      {
        have s1 : ((xs \ {z}) ∪ {u}) = (xs ∪ {u}) \ {z}, exact finset.ne_imp_sdiff_union_comm z u xs h,
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
        have s1 : x ∈ xs ∪ {u}, simp only [finset.mem_union, finset.mem_singleton], apply or.intro_right, exact h',
        have s2 : x ∈ xs \ {z} ∪ {u}, simp only [finset.mem_union, finset.mem_sdiff, finset.mem_singleton],
          apply or.intro_right, exact h',
        rewrite replace_id x y (xs ∪ {u}) p s1,
        rewrite replace_id x y ((xs \ {z}) ∪ {u}) p s2
      },
      {
        have s1 : ((xs \ {z}) ∪ {u}) = (xs ∪ {u}) \ {z}, exact finset.ne_imp_sdiff_union_comm z u xs h,
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
  case formula.pred : n p terms
  {
    unfold replace, unfold holds,
    unfold formula.free_var_set at h1, simp at h1,
    apply iff_of_eq, congr, funext, apply eval_replace_term,
    simp only [finset.not_mem_empty, not_false_iff], exact h1 i
  },
  case formula.eq : s t {
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
    have s1 : y ∉ p.free_var_set, exact finset.not_mem_sdiff_ne_imp_not_mem h1 h2_right,
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
    have s1 : y ∉ p.free_var_set, exact finset.not_mem_sdiff_ne_imp_not_mem h1 h2_right,
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
| m (func n p terms) (func n' p' terms') :=
    if h : n = n'
    then begin subst h; exact ∀ i, is_alpha_eqv_term m (terms i) (terms' i) end
    else false
| _ _ _ := false

def is_alpha_eqv : list (var_symbols × var_symbols) → formula → formula → Prop
| m bottom bottom := true
| m top top := true
| m (pred n p terms) (pred n' p' terms') :=
  if h : n = n'
  then begin subst h; exact ∀ i, is_alpha_eqv_term m (terms i) (terms' i) end
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
  (t : term)
  (h1 : formula.sub_var_term_is_def (sub_single_var x t) p) :
  is_valid ((forall_ x p).imp (formula.sub_var_term (sub_single_var x t) p)) :=
begin
  unfold is_valid, unfold holds,
  intros D m v h2,
  rewrite thm_6 v (sub_single_var x t) p h1,
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
  rewrite @thm_2 D m p (function.update v x a) v s1, exact h2
end


def variant : var_symbols → finset var_symbols → var_symbols
| x vars :=
if h : x ∈ vars
then vars.max' (exists.intro x h) + 1
else x

lemma variant_not_mem
  (x : var_symbols)
  (s : finset var_symbols) :
  variant x s ∉ s :=
begin
  unfold variant, split_ifs,
  {
    intro con,
    have s1 : s.max' _ + 1 ≤ s.max' _, exact finset.le_max' s (s.max' _ + 1) con,
    have s2 : ¬ s.max' _ < s.max' _ + 1, exact s1.not_lt,
    apply s2, apply nat.lt_succ_self
  },
  { assumption }
end


def sub_formula : instantiation → formula → formula
| _ bottom := bottom
| _ top := top
| s (pred n x terms) := pred n x (fun i : fin n, term.sub_var_term s (terms i))
| s (eq u v) := eq (term.sub_var_term s u) (term.sub_var_term s v)
| s (not p) := not (sub_formula s p)
| s (and p q) := and (sub_formula s p) (sub_formula s q)
| s (or p q) := or (sub_formula s p) (sub_formula s q)
| s (imp p q) := imp (sub_formula s p) (sub_formula s q)
| s (iff p q) := iff (sub_formula s p) (sub_formula s q)
| s (forall_ x p) :=
  let x' :=
    if ∃ y ∈ p.free_var_set \ {x}, x ∈ (s y).all_var_set
    then variant x (sub_formula (function.update s x (var x)) p).free_var_set
    else x
  in forall_ x' (sub_formula (function.update s x (var x')) p)
| s (exists_ x p) :=
  let x' :=
    if ∃ y ∈ p.free_var_set \ {x}, x ∈ (s y).all_var_set
    then variant x (sub_formula (function.update s x (var x)) p).free_var_set
    else x
  in exists_ x' (sub_formula (function.update s x (var x')) p)


lemma lem_3_6_1
  (x : var_symbols)
  (p : formula)
  (s : instantiation)
  (h1 : ∀ s : instantiation, (sub_formula s p).free_var_set =
    finset.bUnion p.free_var_set (fun y : var_symbols, (s y).all_var_set)) :
  let x' :=
      if ∃ y ∈ p.free_var_set \ {x}, x ∈ (s y).all_var_set
      then variant x (sub_formula (function.update s x (var x)) p).free_var_set
      else x
  in
  x' ∉ finset.bUnion (p.free_var_set \ {x}) (fun y : var_symbols, (s y).all_var_set) :=
begin
  intro x',
  by_cases x ∈ finset.bUnion (p.free_var_set \ {x}) (fun y : var_symbols, (s y).all_var_set),
  {
    have s1 : finset.bUnion (p.free_var_set \ {x}) (fun y : var_symbols, (s y).all_var_set) ⊆
      (sub_formula (function.update s x (var x)) p).free_var_set,
      calc
      finset.bUnion (p.free_var_set \ {x}) (fun y : var_symbols, (s y).all_var_set) =
        finset.bUnion (p.free_var_set \ {x}) (fun y : var_symbols, ((function.update s x (var x)) y).all_var_set) :
          begin
            symmetry, apply finset.bUnion_congr, refl, intros a h1, congr,
            simp only [finset.mem_sdiff, finset.mem_singleton] at h1, cases h1,
            exact function.update_noteq h1_right (var x) s
          end
      ... ⊆ finset.bUnion p.free_var_set (fun y : var_symbols, ((function.update s x (var x)) y).all_var_set) : 
          begin apply finset.bUnion_subset_bUnion_of_subset_left, apply finset.sdiff_subset end
      ... = (sub_formula (function.update s x (var x)) p).free_var_set :
          begin symmetry, exact h1 (function.update s x (var x)) end,
    have s2 : x' = variant x (sub_formula (function.update s x (var x)) p).free_var_set, simp only [finset.mem_bUnion] at h, exact if_pos h,
    have s3 : x' ∉ (sub_formula (function.update s x (var x)) p).free_var_set, rewrite s2, apply variant_not_mem,
    exact finset.not_mem_mono s1 s3
  },
  {
    have s1 : x' = x, simp only [finset.mem_bUnion] at h, exact if_neg h,
    rewrite s1, exact h
  }
end

lemma finset_bUnion_singleton_union
  {T : Type} [decidable_eq T]
  (x : T)
  (S : finset T)
  (f : T → finset T) :
  finset.bUnion ({x} ∪ S) f = (finset.bUnion S f) ∪ f x :=
begin
  ext, simp only [finset.mem_bUnion, finset.mem_union, finset.mem_singleton, exists_prop],
  split, finish, finish,
end

lemma finset_bUnion_sdiff
  {T : Type} [decidable_eq T]
  (x x' : T)
  (S : finset T)
  (f : T → finset T)
  (h1 : f x = {x'}) :
  (finset.bUnion S f) \ {x'} = (finset.bUnion (S \ {x}) f) \ {x'} :=
begin
  by_cases x ∈ S,
  {
    calc
          (finset.bUnion S f) \ {x'}
        = finset.bUnion S (fun i : T, f i \ {x'}) :
          by simp only [finset.sdiff_singleton_eq_erase, finset.erase_bUnion]
    ... = finset.bUnion ({x} ∪ (S \ {x})) (fun i : T, f i \ {x'}) :
          begin
            congr, symmetry, apply finset.union_sdiff_of_subset,
            simp only [finset.singleton_subset_iff], exact h
          end
    ... = (finset.bUnion (S \ {x}) (fun i : T, f i \ {x'})) ∪ (fun i : T, f i \ {x'}) x :
          by simp only [finset_bUnion_singleton_union]
    ...  = (finset.bUnion (S \ {x}) (fun i : T, f i \ {x'})) :
          begin
            simp only, rewrite h1, rewrite sdiff_self, apply finset.union_empty
          end
    ... = (finset.bUnion (S \ {x}) (fun i : T, f i)) \ {x'} :
          by simp only [finset.sdiff_singleton_eq_erase, finset.erase_bUnion]
    ... = (finset.bUnion (S \ {x}) f) \ {x'} : by simp only
  },
  {
    congr, symmetry, exact finset.sdiff_singleton_not_mem_eq_self S h,
  }
end

lemma lem_3_6
  (p : formula)
  (s : instantiation) :
  (sub_formula s p).free_var_set = finset.bUnion p.free_var_set (fun y : var_symbols, (s y).all_var_set) :=
begin
  induction p generalizing s,
  case formula.bottom {
    unfold sub_formula, unfold formula.free_var_set, simp only [finset.bUnion_empty]
  },
  case formula.top {
    unfold sub_formula, unfold formula.free_var_set, simp only [finset.bUnion_empty]
  },
  case formula.pred : n x terms {
    calc
    (sub_formula s (pred n x terms)).free_var_set = (pred n x (fun i : fin n, term.sub_var_term s (terms i))).free_var_set : by unfold sub_formula
    ... = finset.bUnion finset.univ (fun i : fin n, (term.sub_var_term s (terms i)).all_var_set) : by unfold formula.free_var_set
    ... = finset.bUnion finset.univ (fun i : fin n, (finset.bUnion (terms i).all_var_set (fun y : var_symbols, (s y).all_var_set))) :
        by simp only [thm_4]
    ... = finset.bUnion (finset.bUnion finset.univ (fun i : fin n, (terms i).all_var_set)) (fun y : var_symbols, (s y).all_var_set) :
        begin ext1, simp only [finset.mem_bUnion, finset.mem_univ, exists_prop, exists_true_left], tauto end
    ... = finset.bUnion (pred n x terms).free_var_set (fun y : var_symbols, (s y).all_var_set) : by unfold formula.free_var_set
  },
  case formula.eq : u v {
    unfold sub_formula, unfold formula.free_var_set, simp only [thm_4],
    simp only [finset.bUnion_union],    
  },
  case formula.not : p ih {
    calc
    (sub_formula s (not p)).free_var_set = (not (sub_formula s p)).free_var_set : by unfold sub_formula
    ... = (sub_formula s p).free_var_set : by unfold formula.free_var_set
    ... = finset.bUnion p.free_var_set (fun y : var_symbols, (s y).all_var_set) : ih s
    ... = finset.bUnion (not p).free_var_set (fun y : var_symbols, (s y).all_var_set) : by unfold formula.free_var_set
  },
  case formula.and : p q ih_p ih_q {
    calc
    (sub_formula s (and p q)).free_var_set = (and (sub_formula s p) (sub_formula s q)).free_var_set : by unfold sub_formula
    ... = (sub_formula s p).free_var_set ∪ (sub_formula s q).free_var_set : by unfold formula.free_var_set
    ... = finset.bUnion p.free_var_set (fun y : var_symbols, (s y).all_var_set) ∪
            finset.bUnion q.free_var_set (fun y : var_symbols, (s y).all_var_set) : by simp only [ih_p, ih_q]
    ... = finset.bUnion (p.free_var_set ∪ q.free_var_set) (fun y : var_symbols, (s y).all_var_set) :
          begin ext1, simp only [finset.mem_union, finset.mem_bUnion, exists_prop], split, finish, finish end
    ... = finset.bUnion (and p q).free_var_set (fun y : var_symbols, (s y).all_var_set) : by unfold formula.free_var_set
  },
  case formula.or : p q ih_p ih_q {
    calc
    (sub_formula s (or p q)).free_var_set = (or (sub_formula s p) (sub_formula s q)).free_var_set : by unfold sub_formula
    ... = (sub_formula s p).free_var_set ∪ (sub_formula s q).free_var_set : by unfold formula.free_var_set
    ... = finset.bUnion p.free_var_set (fun y : var_symbols, (s y).all_var_set) ∪
            finset.bUnion q.free_var_set (fun y : var_symbols, (s y).all_var_set) : by simp only [ih_p, ih_q]
    ... = finset.bUnion (p.free_var_set ∪ q.free_var_set) (fun y : var_symbols, (s y).all_var_set) :
          begin ext1, simp only [finset.mem_union, finset.mem_bUnion, exists_prop], split, finish, finish end
    ... = finset.bUnion (or p q).free_var_set (fun y : var_symbols, (s y).all_var_set) : by unfold formula.free_var_set
  },
  case formula.imp : p q ih_p ih_q {
    calc
    (sub_formula s (imp p q)).free_var_set = (imp (sub_formula s p) (sub_formula s q)).free_var_set : by unfold sub_formula
    ... = (sub_formula s p).free_var_set ∪ (sub_formula s q).free_var_set : by unfold formula.free_var_set
    ... = finset.bUnion p.free_var_set (fun y : var_symbols, (s y).all_var_set) ∪
            finset.bUnion q.free_var_set (fun y : var_symbols, (s y).all_var_set) : by simp only [ih_p, ih_q]
    ... = finset.bUnion (p.free_var_set ∪ q.free_var_set) (fun y : var_symbols, (s y).all_var_set) :
          begin ext1, simp only [finset.mem_union, finset.mem_bUnion, exists_prop], split, finish, finish end
    ... = finset.bUnion (imp p q).free_var_set (fun y : var_symbols, (s y).all_var_set) : by unfold formula.free_var_set
  },
  case formula.iff : p q ih_p ih_q {
    calc
    (sub_formula s (iff p q)).free_var_set = (iff (sub_formula s p) (sub_formula s q)).free_var_set : by unfold sub_formula
    ... = (sub_formula s p).free_var_set ∪ (sub_formula s q).free_var_set : by unfold formula.free_var_set
    ... = finset.bUnion p.free_var_set (fun y : var_symbols, (s y).all_var_set) ∪
            finset.bUnion q.free_var_set (fun y : var_symbols, (s y).all_var_set) : by simp only [ih_p, ih_q]
    ... = finset.bUnion (p.free_var_set ∪ q.free_var_set) (fun y : var_symbols, (s y).all_var_set) :
          begin ext1, simp only [finset.mem_union, finset.mem_bUnion, exists_prop], split, finish, finish end
    ... = finset.bUnion (iff p q).free_var_set (fun y : var_symbols, (s y).all_var_set) : by unfold formula.free_var_set
  },
  case formula.forall_ : x p ih {
    let x' :=
      if ∃ y ∈ p.free_var_set \ {x}, x ∈ (s y).all_var_set
      then variant x (sub_formula (function.update s x (var x)) p).free_var_set
      else x,
    calc
          (sub_formula s (forall_ x p)).free_var_set
        = (forall_ x' (sub_formula (function.update s x (var x')) p)).free_var_set :
            by unfold sub_formula
    ... = (sub_formula (function.update s x (var x')) p).free_var_set \ {x'} :
            by unfold formula.free_var_set
    ... = (finset.bUnion p.free_var_set (fun (y : var_symbols), ((function.update s x (var x')) y).all_var_set)) \ {x'} :
            by simp only [ih (function.update s x (var x'))]
    ... = (finset.bUnion (p.free_var_set \ {x}) (fun (y : var_symbols), ((function.update s x (var x')) y).all_var_set)) \ {x'} :
            begin apply finset_bUnion_sdiff, finish end
    ... = (finset.bUnion (p.free_var_set \ {x}) (fun (y : var_symbols), (s y).all_var_set)) \ {x'} :
            begin congr' 1, apply finset.bUnion_congr, refl, intros a h1, congr, apply function.update_noteq,
            simp only [finset.mem_sdiff, finset.mem_singleton] at h1, cases h1, exact h1_right end
    ... = finset.bUnion (p.free_var_set \ {x}) (fun (y : var_symbols), (s y).all_var_set) :
            begin apply finset.sdiff_singleton_not_mem_eq_self, exact lem_3_6_1 x p s ih end
  },
  case formula.exists_ : x p ih {
    let x' :=
      if ∃ y ∈ p.free_var_set \ {x}, x ∈ (s y).all_var_set
      then variant x (sub_formula (function.update s x (var x)) p).free_var_set
      else x,
    calc
          (sub_formula s (exists_ x p)).free_var_set
        = (exists_ x' (sub_formula (function.update s x (var x')) p)).free_var_set :
            by unfold sub_formula
    ... = (sub_formula (function.update s x (var x')) p).free_var_set \ {x'} :
            by unfold formula.free_var_set
    ... = (finset.bUnion p.free_var_set (fun (y : var_symbols), ((function.update s x (var x')) y).all_var_set)) \ {x'} :
            by simp only [ih (function.update s x (var x'))]
    ... = (finset.bUnion (p.free_var_set \ {x}) (fun (y : var_symbols), ((function.update s x (var x')) y).all_var_set)) \ {x'} :
            begin apply finset_bUnion_sdiff, finish end
    ... = (finset.bUnion (p.free_var_set \ {x}) (fun (y : var_symbols), (s y).all_var_set)) \ {x'} :
            begin congr' 1, apply finset.bUnion_congr, refl, intros a h1, congr, apply function.update_noteq,
            simp only [finset.mem_sdiff, finset.mem_singleton] at h1, cases h1, exact h1_right end
    ... = finset.bUnion (p.free_var_set \ {x}) (fun (y : var_symbols), (s y).all_var_set) :
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
  case formula.pred : n x terms {
    calc
    holds T m v (sub_formula s (pred n x terms)) ↔
      holds T m v (pred n x (fun i : fin n, term.sub_var_term s (terms i))) : by unfold sub_formula
    ... ↔ m.pred n x (fun i : fin n, eval_term T m v (term.sub_var_term s (terms i))) : by unfold holds
    ... ↔ m.pred n x (fun i : fin n, eval_term T m ((eval_term T m v) ∘ s) (terms i)) : by simp only [thm_5]
    ... ↔ holds T m ((eval_term T m v) ∘ s) (pred n x terms) : by unfold holds
  },
  case formula.eq : u v {
    unfold sub_formula, unfold holds,
    simp only [thm_5],
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
      then variant x (sub_formula (function.update s x (var x)) p).free_var_set
      else x,
    have s1 : ∀ a : T, ∀ z ∈ p.free_var_set,
      ((eval_term T m (function.update v x' a)) ∘ (function.update s x (var x'))) z =
        (function.update ((eval_term T m v) ∘ s) x a) z,
      intros a z h1,
      by_cases z = x, {
        calc
        ((eval_term T m (function.update v x' a)) ∘ (function.update s x (var x'))) z =
              ((eval_term T m (function.update v x' a)) ∘ (function.update s x (var x'))) x : by rewrite h
        ... = (eval_term T m (function.update v x' a)) ((function.update s x (var x')) x) : by simp only [function.comp_app]
        ... = (eval_term T m (function.update v x' a)) (var x') : by simp only [function.update_same]
        ... = (function.update v x' a) x' : by unfold eval_term
        ... = a : by simp only [function.update_same]
        ... = (function.update ((eval_term T m v) ∘ s) x a) x : by simp only [function.update_same]
        ... = (function.update ((eval_term T m v) ∘ s) x a) z : by rewrite h
      },
      {
        have s2 : z ∈ p.free_var_set \ {x}, simp only [finset.mem_sdiff, finset.mem_singleton], exact and.intro h1 h,
        have s3 : x' ∉ finset.bUnion (p.free_var_set \ {x}) (fun y : var_symbols, (s y).all_var_set),
          exact lem_3_6_1 x p s (lem_3_6 p),
        have s4 : (s z).all_var_set ⊆ finset.bUnion (p.free_var_set \ {x}) (fun y : var_symbols, (s y).all_var_set),
          exact finset.subset_bUnion_of_mem (fun y : var_symbols, (s y).all_var_set) s2,
        have s5 : x' ∉ (s z).all_var_set, exact finset.not_mem_mono s4 s3,
        have s6 : ∀ (x : var_symbols), x ∈ (s z).all_var_set → x ≠ x', intros y h3, by_contradiction, apply s5, rewrite <- h, exact h3,
        calc
        ((eval_term T m (function.update v x' a)) ∘ (function.update s x (var x'))) z =
              (eval_term T m (function.update v x' a)) ((function.update s x (var x')) z) : by simp only [function.comp_app]
        ... = (eval_term T m (function.update v x' a)) (s z) : by simp only [function.update_noteq h]
        ... = eval_term T m v (s z) : begin apply thm_1 (function.update v x' a) v, intros x h3,
                                      apply function.update_noteq, exact s6 x h3 end
        ... = ((eval_term T m v) ∘ s) z : by simp only [eq_self_iff_true]
        ... = (function.update ((eval_term T m v) ∘ s) x a) z : begin symmetry, apply function.update_noteq h end
      },
    calc
    holds T m v (sub_formula s (forall_ x p))
      ↔ holds T m v (forall_ x' (sub_formula (function.update s x (var x')) p)) : by unfold sub_formula
    ... ↔ ∀ a : T, holds T m (function.update v x' a) (sub_formula (function.update s x (var x')) p) : by unfold holds
    ... ↔ (∀ a : T, (holds T m ((eval_term T m (function.update v x' a)) ∘ (function.update s x (var x'))) p)) : by finish
    ... ↔ (∀ a : T, holds T m (function.update ((eval_term T m v) ∘ s) x a) p) :
      begin split,
      intros h1 a,
      rewrite <- (thm_2 ((eval_term T m (function.update v x' a)) ∘ (function.update s x (var x'))) (function.update ((eval_term T m v) ∘ s) x a) (s1 a)), exact h1 a,
      intros h1 a,
      rewrite (thm_2 ((eval_term T m (function.update v x' a)) ∘ (function.update s x (var x'))) (function.update ((eval_term T m v) ∘ s) x a) (s1 a)), exact h1 a
      end
    ... ↔ holds T m (eval_term T m v ∘ s) (forall_ x p) : by unfold holds
  },
  case formula.exists_ : x p ih {
    let x' :=
      if ∃ y ∈ p.free_var_set \ {x}, x ∈ (s y).all_var_set
      then variant x (sub_formula (function.update s x (var x)) p).free_var_set
      else x,
    have s1 : ∀ a : T, ∀ z ∈ p.free_var_set,
      ((eval_term T m (function.update v x' a)) ∘ (function.update s x (var x'))) z = (function.update ((eval_term T m v) ∘ s) x a) z,
      intros a z h1,
      by_cases z = x, {
        calc
        ((eval_term T m (function.update v x' a)) ∘ (function.update s x (var x'))) z =
              ((eval_term T m (function.update v x' a)) ∘ (function.update s x (var x'))) x : by rewrite h
        ... = (eval_term T m (function.update v x' a)) ((function.update s x (var x')) x) : by simp only [function.comp_app]
        ... = (eval_term T m (function.update v x' a)) (var x') : by simp only [function.update_same]
        ... = (function.update v x' a) x' : by unfold eval_term
        ... = a : by simp only [function.update_same]
        ... = (function.update ((eval_term T m v) ∘ s) x a) x : by simp only [function.update_same]
        ... = (function.update ((eval_term T m v) ∘ s) x a) z : by rewrite h
      },
      {
        have s2 : z ∈ p.free_var_set \ {x}, simp only [finset.mem_sdiff, finset.mem_singleton], exact and.intro h1 h,
        have s3 : x' ∉ finset.bUnion (p.free_var_set \ {x}) (fun y : var_symbols, (s y).all_var_set),
          exact lem_3_6_1 x p s (lem_3_6 p),
        have s4 : (s z).all_var_set ⊆ finset.bUnion (p.free_var_set \ {x}) (fun y : var_symbols, (s y).all_var_set),
          exact finset.subset_bUnion_of_mem (fun y : var_symbols, (s y).all_var_set) s2,
        have s5 : x' ∉ (s z).all_var_set, exact finset.not_mem_mono s4 s3,
        have s6 : ∀ (x : var_symbols), x ∈ (s z).all_var_set → x ≠ x', intros y h3, by_contradiction, apply s5, rewrite <- h, exact h3,
        calc
        ((eval_term T m (function.update v x' a)) ∘ (function.update s x (var x'))) z =
              (eval_term T m (function.update v x' a)) ((function.update s x (var x')) z) : by simp only [function.comp_app]
        ... = (eval_term T m (function.update v x' a)) (s z) : by simp only [function.update_noteq h]
        ... = eval_term T m v (s z) : begin apply thm_1 (function.update v x' a) v, intros x h3,
                                      apply function.update_noteq, exact s6 x h3 end
        ... = ((eval_term T m v) ∘ s) z : by simp only [eq_self_iff_true]
        ... = (function.update ((eval_term T m v) ∘ s) x a) z : begin symmetry, apply function.update_noteq h end
      },
    calc
    holds T m v (sub_formula s (exists_ x p))
      ↔ holds T m v (exists_ x' (sub_formula (function.update s x (var x')) p)) : by unfold sub_formula
    ... ↔ ∃ a : T, holds T m (function.update v x' a) (sub_formula (function.update s x (var x')) p) : by unfold holds
    ... ↔ (∃ a : T, (holds T m ((eval_term T m (function.update v x' a)) ∘ (function.update s x (var x'))) p)) : by finish
    ... ↔ (∃ a : T, holds T m (function.update ((eval_term T m v) ∘ s) x a) p) :
    begin
      split,
      {
        intros h1,
        apply exists.elim h1, intros a h2, apply exists.intro a,
        rewrite <- thm_2
          ((eval_term T m (function.update v x' a)) ∘ (function.update s x (var x')))
          (function.update ((eval_term T m v) ∘ s) x a) (s1 a),
        exact h2,
      },
      {
        intros h1,
        apply exists.elim h1, intros a h2, apply exists.intro a,
        rewrite thm_2
          ((eval_term T m (function.update v x' a)) ∘ (function.update s x (var x')))
          (function.update ((eval_term T m v) ∘ s) x a) (s1 a),
        exact h2,
      },
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
  unfold is_valid at *,
  intros D m v,
  simp only [thm_3_7], apply h1
end


def sub_single_var' (x : var_symbols) (t : term) : instantiation :=
  function.update (fun v : var_symbols, var v) x t

theorem is_valid_pred_2'
  (p : formula)
  (x : var_symbols)
  (t : term) :
  let s := sub_single_var x t in
  is_valid ((forall_ x p).imp (sub_formula s p)) :=
begin
  intro s,
  unfold is_valid, unfold holds,
  intros D m v h2,
    rewrite thm_3_7 p s D m v,
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


def formula.all_pred_set' : formula → finset pred_symbols
| bottom := ∅
| top := ∅
| (pred n x terms) := {x}
| (eq _ _) := ∅
| (not p) := p.all_pred_set'
| (and p q) := p.all_pred_set' ∪ q.all_pred_set'
| (or p q) := p.all_pred_set' ∪ q.all_pred_set'
| (imp p q) := p.all_pred_set' ∪ q.all_pred_set'
| (iff p q) := p.all_pred_set' ∪ q.all_pred_set'
| (forall_ x p) := p.all_pred_set'
| (exists_ x p) := p.all_pred_set'


def fin_fun_range
  {α : Type} [decidable_eq α]
  {n : ℕ}
  (f : fin n → α) :
  finset α := finset.image f (finset.fin_range n)

def list_zip_fun
  {α β : Type} [decidable_eq α]
  (f : list α)
  (g : list β)
  (h2 : g.length = f.length)
  (default : α → β) :
  α → β :=
  fun x : α,
    if h3 : x ∈ f
    then
      g.nth_le (f.index_of x)
      begin rewrite h2, simp only [list.index_of_lt_length], exact h3 end
    else default x

def fin_zip_fun
  {α β : Type} [decidable_eq α]
  {m n : ℕ}
  (h1 : n = m)
  (f : fin m → α)
  (g : fin n → β)
  (default : α → β) :
  α → β := list_zip_fun (list.of_fn f) (list.of_fn g)
  begin simp only [list.length_of_fn], exact h1, end default

def fin_zip_fun'
  {α β : Type} [decidable_eq α]
  {m n : ℕ}
  (h1 : m = n)
  (f : fin m → α)
  (nodup : ∀ a b : fin m, a ≠ b → f a ≠ f b)
  (g : fin n → β)
  (default : α → β) :
  α → β :=
fun x : α, if h : ∃ a : fin m, f a = x then
  begin
  subst h1,
  apply g,
  apply fintype.choose (fun a : fin m, f a = x),
  simp only,
  apply exists.elim h, intros a h2,
  apply exists.intro a, simp only,
  split,
  exact h2,
  intros y h3,
  by_contradiction,
  apply nodup y a h, rewrite h2, rewrite h3,
  end
 else default x

def sub_single_predicate
  (q_n : ℕ)
  (q : pred_symbols)
  (params : fin q_n → var_symbols)
  (h1 : ∀ a b : fin q_n, a ≠ b → params a ≠ params b)
  (r : formula) :
  formula → formula
| bottom := bottom
| top := top
| (pred n x terms) :=
    if h : q_n = n ∧ x = q
    then sub_formula (fin_zip_fun' h.left params h1 terms term.var) r
    else pred n x terms
| (eq u v) := eq u v
| (not p) := not (sub_single_predicate p)
| (and p q) := and (sub_single_predicate p) (sub_single_predicate q)
| (or p q) := or (sub_single_predicate p) (sub_single_predicate q)
| (imp p q) := imp (sub_single_predicate p) (sub_single_predicate q)
| (iff p q) := iff (sub_single_predicate p) (sub_single_predicate q)
| (forall_ x p) :=
    let free_minus_params : finset var_symbols
      := r.free_var_set \ fin_fun_range params
    in
  let x' : var_symbols :=
    if x ∈ free_minus_params
    then variant x (free_minus_params ∪ (p.free_var_set \ {x}))
    else x
  in forall_ x' (sub_single_predicate p)
| (exists_ x p) :=
    let free_minus_params : finset var_symbols
      := r.free_var_set \ fin_fun_range params
    in
  let x' : var_symbols :=
    if x ∈ free_minus_params
    then variant x (free_minus_params ∪ (p.free_var_set \ {x}))
    else x
  in forall_ x' (sub_single_predicate p)


-- uniform simultaneous replacement of the predicates in a formula by formulas

def formula.sub_pred_formula (s : (ℕ × string) → formula) : formula → formula
| bottom := bottom
| top := top
| (pred n x terms) := s (n, x)
| (eq u v) := eq u v
| (not p) := not (formula.sub_pred_formula p)
| (and p q) := and (formula.sub_pred_formula p) (formula.sub_pred_formula q)
| (or p q) := or (formula.sub_pred_formula p) (formula.sub_pred_formula q)
| (imp p q) := imp (formula.sub_pred_formula p) (formula.sub_pred_formula q)
| (iff p q) := iff (formula.sub_pred_formula p) (formula.sub_pred_formula q)
| (forall_ x p) :=
  let x' :=
  if ∃ r ∈ p.all_pred_set, x ∈ (s r).free_var_set
  then variant x ((formula.sub_pred_formula p).free_var_set)
  else x
  in forall_ x' (formula.sub_pred_formula p)
| (exists_ x p) :=
  let x' :=
  if ∃ r ∈ p.all_pred_set, x ∈ (s r).free_var_set
  then variant x ((formula.sub_pred_formula p).free_var_set)
  else x
  in exists_ x' (formula.sub_pred_formula p)

def interpretation.sub'
  {D : Type}
  (m : interpretation D)
  (v : valuation D)
  (f : (ℕ × string) → formula) : interpretation D :=
    interpretation.mk m.nonempty m.func
      (fun n : ℕ, fun x : string, fun terms : fin n → D, holds D m v (f (n, x)))

lemma formula.sub_pred_formula_holds
  (D : Type)
  (m : interpretation D)
  (v v' : valuation D)
  (p : formula)
  (s : (ℕ × string) → formula)
  (hv : ∀ (y ∈ p.all_pred_set) (x ∈ (s y).free_var_set), v x = v' x) :
  holds D m v (formula.sub_pred_formula s p)
    ↔ holds D (m.sub v' s) v p :=
begin
  induction p generalizing v,
  case formula.bottom : v hv
  { unfold interpretation.sub, unfold formula.sub_pred_formula, unfold holds },
  case formula.top : v hv
  { unfold interpretation.sub, unfold formula.sub_pred_formula, unfold holds },
  case formula.pred : n p terms v hv
  {
    simp only [interpretation.sub], unfold formula.sub_pred_formula, unfold holds,
    simp [formula.all_pred_set] at hv,
    apply thm_2,
    intros x h2, apply hv n p, refl, refl, exact h2
  },
  case formula.eq : t t'
  {
    simp only [interpretation.sub],
    unfold formula.sub_pred_formula,
    unfold holds, 
    admit,
  },
  case formula.not : p p_ih v hv
  {
    unfold formula.sub_pred_formula, unfold holds,
    apply not_congr, apply p_ih _ hv
  },
  case formula.and : p q p_ih q_ih
  {
    unfold formula.sub_pred_formula, unfold holds,
    simp [formula.all_pred_set, or_imp_distrib, forall_and_distrib] at hv,
    apply and_congr,
    apply p_ih,
    intros y h2 x h3, apply hv.1 y.1 y.2,
    simp only [prod.mk.eta], exact h2, simp only [prod.mk.eta], exact h3,
    apply q_ih,
    intros y h2 x h3, apply hv.2 y.1 y.2,
    simp only [prod.mk.eta], exact h2, simp only [prod.mk.eta], exact h3
  },
  case formula.or : p q p_ih q_ih
  {
    unfold formula.sub_pred_formula, unfold holds,
    simp [formula.all_pred_set, or_imp_distrib, forall_and_distrib] at hv,
    apply or_congr,
    apply p_ih,
    intros y h2 x h3, apply hv.1 y.1 y.2,
    simp only [prod.mk.eta], exact h2, simp only [prod.mk.eta], exact h3,
    apply q_ih,
    intros y h2 x h3, apply hv.2 y.1 y.2,
    simp only [prod.mk.eta], exact h2, simp only [prod.mk.eta], exact h3
  },
  case formula.imp : p q p_ih q_ih
  {
    unfold formula.sub_pred_formula, unfold holds,
    simp [formula.all_pred_set, or_imp_distrib, forall_and_distrib] at hv,
    apply imp_congr,
    apply p_ih,
    intros y h2 x h3, apply hv.1 y.1 y.2,
    simp only [prod.mk.eta], exact h2, simp only [prod.mk.eta], exact h3,
    apply q_ih,
    intros y h2 x h3, apply hv.2 y.1 y.2,
    simp only [prod.mk.eta], exact h2, simp only [prod.mk.eta], exact h3
  },
  case formula.iff : p q p_ih q_ih
  {
    unfold formula.sub_pred_formula, unfold holds,
    simp [formula.all_pred_set, or_imp_distrib, forall_and_distrib] at hv,
    apply iff_congr,
    apply p_ih,
    intros y h2 x h3, apply hv.1 y.1 y.2,
    simp only [prod.mk.eta], exact h2, simp only [prod.mk.eta], exact h3,
    apply q_ih,
    intros y h2 x h3, apply hv.2 y.1 y.2,
    simp only [prod.mk.eta], exact h2, simp only [prod.mk.eta], exact h3
  },
  case formula.forall_ : y p p_ih v hv
  {
    unfold formula.all_pred_set at hv,
    unfold formula.sub_pred_formula,
    simp,
    unfold holds,
    apply forall_congr, intros a,
    specialize p_ih (function.update v y a),
    sorry
  },
  case formula.exists_ : y p p_ih v hv
  {
    sorry
  },
end


structure blah : Type :=
(n : ℕ)
(params : fin n → var_symbols)
(nodup : ∀ l m : fin n, l ≠ m → params l ≠ params m)
(q : formula)

def sub_predicate :
  (pred_symbols → blah) → formula → formula
| m bottom := bottom
| m top := top
| m (pred n x terms) :=
    let r := m x in
    if h : r.n = n then
    let s := fin_zip_fun' h r.params r.nodup terms term.var in
    sub_formula s r.q
    else pred n x terms
| m (eq u v) := eq u v
| m (not p) := not (sub_predicate m p)
| m (and p q) := and (sub_predicate m p) (sub_predicate m q)
| m (or p q) := or (sub_predicate m p) (sub_predicate m q)
| m (imp p q) := imp (sub_predicate m p) (sub_predicate m q)
| m (iff p q) := iff (sub_predicate m p) (sub_predicate m q)
| m (forall_ x p) :=
  let free_minus_param :=
  finset.bUnion p.all_pred_set'
    (fun y : pred_symbols, (m y).q.free_var_set \ finset.image (m y).params (finset.fin_range (m y).n))
  in
  let x' : var_symbols :=
    if x ∈ free_minus_param
    then variant x (free_minus_param ∪ (p.free_var_set \ {x}))
    else x
  in forall_ x' (sub_predicate m p)
| m (exists_ x p) :=
  let free_minus_param :=
  finset.bUnion p.all_pred_set'
    (fun y : pred_symbols, (m y).q.free_var_set \ finset.image (m y).params (finset.fin_range (m y).n))
  in
  let x' : var_symbols :=
    if x ∈ free_minus_param
    then variant x (free_minus_param ∪ (p.free_var_set \ {x}))
    else x
  in exists_ x' (sub_predicate m p)


theorem sub_pred_is_valid
  (p : formula)
  (h1 : is_valid p)
  (a : pred_symbols → blah) :
  is_valid (sub_predicate a p) :=
begin
  induction p,
  case formula.bottom
  { unfold sub_predicate, exact h1, },
  case formula.top
  { unfold sub_predicate, exact h1, },
  case formula.pred : n x terms
  {
    unfold sub_predicate,
    unfold is_valid,
    intros D m v,
    simp only,
    split_ifs,
    simp only [thm_3_7],
    unfold function.comp,
    unfold fin_zip_fun',
    subst h,
    simp only,
    sorry, sorry,
  },
  case formula.eq : p_ᾰ p_ᾰ_1
  { admit },
  case formula.not : p_ᾰ p_ih
  { admit },
  case formula.and : p_ᾰ p_ᾰ_1 p_ih_ᾰ p_ih_ᾰ_1
  { admit },
  case formula.or : p_ᾰ p_ᾰ_1 p_ih_ᾰ p_ih_ᾰ_1
  { admit },
  case formula.imp : p_ᾰ p_ᾰ_1 p_ih_ᾰ p_ih_ᾰ_1
  { admit },
  case formula.iff : p_ᾰ p_ᾰ_1 p_ih_ᾰ p_ih_ᾰ_1
  { admit },
  case formula.forall_ : p_ᾰ p_ᾰ_1 p_ih
  { admit },
  case formula.exists_ : p_ᾰ p_ᾰ_1 p_ih
  { admit },
end


/-
Proof schemes.
Proof schemes are semantically valid formula schemes.
-/
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

/-
to_fun = Takes a list of string formula pairs and returns a function
from strings to formulas. For each pair in the list the function maps
the string in the pair to the formula in the pair. The function maps
each string not in a pair to an atomic proposition of the same name as
the string.
-/
def to_fun : list (string × formula) → string → formula
| [] v := mk_prop v
| ((u, f) :: fs) v := if u = v then f else to_fun fs v


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
--| replace : ℕ → (pred_symbols → (list var_symbols × formula)) → step

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
  return (local_context.append_formula (eq lhs rhs))

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
  let s := sub_single_var' x t,
  let f := (forall_ x p).imp (sub_formula s p),
  let t1 : is_valid f := is_valid_pred_2' p x t,
  return (local_context.append_proof (proof.mk f t1))

| _ local_context (pred_3 p_index x) := do
  p <- local_context.get_nth_formula p_index,
  (plift.up h1) <- dguard (x ∉ p.free_var_set),
  let f := (p.imp (forall_ x p)),
  let t1 : is_valid f := is_valid_pred_3 p x h1,
  return (local_context.append_proof (proof.mk f t1))
/-
| global_context local_context (replace p_index m) := do
  (proof.mk p hp) <- global_context.get_nth_proof p_index,
  let f := sub_predicate m p,
  let t1 : is_valid f := sub_pred_is_valid p hp m,
  return (local_context.append_proof (proof.mk f t1))
-/
/-
If p is a semantically valid formula in the global context then
any consistent substitution of formulas for
the propositions in p is a semantically valid formula.
-/
/-
| glb_ctx loc_ctx (apply_proof idx m) := do
  (proof.mk p h1) <- glb_ctx.get_proof idx,
  let split := list.unzip m,
  let split_fst := prod.fst split,
  let split_snd := prod.snd split,
  split_snd' <- list.mmap (loc_ctx.get_formula) split_snd,
  let join := list.zip split_fst split_snd',
  let m := to_fun join,
  let f := formula.sub m p,
  let t1 : is_valid f := thm_2_4_gen p h1 m,
  return (loc_ctx.append_proof (proof.mk f t1))
-/

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
