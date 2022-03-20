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


def list_to_fin_fun {T : Type} (l : list T) : fin l.length → T :=
fun i : fin l.length, list.nth_le l i.val i.property


meta def fin_fun.to_string {α} [has_to_string α] {n} (as : fin n → α) : string :=
list.to_string (list.of_fn as)


/-
Term schemes.
var "x" : An object variable named "x".
func "c" [] : A constant named "c".
func "f" [x1 .. xn] : A function named "f" of n terms.
-/
inductive term : Type
| var : string → term
| func {n} : string → (fin n → term) → term

open term

meta def term.repr : term → string
| (var x) := x.quote
| (func f args) := f.quote ++ fin_fun.to_string (fun i, (args i).repr)

meta instance : has_repr term := has_repr.mk term.repr

def mk_func (name : string) (terms : list term)
:= func name (list_to_fin_fun terms)


/-
Formula schemes.
atom "P" [] : A propositional variable named "P".
atom "P" [x1 .. xn] : A predicate variable named "P" of n terms.
-/
inductive formula : Type
| bottom : formula
| top : formula
| atom {n} : string → (fin n → term) → formula
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
| (atom x terms) := x.quote ++ fin_fun.to_string (fun i, (terms i).repr)
| (not p) := sformat!"(¬ {p.repr})"
| (and p q) := sformat!"({p.repr} ∧ {q.repr})"
| (or p q) := sformat!"({p.repr} ∨ {q.repr})"
| (imp p q) := sformat!"({p.repr} → {q.repr})"
| (iff p q) := sformat!"({p.repr} ↔ {q.repr})"
| (forall_ x p) := sformat!"(∀ {x.quote}. {p.repr})"
| (exists_ x p) := sformat!"(∃ {x.quote}. {p.repr})"

meta instance : has_repr formula := has_repr.mk formula.repr

def mk_atom (name : string) (terms : list term) :=
atom name (list_to_fin_fun terms)


structure interpretation (T : Type) : Type :=
(domain : set T)
(nonempty : domain.nonempty)
(func {n} : string → (fin n → T) → T)
(pred {n} : string → (fin n → T) → bool)

def valuation (T : Type) := string → T

def eval_term
(T : Type) (m : interpretation T) (v : valuation T) : term → T
| (var x) := v x
| (func f args) := m.func f (fun i, eval_term (args i))


def holds (T : Type) (m : interpretation T) : valuation T → formula → Prop
| _ bottom := false
| _ top := true
| v (atom x args) := m.pred x (fun i, eval_term T m v (args i))
| v (not p) := ¬ holds v p
| v (and p q) := holds v p ∧ holds v q
| v (or p q) := holds v p ∨ holds v q
| v (imp p q) := holds v p → holds v q
| v (iff p q) := holds v p ↔ holds v q
| v (forall_ x p) := forall a ∈ m.domain, holds (function.update v x a) p
| v (exists_ x p) := exists a ∈ m.domain, holds (function.update v x a) p

def term.all_var_set : term → set string
| (var x) := {x}
| (func f args) := ⋃ i, term.all_var_set (args i)

theorem thm_3_1
  (T : Type)
  (m : interpretation T)
  (t : term)
  (v v' : valuation T)
  (h1 : ∀ x ∈ (term.all_var_set t), v x = v' x) :
  eval_term T m v t = eval_term T m v' t :=
begin
  induction t,
  case term.var {
    unfold term.all_var_set at h1,
    unfold eval_term,
    simp only [set.mem_singleton_iff, forall_eq] at h1,
    exact h1 },
  case term.func : n f args ih {
    unfold term.all_var_set at *,
    have s1 : forall i : fin n, forall x : string, x ∈ term.all_var_set (args i) → v x = v' x,
    intros i x h, apply h1, exact set.mem_Union_of_mem i h,
    unfold eval_term at *, congr, ext, apply ih, apply s1
	}
end

#eval (forall_ "x" (mk_atom "P" [mk_func "f" [(var "x")], var "y"]))

def formula.all_var_set : formula → set string
| bottom := ∅
| top := ∅
| (atom x terms) := ⋃ i, term.all_var_set (terms i)
| (not p) := p.all_var_set
| (and p q) := set.union p.all_var_set q.all_var_set
| (or p q) := set.union p.all_var_set q.all_var_set
| (imp p q) := set.union p.all_var_set q.all_var_set
| (iff p q) := set.union p.all_var_set q.all_var_set
| (forall_ x p) := set.insert x p.all_var_set
| (exists_ x p) := set.insert x p.all_var_set

def formula.free_var_set : formula → set string
| bottom := ∅
| top := ∅
| (atom x terms) := ⋃ i, term.all_var_set (terms i)
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
    have s1 : forall i, eval_term T m v (terms i) = eval_term T m v' (terms i),
      intros i, apply thm_3_1, intros x h, apply h1, exact set.mem_Union_of_mem i h,
    unfold holds, finish
  },
  case formula.not : p ih {
    have s1 : holds T m v p ↔ holds T m v' p, apply ih, unfold formula.free_var_set at h1,
      exact h1,
    unfold holds, rewrite s1
  },
  case formula.and : p q ih_p ih_q {
    have s1 : holds T m v p ↔ holds T m v' p, apply ih_p, intros x h, apply h1,
      unfold formula.free_var_set, left, exact h,
    have s2 : holds T m v q ↔ holds T m v' q, apply ih_q, intros x h, apply h1,
      unfold formula.free_var_set, right, exact h,
    unfold holds, rewrite s1, rewrite s2
  },
  case formula.or : p q ih_p ih_q {
    have s1 : holds T m v p ↔ holds T m v' p, apply ih_p, intros x h, apply h1,
      unfold formula.free_var_set, left, exact h,
    have s2 : holds T m v q ↔ holds T m v' q, apply ih_q, intros x h, apply h1,
      unfold formula.free_var_set, right, exact h,
    unfold holds, rewrite s1, rewrite s2
  },
  case formula.imp : p q ih_p ih_q {
    have s1 : holds T m v p ↔ holds T m v' p, apply ih_p, intros x h, apply h1,
      unfold formula.free_var_set, left, exact h,
    have s2 : holds T m v q ↔ holds T m v' q, apply ih_q, intros x h, apply h1,
      unfold formula.free_var_set, right, exact h,
    unfold holds, rewrite s1, rewrite s2
  },
  case formula.iff : p q ih_p ih_q {
    have s1 : holds T m v p ↔ holds T m v' p, apply ih_p, intros x h, apply h1,
      unfold formula.free_var_set, left, exact h,
    have s2 : holds T m v q ↔ holds T m v' q, apply ih_q, intros x h, apply h1,
      unfold formula.free_var_set, right, exact h,
    unfold holds, rewrite s1, rewrite s2
  },
  case formula.forall_ : x p ih {
    unfold formula.free_var_set at h1,
    unfold holds,
    have s1 : ∀ (a : T), a ∈ m.domain →
      (holds T m (function.update v x a) p ↔ holds T m (function.update v' x a) p),
        intros a h, apply ih, intros y h',
        unfold function.update, simp, split_ifs, refl,
        apply h1, simp only [set.mem_diff, set.mem_singleton_iff], exact and.intro h' h_1,
    exact ball_congr s1
  },
  case formula.exists_ : x p ih {
    unfold formula.free_var_set at h1,
    unfold holds,
    have s1 : ∀ (a : T), a ∈ m.domain →
      (holds T m (function.update v x a) p ↔ holds T m (function.update v' x a) p),
        intros a h, apply ih, intros y h',
        unfold function.update, simp, split_ifs, refl,
        apply h1, simp only [set.mem_diff, set.mem_singleton_iff], exact and.intro h' h_1,
    exact bex_congr s1
  }
end

def is_sentence (p : formula) : Prop := p.free_var_set = ∅

