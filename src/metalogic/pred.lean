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


def list_to_fin_list {T : Type} (l : list T) : fin l.length → T :=
fun i : fin l.length, list.nth_le l i.val i.property


meta def fin_list.to_string {α} [has_to_string α] {n} (as : fin n → α) : string :=
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
| (func f args) := f.quote ++ fin_list.to_string (fun i, (args i).repr)

meta instance : has_repr term := has_repr.mk term.repr

def mk_func (name : string) (terms : list term)
:= func name (list_to_fin_list terms)


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
| (atom x terms) := x.quote ++ fin_list.to_string (fun i, (terms i).repr)
| (not p) := sformat!"(¬ {p.repr})"
| (and p q) := sformat!"({p.repr} ∧ {q.repr})"
| (or p q) := sformat!"({p.repr} ∨ {q.repr})"
| (imp p q) := sformat!"({p.repr} → {q.repr})"
| (iff p q) := sformat!"({p.repr} ↔ {q.repr})"
| (forall_ x p) := sformat!"(∀ {x.quote}. {p.repr})"
| (exists_ x p) := sformat!"(∃ {x.quote}. {p.repr})"

meta instance : has_repr formula := has_repr.mk formula.repr

def mk_atom (name : string) (terms : list term) :=
atom name (list_to_fin_list terms)


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

def all_var_set : term → set string
| (var x) := {x}
| (func f args) := ⋃ i, all_var_set (args i)

theorem thm_3_1
  (T : Type)
  (m : interpretation T)
  (t : term)
  (v v' : valuation T)
  (h1 : ∀ x ∈ (all_var_set t), v x = v' x) :
  eval_term T m v t = eval_term T m v' t :=
begin
  induction t,
  case term.var {
    unfold all_var_set at h1,
    unfold eval_term,
    simp only [set.mem_singleton_iff, forall_eq] at h1,
    exact h1 },
  case term.func : n f arg ih {
    unfold all_var_set at *,
    simp at *,
    sorry
	}

end

#eval (forall_ "x" (mk_atom "P" [mk_func "f" [(var "x")], var "y"]))
