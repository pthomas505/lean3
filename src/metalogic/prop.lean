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

/-
Formula schemes.
atom "P" : A formula scheme variable named "P".
-/
@[derive decidable_eq] inductive formula : Type
| bottom : formula
| top : formula
| atom : string → formula
| not : formula → formula
| and : formula → formula → formula
| or : formula → formula → formula
| imp : formula → formula → formula
| iff : formula → formula → formula

open formula

meta def formula.repr : formula → string
| bottom := sformat!"F"
| top := sformat!"T"
| (atom x) := x.quote
| (not p) := sformat!"(¬ {p.repr})"
| (and p q) := sformat!"({p.repr} ∧ {q.repr})"
| (or p q) := sformat!"({p.repr} ∨ {q.repr})"
| (imp p q) := sformat!"({p.repr} → {q.repr})"
| (iff p q) := sformat!"({p.repr} ↔ {q.repr})"
meta instance : has_repr formula := has_repr.mk formula.repr

def valuation := string → bool

def eval : formula → valuation → bool
| bottom _ := ff
| top _ := tt
| (atom x) m := m x
| (not p) m := !(eval p m)
| (and p q) m := (eval p m) && (eval q m)
| (or p q) m := (eval p m) || (eval q m)
| (imp p q) m := (!(eval p m)) || (eval q m)
| (iff p q) m := (eval p m) = (eval q m)

def atoms : formula → set string
| bottom := {}
| top := {}
| (atom x) := {x}
| (not p) := atoms p
| (and p q) := (atoms p) ∪ (atoms q)
| (or p q) := (atoms p) ∪ (atoms q)
| (imp p q) := (atoms p) ∪ (atoms q)
| (iff p q) := (atoms p) ∪ (atoms q)

theorem thm_2_1
  (p : formula) :
  set.finite (atoms p) :=
begin
  induction p,
  case bottom { unfold atoms, exact set.finite_empty},
  case top { unfold atoms, exact set.finite_empty},
  case atom : x { unfold atoms, exact set.finite_singleton x },
  case not : p ih_p { unfold atoms, exact ih_p },
  case and : p q ih_p ih_q { unfold atoms, exact set.finite.union ih_p ih_q },
  case or : p q ih_p ih_q { unfold atoms, exact set.finite.union ih_p ih_q },
  case imp : p q ih_p ih_q { unfold atoms, exact set.finite.union ih_p ih_q },
  case iff : p q ih_p ih_q { unfold atoms, exact set.finite.union ih_p ih_q },
end

theorem thm_2_2
  (p : formula)
  (v v' : valuation)
  (h1 : ∀ x ∈ (atoms p), v x = v' x) :
  eval p v = eval p v' :=
begin
  induction p,
  case bottom : { reflexivity },
  case top : { reflexivity },
  case atom : x { unfold eval, apply h1 x, unfold atoms, simp only [set.mem_singleton] },
  case not : p ih {
    unfold eval, unfold atoms at h1,
    have s1 : eval p v = eval p v', apply ih, exact h1,
    rewrite s1 },
  case and : p q ih_p ih_q {
    unfold eval, unfold atoms at h1, simp only [set.mem_union_eq] at h1,
    have s1 : eval p v = eval p v', apply ih_p, intros x h2, apply h1, left, exact h2,
    have s2 : eval q v = eval q v', apply ih_q, intros x h2, apply h1, right, exact h2,
    rewrite s1, rewrite s2 },
  case or : p q ih_p ih_q {
    unfold eval, unfold atoms at h1, simp only [set.mem_union_eq] at h1,
    have s1 : eval p v = eval p v', apply ih_p, intros x h2, apply h1, left, exact h2,
    have s2 : eval q v = eval q v', apply ih_q, intros x h2, apply h1, right, exact h2,
    rewrite s1, rewrite s2 },
  case imp : p q ih_p ih_q {
    unfold eval, unfold atoms at h1, simp only [set.mem_union_eq] at h1,
    have s1 : eval p v = eval p v', apply ih_p, intros x h2, apply h1, left, exact h2,
    have s2 : eval q v = eval q v', apply ih_q, intros x h2, apply h1, right, exact h2,
    rewrite s1, rewrite s2 },
  case iff : p q ih_p ih_q {
    unfold eval, unfold atoms at h1, simp only [set.mem_union_eq] at h1,
    have s1 : eval p v = eval p v', apply ih_p, intros x h2, apply h1, left, exact h2,
    have s2 : eval q v = eval q v', apply ih_q, intros x h2, apply h1, right, exact h2,
    rewrite s1, rewrite s2 }
end

def sub : (string → formula) → formula → formula
| _ bottom := bottom
| _ top := top
| f (atom x) := f x
| f (not p) := not (sub f p)
| f (and p q) := and (sub f p) (sub f q)
| f (or p q) := or (sub f p) (sub f q)
| f (imp p q) := imp (sub f p) (sub f q)
| f (iff p q) := iff (sub f p) (sub f q)

theorem thm_2_3_gen
  (p : formula)
  (f : string → formula)
  (v : valuation) :
  eval (sub f p) v = eval p (fun i, eval (f i) v) :=
begin
  induction p,
  case bottom { reflexivity },
  case top { reflexivity },
  case atom : x { reflexivity },
  case not : p ih_p { unfold sub, unfold eval, rewrite ih_p },
  case and : p q ih_p ih_q { unfold sub, unfold eval, rewrite ih_p, rewrite ih_q },
  case or : p q ih_p ih_q { unfold sub, unfold eval, rewrite ih_p, rewrite ih_q },
  case imp : p q ih_p ih_q { unfold sub, unfold eval, rewrite ih_p, rewrite ih_q },
  case iff : p q ih_p ih_q { unfold sub, unfold eval, rewrite ih_p, rewrite ih_q }
end

notation  x `↦` a := fun v, function.update v x a

theorem thm_2_3
  (x : string)
  (p q : formula)
  (v : valuation) :
  eval (sub ((x ↦ q) atom) p) v =
    eval p ((x ↦ (eval q v)) v) :=
begin
  rewrite thm_2_3_gen,
  congr, ext p,
  simp [function.update]; split_ifs; simp [eval]
end

def is_tauto (p : formula) : Prop := ∀ v : valuation, eval p v = tt

theorem thm_2_4_gen
  (p : formula)
  (h1 : is_tauto p)
  (f : string → formula) :
  is_tauto (sub f p) :=
begin
  unfold is_tauto at *,
  intros v,
  rewrite thm_2_3_gen, apply h1
end

theorem thm_2_4
  (p : formula)
  (h1 : is_tauto p)
  (x : string)
  (q : formula) :
  is_tauto (sub ((x ↦ q) atom) p) :=
begin
  apply thm_2_4_gen _ h1
end

theorem thm_2_5
  (v : valuation)
  (p q : formula)
  (h1 : eval p v = eval q v)
  (x : string)
  (r : formula) :
  eval (sub ((x ↦ p) atom) r) v =
    eval (sub ((x ↦ q) atom) r) v :=
begin
  rewrite [thm_2_3, thm_2_3, h1]
end

theorem eval_not
  (p : formula)
  (v : valuation) :
  eval (not p) v = tt ↔ ¬ (eval p v = tt) :=
begin
  unfold eval, cases eval p v; exact dec_trivial
end

theorem eval_imp
  (p q : formula)
  (v : valuation) :
  eval (imp p q) v = tt ↔ ((eval p v = tt) → (eval q v = tt)) :=
begin
  unfold eval, cases eval p v; cases eval q v; exact dec_trivial
end

theorem is_tauto_mp
  (p q : formula)
  (h1 : is_tauto p)
  (h2 : is_tauto (p.imp q)) :
  is_tauto q :=
begin
  unfold is_tauto at *,
  intro v,
  simp only [eval_imp] at h2,
  apply h2, apply h1
end

theorem is_tauto_prop_1
(p q : formula) :
is_tauto (p.imp (q.imp p)) :=
begin
  unfold is_tauto,
  intro v,
  simp only [eval_imp],
  intros h1 h2,
  exact h1
end

theorem is_tauto_prop_2
  (p q r : formula) :
  is_tauto ((p.imp (q.imp r)).imp ((p.imp q).imp (p.imp r))) :=
begin
  unfold is_tauto,
  intro v,
  simp only [eval_imp],
  intros h1 h2 h3,
  apply h1, exact h3, apply h2, exact h3
end

theorem is_tauto_prop_3
(p q : formula) :
is_tauto (((not p).imp (not q)).imp (q.imp p)) :=
begin
  unfold is_tauto,
  intro v,
  simp only [eval_not, eval_imp],
  intros h1 h2,
  by_contradiction, apply h1, exact h, exact h2
end
