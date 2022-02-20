/-
References:

https://www.cambridge.org/core/books/handbook-of-practical-logic-and-automated-reasoning/EB6396296813CB562987E8C37AC4520D
https://www.cl.cam.ac.uk/~jrh13/atp/index.html
Harrison, J. (2009).
Handbook of Practical Logic and Automated Reasoning.
Cambridge: Cambridge University Press.
doi:10.1017/CBO9780511576430
-/

import tactic

inductive formula : Type
| bottom : formula
| top : formula
| atom : string → formula
| not : formula → formula
| and : formula → formula → formula
| or : formula → formula → formula
| imp : formula → formula → formula
| iff : formula → formula → formula

open formula

def eval : formula → (string → bool) → bool
| bottom _ := ff
| top _ := tt
| (atom x) m := m x
| (not p) m := eval p m
| (and p q) m := (eval p m) && (eval q m)
| (or p q) m := (eval p m) || (eval q m)
| (imp p q) m := (!(eval p m)) || (eval q m)
| (iff p q) m := (eval p m) = (eval q m)

def atoms : formula → (set string)
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
  (v v' : string → bool)
  (h1 : ∀ x ∈ (atoms p), v x = v' x) :
  eval p v = eval p v' :=
begin
  induction p,
  case bottom : { reflexivity },
  case top : { reflexivity },
  case atom : x {unfold eval, apply h1 x, unfold atoms, simp only [set.mem_singleton]},
  case not : p ih { unfold eval, exact ih h1 },
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

def atom_id : string -> formula := fun (x : string), atom x

theorem thm_2_3_gen
  (p : formula)
  (f : string → formula)
  (v : string -> bool) :
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

theorem thm_2_3
  (x : string)
  (p q : formula)
  (v : string → bool) :
  eval (sub (function.update atom_id x q) p) v =
    eval p (function.update v x (eval q v)) :=
begin
  have s1 : (fun i, eval (((function.update atom_id x q)) i) v) =
    (function.update v x (eval q v)),
    ext, unfold function.update, split_ifs,
    simp, unfold atom_id, unfold eval,
  have s2 : eval (sub (function.update atom_id x q) p) v =
    eval p (fun i, eval ((function.update atom_id x q) i) v),
    exact thm_2_3_gen p (function.update atom_id x q) v,
  rewrite s2, rewrite s1
end


def is_tauto (p : formula) : Prop := ∀ v : string → bool, eval p v = tt

theorem thm_2_4_gen
  (p : formula)
  (h1 : is_tauto p)
  (f : string -> formula) :
  is_tauto (sub f p) :=
begin
  unfold is_tauto at *,
  intros v,
  rewrite thm_2_3_gen p f v,
  exact h1 (fun (i : string), eval (f i) v)
end

theorem thm_2_4
  (p : formula)
  (h1 : is_tauto p)
  (x : string)
  (q : formula) :
  is_tauto (sub (function.update atom_id x q) p) :=
begin
  unfold is_tauto at *,
  intros v,
  rewrite thm_2_3 x p q v,
  exact h1 (function.update v x (eval q v))
end

theorem thm_2_5
  (v : string → bool)
  (p q : formula)
  (h1 : eval p v = eval q v)
  (x : string)
  (r : formula) :
  eval (sub (function.update atom_id x p) r) v =
    eval (sub (function.update atom_id x q) r) v :=
begin
  have s1 : eval (sub (function.update atom_id x p) r) v =
    eval r (function.update v x (eval p v)), apply thm_2_3,
  have s2 : eval (sub (function.update atom_id x q) r) v =
    eval r (function.update v x (eval q v)), apply thm_2_3,
  rewrite s1, rewrite s2, rewrite h1
end
