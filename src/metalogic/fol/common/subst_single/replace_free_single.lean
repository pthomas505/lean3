import metalogic.fol.aux.misc_list
import metalogic.fol.aux.function_update_ite
import metalogic.fol.common.semantics
import metalogic.fol.common.binders

import data.finset


set_option pp.parens true


namespace fol

open formula


/-
[margaris]
pg. 48

If $P$ is a formula, $v$ is a variable, and $t$ is a term, then $P(t/v)$ is the result of replacing each free occurrence of $v$ in $P$ by an occurrence of $t$.
-/

/--
  Helper function for replace_free.
-/
def replace_free_aux (v t : var_name) : finset var_name → formula → formula
| _ true_ := true_
| binders (pred_ X xs) :=
    pred_
    X
    (xs.map (fun (x : var_name), if x = v ∧ x ∉ binders then t else x))
| binders (not_ phi) := not_ (replace_free_aux binders phi)
| binders (imp_ phi psi) :=
    imp_
    (replace_free_aux binders phi)
    (replace_free_aux binders psi)
| binders (forall_ x phi) := forall_ x (replace_free_aux (binders ∪ {x}) phi)

/--
  replace_free v t P :=

  P(t/v)

  v → t in P for each free occurrence of v in P

  The result of replacing each free occurrence of v in P by an occurrence of t.
-/
def replace_free (v t : var_name) (F : formula) : formula :=
  replace_free_aux v t ∅ F


/--
  fast_replace_free v t P :=

  P(t/v)

  v → t in P for each free occurrence of v in P

  The result of replacing each free occurrence of v in P by an occurrence of t.

  This is a more efficient version of replace_free.
-/
def fast_replace_free (v t : var_name) : formula → formula
| true_ := true_
| (pred_ X xs) :=
    pred_
    X
    (xs.map (fun (x : var_name), if x = v then t else x))
| (not_ phi) := not_ (fast_replace_free phi)
| (imp_ phi psi) := imp_ (fast_replace_free phi) (fast_replace_free psi)
| (forall_ x phi) :=
    if v = x
    then forall_ x phi -- v is not free in (forall_ x phi)
    else forall_ x (fast_replace_free phi)


-- replace_free = fast_replace_free

lemma replace_free_aux_mem_binders
  (F : formula)
  (v t : var_name)
  (binders : finset var_name)
  (h1 : v ∈ binders) :
  replace_free_aux v t binders F = F :=
begin
  induction F generalizing binders,
  case formula.true_ : binders h1
  {
    refl,
  },
  case formula.pred_ : X xs binders h1
  {
    unfold replace_free_aux,
    simp only [eq_self_iff_true, list.map_eq_self_iff, ite_eq_right_iff, and_imp, true_and],
    intros x a1 a2 a3,
    subst a2,
    contradiction,
  },
  case formula.not_ : phi phi_ih binders h1
  {
    solve_by_elim,
  },
  case formula.imp_ : phi psi phi_ih psi_ih binders h1
  {
    unfold replace_free_aux,
    congr,
    {
      exact phi_ih binders h1,
    },
    {
      exact psi_ih binders h1,
    }
  },
  case formula.forall_ : x phi phi_ih binders h1
  {
    unfold replace_free_aux,
    simp only [eq_self_iff_true, true_and],
    apply phi_ih,
    simp only [finset.mem_union, finset.mem_singleton],
    tauto,
  },
end


lemma replace_free_aux_eq_fast_replace_free
  (F : formula)
  (v t : var_name)
  (binders : finset var_name)
  (h1 : v ∉ binders) :
  replace_free_aux v t binders F = fast_replace_free v t F :=
begin
  induction F generalizing binders,
  case formula.true_ : binders h1
  {
    refl,
  },
  case formula.pred_ : X xs binders h1
  {
    unfold replace_free_aux,
    unfold fast_replace_free,
    congr,
    funext,
    by_cases c1 : x = v,
    {
      subst c1,
      simp only [eq_self_iff_true, true_and, ite_not, if_true, ite_eq_right_iff],
      intros a1,
      contradiction,
    },
    {
      simp only [if_neg c1],
      simp only [ite_eq_right_iff, and_imp],
      intros a1,
      contradiction,
    }
  },
  case formula.not_ : phi phi_ih binders h1
  {
    unfold replace_free_aux,
    unfold fast_replace_free,
    simp only,
    exact phi_ih binders h1,
  },
  case formula.imp_ : phi psi phi_ih psi_ih binders h1
  {
    unfold replace_free_aux,
    unfold fast_replace_free,
    simp only,
    split,
    {
      exact phi_ih binders h1,
    },
    {
      exact psi_ih binders h1,
    }
  },
  case formula.forall_ : x phi phi_ih binders h1
  {
    unfold replace_free_aux,
    unfold fast_replace_free,
    split_ifs,
    {
      simp only [eq_self_iff_true, true_and],
      apply replace_free_aux_mem_binders,
      simp only [finset.mem_union, finset.mem_singleton],
      right,
      exact h,
    },
    {
      simp only [eq_self_iff_true, true_and],
      apply phi_ih,
      simp only [finset.mem_union, finset.mem_singleton],
      push_neg,
      split,
      {
        exact h1,
      },
      {
        exact h,
      }
    }
  },
end

theorem replace_free_eq_fast_replace_free
  (F : formula)
  (v t : var_name) :
  replace_free v t F = fast_replace_free v t F :=
begin
  unfold replace_free,
  apply replace_free_aux_eq_fast_replace_free,
  simp only [finset.not_mem_empty, not_false_iff],
end

--

theorem fast_replace_free_self
  (F : formula)
  (v : var_name) :
  fast_replace_free v v F = F :=
begin
  induction F,
  case formula.true_
  {
    refl,
  },
  case formula.pred_ : X xs
  {
    unfold fast_replace_free,
    simp only [eq_self_iff_true, list.map_eq_self_iff, ite_eq_right_iff, true_and],
    tauto,
  },
  case formula.not_ : phi phi_ih
  {
    solve_by_elim,
  },
  case formula.imp_ : phi psi phi_ih psi_ih
  {
    unfold fast_replace_free,
    simp only,
    tauto,
  },
  case formula.forall_ : x phi phi_ih
  {
    unfold fast_replace_free,
    simp only [ite_eq_left_iff, eq_self_iff_true, true_and],
    tauto,
  },
end


theorem not_free_in_fast_replace_free_self
  (F : formula)
  (v t : var_name)
  (h1 : ¬ is_free_in v F) :
  fast_replace_free v t F = F :=
begin
  induction F,
  case formula.true_
  {
    refl,
  },
  case formula.pred_ : X xs
  {
    unfold is_free_in at h1,
    simp only [list.mem_to_finset, bool.of_to_bool_iff] at h1,

    unfold fast_replace_free,
    congr,
    simp only [list.map_eq_self_iff, ite_eq_right_iff],
    intros x a1 a2,
    subst a2,
    contradiction,
  },
  case formula.not_ : phi phi_ih
  {
    solve_by_elim,
  },
  case formula.imp_ : phi psi phi_ih psi_ih
  {
    unfold is_free_in at h1,
    simp only [bool.of_to_bool_iff] at h1,
    push_neg at h1,
    cases h1,

    unfold fast_replace_free,
    congr,
    {
      exact phi_ih h1_left,
    },
    {
      exact psi_ih h1_right,
    }
  },
  case formula.forall_ : x phi phi_ih
  {
    unfold is_free_in at h1,
    simp only [bool.of_to_bool_iff, not_and] at h1,

    unfold fast_replace_free,
    simp only [ite_eq_left_iff, eq_self_iff_true, true_and],
    intros a1,
    apply phi_ih,
    exact h1 a1,
  },
end


theorem fast_replace_free_inverse
  (F : formula)
  (v t : var_name)
  (h1 : ¬ occurs_in t F) :
  fast_replace_free t v (fast_replace_free v t F) = F :=
begin
  induction F,
  case formula.true_
  {
    refl,
  },
  case formula.pred_ : X xs
  {
    unfold occurs_in at h1,
    simp only [list.mem_to_finset, bool.of_to_bool_iff] at h1,

    unfold fast_replace_free,
    congr,
    simp only [list.map_map, list.map_eq_self_iff, function.comp_app, ite_eq_left_iff],
    intros x a1,
    by_cases c1 : x = v,
    {
      subst c1,
      simp only [eq_self_iff_true, not_true, is_empty.forall_iff, if_true],
    },
    {
      simp only [if_neg c1],
      simp only [ite_eq_right_iff],
      intros a2,
      specialize a2 c1,
      subst a2,
      contradiction,
    },
  },
  case formula.not_ : phi phi_ih
  {
    solve_by_elim,
  },
  case formula.imp_ : phi psi phi_ih psi_ih
  {
    unfold occurs_in at h1,
    simp only [bool.of_to_bool_iff] at h1,
    push_neg at h1,
    cases h1,

    unfold fast_replace_free,
    congr,
    {
      exact phi_ih h1_left,
    },
    {
      exact psi_ih h1_right,
    }
  },
  case formula.forall_ : x phi phi_ih
  {
    unfold occurs_in at h1,
    simp only [bool.of_to_bool_iff] at h1,
    push_neg at h1,
    cases h1,

    unfold fast_replace_free,
    split_ifs,
    {
      unfold fast_replace_free,
      simp [if_neg h1_left],
      apply not_free_in_fast_replace_free_self,
      contrapose! h1_right,
      exact is_free_in_imp_occurs_in t phi h1_right,
    },
    {
      unfold fast_replace_free,
      simp only [if_neg h1_left],
      tauto,
    }
  },
end


theorem not_is_free_in_fast_replace_free
  (F : formula)
  (v t : var_name)
  (h1 : ¬ v = t) :
  ¬ is_free_in v (fast_replace_free v t F) :=
begin
  induction F,
  case formula.true_
  {
    unfold fast_replace_free,
    unfold is_free_in,
    simp only [to_bool_false_eq_ff, coe_sort_ff, not_false_iff],
  },
  case formula.pred_ : X xs
  {
    unfold fast_replace_free,
    unfold is_free_in,
    simp only [bool.of_to_bool_iff, list.mem_to_finset, list.mem_map, not_exists, not_and],
    intros x a1,
    split_ifs,
    {
      tauto,
    },
    {
      exact h,
    }
  },
  case formula.not_ : phi phi_ih
  {
    assumption,
  },
  case formula.imp_ : phi psi phi_ih psi_ih
  {
    unfold fast_replace_free,
    unfold is_free_in,
    simp only [bool.of_to_bool_iff],
    push_neg,
    split,
    {
      exact phi_ih,
    },
    {
      exact psi_ih,
    }
  },
  case formula.forall_ : x phi phi_ih
  {
    unfold fast_replace_free,
    split_ifs,
    {
      unfold is_free_in,
      simp only [bool.of_to_bool_iff, not_and, eq_ff_eq_not_eq_tt],
      tauto,
    },
    {
      unfold is_free_in,
      simp only [bool.of_to_bool_iff, not_and],
      tauto,
    }
  },
end

end fol
