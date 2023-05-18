import .binders
import metalogic.fol.aux.misc_list
import metalogic.fol.aux.function_update_ite

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


/-
[margaris]
pg. 48

If $v$ and $u$ are variables and $P$ is a formula, then $P$ admits $u$ for $v$ if and only if there is no free occurrence of $v$ in $P$ that becomes a bound occurrence of $u$ in $P(u/v)$. If $t$ is a term, then $P$ admits $t$ for $v$ if and only if $P$ admits for $v$ every variable in $t$.
-/

/--
  Helper function for admits.
-/
@[derive decidable]
def admits_aux (v u : var_name) : finset var_name → formula → bool
| _ true_ := true
| binders (pred_ X xs) :=
    (v ∈ xs ∧ v ∉ binders) → -- if there is a free occurrence of v in P
    u ∉ binders -- then it does not become a bound occurrence of u in P(u/v)
| binders (not_ phi) := admits_aux binders phi
| binders (imp_ phi psi) := admits_aux binders phi ∧ admits_aux binders psi
| binders (forall_ x phi) := admits_aux (binders ∪ {x}) phi

/--
  admits v u P := True if and only if there is no free occurrence of the variable v in the formula P that becomes a bound occurrence of the variable u in P(u/v).

  P admits u for v

  v → u in P
-/
@[derive decidable]
def admits (v u : var_name) (F : formula) : bool :=
  admits_aux v u ∅ F


/--
  Helper function for fast_admits.
-/
@[derive decidable]
def fast_admits_aux (v u : var_name) : finset var_name → formula → bool
| _ true_ := true
| binders (pred_ X xs) :=
    v ∈ xs → -- if there is a free occurrence of v in P
    u ∉ binders -- then it does not become a bound occurrence of u in P(u/v)
| binders (not_ phi) := fast_admits_aux binders phi
| binders (imp_ phi psi) := fast_admits_aux binders phi ∧ fast_admits_aux binders psi
| binders (forall_ x phi) := v = x ∨ fast_admits_aux (binders ∪ {x}) phi

/--
  fast_admits v u P := True if and only if there is no free occurrence of the variable v in the formula P that becomes a bound occurrence of the variable u in P(u/v).

  P admits u for v

  v → u in P

  This is a more efficient version of admits.
-/
@[derive decidable]
def fast_admits (v u : var_name) (F : formula) : bool :=
  fast_admits_aux v u ∅ F


/--
  Used to label each occurrence of a variable in a formula as free or bound.
-/
@[derive [inhabited, decidable_eq]]
inductive bool_formula : Type
| true_ : bool_formula
| pred_ : pred_name → list bool → bool_formula
| not_ : bool_formula → bool_formula
| imp_ : bool_formula → bool_formula → bool_formula
| forall_ : bool → bool_formula → bool_formula


/--
  Helper function for to_is_bound.
-/
def to_is_bound_aux : finset var_name → formula → bool_formula
| _ true_ := bool_formula.true_
| binders (pred_ X xs) := bool_formula.pred_ X (xs.map (fun (v : var_name), v ∈ binders))
| binders (not_ phi) := bool_formula.not_ (to_is_bound_aux binders phi)
| binders (imp_ phi psi) := bool_formula.imp_ (to_is_bound_aux binders phi) (to_is_bound_aux binders psi)
| binders (forall_ x phi) := bool_formula.forall_ true (to_is_bound_aux (binders ∪ {x}) phi)


/--
  Creates a bool_formula from a formula. Each bound occurence of a variable in the formula is mapped to true in the bool formula. Each free occurence of a variable in the formula is mapped to false in the bool formula.
-/
def to_is_bound (F : formula) : bool_formula :=
  to_is_bound_aux ∅ F


-- admits ↔ fast_admits

lemma admits_aux_imp_fast_admits_aux
  (F : formula)
  (v u : var_name)
  (binders : finset var_name)
  (h1 : v ∉ binders)
  (h2 : admits_aux v u binders F) :
  fast_admits_aux v u binders F :=
begin
  induction F generalizing binders,
  case formula.true_ : binders h1 h2
  {
    unfold fast_admits_aux,
    simp only [to_bool_true_eq_tt, coe_sort_tt],
  },
  case fol.formula.pred_ : X xs binders h1 h2
  {
    unfold admits_aux at h2,
    simp at h2,

    unfold fast_admits_aux,
    simp,
    intros a1,
    exact h2 a1 h1,
  },
  case fol.formula.not_ : phi phi_ih binders h1 h2
  {
    unfold admits_aux at h2,

    unfold fast_admits_aux,
    exact phi_ih binders h1 h2,
  },
  case fol.formula.imp_ : phi psi phi_ih psi_ih binders h1 h2
  {
    unfold admits_aux at h2,
    simp at h2,
    cases h2,

    unfold fast_admits_aux,
    simp,
    split,
    {
      exact phi_ih binders h1 h2_left,
    },
    {
      exact psi_ih binders h1 h2_right,
    }
  },
  case formula.forall_ : x phi phi_ih binders h1 h2
  {
    unfold admits_aux at h2,

    unfold fast_admits_aux,
    simp,
    by_cases c1 : v = x,
    {
      left,
      exact c1,
    },
    {
      right,
      apply phi_ih,
      {
        simp only [finset.mem_union, finset.mem_singleton],
        tauto,
      },
      {
        exact h2,
      },
    }
  },
end


lemma mem_binders_imp_admits_aux
  (F : formula)
  (v u : var_name)
  (binders : finset var_name)
  (h1 : v ∈ binders) :
  admits_aux v u binders F :=
begin
  induction F generalizing binders,
  case formula.true_ : binders h1
  {
    unfold admits_aux,
    simp,
  },
  case fol.formula.pred_ : X xs binders h1
  {
    unfold admits_aux,
    simp,
    intros a1 a2,
    contradiction,
  },
  case fol.formula.not_ : phi phi_ih binders h1
  {
    unfold admits_aux,
    exact phi_ih binders h1,
  },
  case fol.formula.imp_ : phi psi phi_ih psi_ih binders h1
  {
    unfold admits_aux,
    simp,
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
    unfold admits_aux,
    apply phi_ih,
    simp only [finset.mem_union, finset.mem_singleton],
    left,
    exact h1,
  },
end


lemma fast_admits_aux_imp_admits_aux
  (F : formula)
  (v u : var_name)
  (binders : finset var_name)
  (h1 : fast_admits_aux v u binders F) :
  admits_aux v u binders F :=
begin
  induction F generalizing binders,
  case formula.true_ : binders h1
  {
    unfold admits_aux,
    simp only [to_bool_true_eq_tt, coe_sort_tt],
  },
  case fol.formula.pred_ : X xs binders h1
  {
    unfold fast_admits_aux at h1,
    simp at h1,

    unfold admits_aux,
    simp,
    tauto,
  },
  case fol.formula.not_ : phi phi_ih binders h1
  {
    unfold fast_admits_aux at h1,

    unfold admits_aux,
    exact phi_ih binders h1,
  },
  case fol.formula.imp_ : phi psi phi_ih psi_ih binders h1
  {
    unfold fast_admits_aux at h1,
    simp at h1,
    cases h1,

    unfold admits_aux,
    simp,
    split,
    {
      exact phi_ih binders h1_left,
    },
    {
      exact psi_ih binders h1_right,
    }
  },
  case formula.forall_ : x phi phi_ih binders h1
  {
    unfold fast_admits_aux at h1,
    simp at h1,

    unfold admits_aux,
    cases h1,
    {
      apply mem_binders_imp_admits_aux,
      subst h1,
      simp only [finset.mem_union, finset.mem_singleton, eq_self_iff_true, or_true],
    },
    {
      apply phi_ih,
      exact h1,
    }
  },
end


theorem admits_iff_fast_admits
  (F : formula)
  (v u : var_name) :
  admits v u F ↔ fast_admits v u F :=
begin
  unfold admits,
  unfold fast_admits,
  split,
  {
    apply admits_aux_imp_fast_admits_aux,
    simp only [finset.not_mem_empty, not_false_iff],
  },
  {
    apply fast_admits_aux_imp_admits_aux,
  }
end


-- fast_admits


lemma fast_admits_aux_self
  (F : formula)
  (v : var_name)
  (binders : finset var_name)
  (h1 : v ∉ binders) :
  fast_admits_aux v v binders F :=
begin
  induction F generalizing binders,
  case formula.true_ : binders h1
  {
    unfold fast_admits_aux,
    simp only [to_bool_true_eq_tt, coe_sort_tt],
  },
  case fol.formula.pred_ : X xs binders h1
  {
    unfold fast_admits_aux,
    simp only [bool.of_to_bool_iff],
    intros a1,
    exact h1,
  },
  case fol.formula.not_ : phi phi_ih binders h1
  {
    unfold fast_admits_aux,
    exact phi_ih binders h1,
  },
  case fol.formula.imp_ : phi psi phi_ih psi_ih binders h1
  {
    unfold fast_admits_aux,
    simp,
    split,
    {
      exact phi_ih binders h1,
    },
    {
      exact psi_ih binders h1,
    },
  },
  case formula.forall_ : x phi phi_ih binders h1
  {
    unfold fast_admits_aux,
    by_cases c1 : v = x,
    {
      simp,
      tauto,
    },
    {
      simp,
      right,
      apply phi_ih,
      simp only [finset.mem_union, finset.mem_singleton],
      tauto,
    }
  },
end


theorem fast_admits_self
  (F : formula)
  (v : var_name) :
  fast_admits v v F :=
begin
  unfold fast_admits,
  apply fast_admits_aux_self,
  simp only [finset.not_mem_empty, not_false_iff],
end

--

lemma not_is_free_in_imp_fast_admits_aux
  (F : formula)
  (v u : var_name)
  (binders : finset var_name)
  (h1 : ¬ is_free_in v F) :
  fast_admits_aux v u binders F :=
begin
  induction F generalizing binders,
  case formula.true_ : binders
  {
    unfold fast_admits_aux,
    simp,
  },
  case formula.pred_ : X xs
  {
    unfold is_free_in at h1,
    simp at h1,

    unfold fast_admits_aux,
    simp,
    intros a1,
    contradiction,
  },
  case fol.formula.not_ : phi phi_ih binders
  {
    unfold is_free_in at h1,

    unfold fast_admits_aux,
    exact phi_ih h1 binders,
  },
  case fol.formula.imp_ : phi psi phi_ih psi_ih binders
  {
    unfold is_free_in at h1,
    simp at h1,
    push_neg at h1,
    cases h1,

    unfold fast_admits_aux,
    simp,
    split,
    {
      exact phi_ih h1_left binders,
    },
    {
      exact psi_ih h1_right binders,
    },
  },
  case fol.formula.forall_ : x phi phi_ih binders
  {
    unfold is_free_in at h1,
    simp only [bool.of_to_bool_iff, not_and] at h1,

    unfold fast_admits_aux,
    simp,
    by_cases c1 : v = x,
    {
      left,
      exact c1,
    },
    {
      right,
      apply phi_ih,
      exact h1 c1,
    },
  },
end


theorem not_is_free_in_imp_fast_admits
  (F : formula)
  (v u : var_name)
  (h1 : ¬ is_free_in v F) :
  fast_admits v u F :=
begin
  unfold fast_admits,
  apply not_is_free_in_imp_fast_admits_aux,
  exact h1,
end

--

lemma not_is_bound_in_imp_fast_admits_aux
  (F : formula)
  (v u : var_name)
  (binders : finset var_name)
  (h1 : ¬ is_bound_in u F)
  (h2 : u ∉ binders) :
  fast_admits_aux v u binders F :=
begin
  induction F generalizing binders,
  case formula.true_ : binders h2
  {
    unfold fast_admits_aux,
    simp only [to_bool_true_eq_tt, coe_sort_tt],
  },
  case formula.pred_ : X xs binders h2
  {
    unfold fast_admits_aux,
    simp,
    tauto,
  },
  case formula.not_ : phi phi_ih binders h2
  {
    unfold is_bound_in at h1,

    unfold fast_admits_aux,
    tauto,
  },
  case formula.imp_ : phi psi phi_ih psi_ih binders h2
  {
    unfold is_bound_in at h1,
    simp at h1,

    unfold fast_admits_aux,
    simp,
    tauto,
  },
  case formula.forall_ : x phi phi_ih binders h2
  {
    unfold is_bound_in at h1,
    simp at h1,
    push_neg at h1,
    cases h1,

    unfold fast_admits_aux,
    simp,
    right,
    apply phi_ih,
    {
      exact h1_right,
    },
    {
      simp only [finset.mem_union, finset.mem_singleton],
      tauto,
    }
  },
end

theorem not_is_bound_in_imp_fast_admits
  (F : formula)
  (v u : var_name)
  (h1 : ¬ is_bound_in u F) :
  fast_admits v u F :=
begin
  unfold fast_admits,
  apply not_is_bound_in_imp_fast_admits_aux,
  {
    exact h1,
  },
  {
    simp only [finset.not_mem_empty, not_false_iff],
  }
end

--

lemma fast_replace_free_aux_fast_admits_aux
  (F : formula)
  (v t : var_name)
  (binders : finset var_name)
  (h1 : ¬ occurs_in t F)
  (h2 : v ∉ binders) :
  fast_admits_aux t v binders (fast_replace_free v t F) :=
begin
  induction F generalizing binders,
  case formula.true_ : binders h2
  {
    unfold fast_replace_free,
    unfold fast_admits_aux,
    simp,
  },
  case formula.pred_ : X xs binders h2
  {
    unfold fast_replace_free,
    unfold fast_admits_aux,
    simp,
    tauto,
  },
  case formula.not_ : phi phi_ih binders h2
  {
    unfold occurs_in at h1,

    unfold fast_replace_free,
    unfold fast_admits_aux,
    tauto,
  },
  case formula.imp_ : phi psi phi_ih psi_ih binders h2
  {
    unfold occurs_in at h1,
    simp at h1,

    unfold fast_replace_free,
    unfold fast_admits_aux,
    simp,
    tauto,
  },
  case formula.forall_ : x phi phi_ih binders h2
  {
    unfold occurs_in at h1,
    simp at h1,
    push_neg at h1,
    cases h1,

    unfold fast_replace_free,
    split_ifs,
    {
      unfold fast_admits_aux,
      subst h,
      simp,
      right,
      apply not_is_free_in_imp_fast_admits_aux,
      intros contra,
      apply h1_right,
      apply is_free_in_imp_occurs_in,
      exact contra,
    },
    {
      unfold fast_admits_aux,
      simp,
      right,
      apply phi_ih h1_right,
      simp only [finset.mem_union, finset.mem_singleton],
      tauto,
    },
  },
end


lemma fast_replace_free_fast_admits
  (F : formula)
  (v t : var_name)
  (h1 : ¬ occurs_in t F) :
  fast_admits t v (fast_replace_free v t F) :=
begin
  unfold fast_admits,
  apply fast_replace_free_aux_fast_admits_aux F v t ∅ h1,
  simp only [finset.not_mem_empty, not_false_iff],
end

--

lemma replace_free_aux_fast_admits_aux
  (F : formula)
  (v t : var_name)
  (binders : finset var_name)
  (h1 : ¬ occurs_in t F) :
  fast_admits_aux t v binders (replace_free_aux v t binders F) :=
begin
  induction F generalizing binders,
  case formula.true_ : binders
  {
    unfold replace_free_aux,
    unfold fast_admits_aux,
    simp,
  },
  case formula.pred_ : X xs binders
  {
    unfold occurs_in at h1,
    simp at h1,

    unfold replace_free_aux,
    unfold fast_admits_aux,
    simp,
    intros x a1 a2,

    by_cases c1 : x = v ∧ x ∉ binders,
    {
      cases c1,
      subst c1_left,
      exact c1_right,
    },
    {
      push_neg at c1,
      specialize a2 c1,
      subst a2,
      contradiction,
    }
  },
  case formula.not_ : phi phi_ih binders
  {
    unfold occurs_in at h1,

    unfold replace_free_aux,
    unfold fast_admits_aux,
    tauto,
  },
  case formula.imp_ : phi psi phi_ih psi_ih binders
  {
    unfold occurs_in at h1,
    simp at h1,

    unfold replace_free_aux,
    unfold fast_admits_aux,
    simp,
    tauto,
  },
  case formula.forall_ : x phi phi_ih binders
  {
    unfold occurs_in at h1,
    simp at h1,

    unfold replace_free_aux,
    unfold fast_admits_aux,
    simp,
    tauto,
  },
end


lemma replace_free_fast_admits
  (F : formula)
  (v t : var_name)
  (h1 : ¬ occurs_in t F) :
  fast_admits t v (replace_free v t F) :=
begin
  unfold replace_free,
  unfold fast_admits,
  apply replace_free_aux_fast_admits_aux,
  exact h1,
end

--

lemma fast_admits_aux_add_binders
  (F : formula)
  (v u : var_name)
  (S T : finset var_name)
  (h1 : fast_admits_aux v u S F)
  (h2 : u ∉ T) :
  fast_admits_aux v u (S ∪ T) F :=
begin
  induction F generalizing S,
  case formula.true_ : S h1
  {
    unfold fast_admits_aux,
    simp,
  },
  case formula.pred_ : X xs S h1
  {
    unfold fast_admits_aux at h1,
    simp at h1,

    unfold fast_admits_aux,
    simp,
    tauto,
  },
  case formula.not_ : phi phi_ih S h1
  {
    unfold fast_admits_aux at h1,

    unfold fast_admits_aux,
    tauto,
  },
  case formula.imp_ : phi psi phi_ih psi_ih S h1
  {
    unfold fast_admits_aux at h1,
    simp at h1,

    unfold fast_admits_aux,
    simp,
    tauto,
  },
  case formula.forall_ : x phi phi_ih S h1
  {
    unfold fast_admits_aux at h1,
    simp at h1,

    unfold fast_admits_aux,
    simp only [bool.of_to_bool_iff],
    cases h1,
    {
      tauto,
    },
    {
      right,
      simp only [finset.union_right_comm S T {x}],
      tauto,
    }
  },
end


lemma fast_admits_aux_del_binders
  (F : formula)
  (v u : var_name)
  (S T : finset var_name)
  (h1 : fast_admits_aux v u (S ∪ T) F) :
  fast_admits_aux v u S F :=
begin
  induction F generalizing S,
  case formula.true_ : S h1
  {
    unfold fast_admits_aux,
    simp,
  },
  case formula.pred_ : X xs S h1
  {
    unfold fast_admits_aux at h1,
    simp at h1,

    unfold fast_admits_aux,
    simp,
    tauto,
  },
  case formula.not_ : phi phi_ih S h1
  {
    unfold fast_admits_aux at h1,

    unfold fast_admits_aux,
    tauto,
  },
  case formula.imp_ : phi psi phi_ih psi_ih S h1
  {
    unfold fast_admits_aux at h1,
    simp at h1,
    cases h1,

    unfold fast_admits_aux,
    simp,
    tauto,
  },
  case formula.forall_ : x phi phi_ih S h1
  {
    unfold fast_admits_aux at h1,
    simp only [finset.union_right_comm S T {x}] at h1,
    simp only [bool.of_to_bool_iff] at h1,

    unfold fast_admits_aux,
    simp,
    tauto,
  },
end

--

lemma fast_admits_aux_is_free_in
  (F : formula)
  (v u : var_name)
  (binders : finset var_name)
  (h1 : fast_admits_aux v u binders F)
  (h2 : is_free_in v F) :
  u ∉ binders :=
begin
  induction F generalizing binders,
  case formula.true_ : binders h1
  {
    unfold is_free_in at h2,

    contradiction,
  },
  case formula.pred_ : X xs binders h1
  {
    unfold fast_admits_aux at h1,
    simp at h1,

    unfold is_free_in at h2,
    simp at h2,

    tauto,
  },
  case formula.not_ : phi phi_ih binders h1
  {
    unfold fast_admits_aux at h1,

    unfold is_free_in at h2,

    exact phi_ih h2 binders h1,
  },
  case formula.imp_ : phi psi phi_ih psi_ih binders h1
  {
    unfold fast_admits_aux at h1,
    simp at h1,
    cases h1,

    unfold is_free_in at h2,
    simp at h2,

    cases h2,
    {
      exact phi_ih h2 binders h1_left,
    },
    {
      exact psi_ih h2 binders h1_right,
    }
  },
  case formula.forall_ : x phi phi_ih binders h1
  {
    unfold fast_admits_aux at h1,
    simp at h1,

    unfold is_free_in at h2,
    simp at h2,
    cases h2,

    apply phi_ih h2_right,
    {
      cases h1,
      {
        contradiction,
      },
      {
        apply fast_admits_aux_del_binders phi v u binders {x} h1,
      }
    }
  },
end


lemma fast_admits_aux_mem_binders
  (F : formula)
  (v u : var_name)
  (binders : finset var_name)
  (h1 : fast_admits_aux v u binders F)
  (h2 : u ∈ binders) :
  ¬ is_free_in v F :=
begin
  contrapose! h2,
  exact fast_admits_aux_is_free_in F v u binders h1 h2,
end


--


lemma fast_admits_aux_imp_free_and_bound_unchanged
  (F : formula)
  (v u : var_name)
  (binders : finset var_name)
  (h1 : v ∉ binders)
  (h2 : fast_admits_aux v u binders F) :
  to_is_bound_aux binders F = to_is_bound_aux binders (fast_replace_free v u F) :=
begin
  induction F generalizing binders,
  case formula.true_ : binders h1 h2
  {
    refl,
  },
  case formula.pred_ : X xs binders h1 h2
  {
    induction xs,
    case list.nil
    {
      unfold fast_replace_free,
      simp only [list.map_nil],
    },
    case list.cons : args_hd args_tl args_ih
    {
      unfold fast_admits_aux at h2,
      simp only [list.mem_cons_iff] at h2,
      simp at h2,

      unfold fast_admits_aux at args_ih,
      unfold fast_replace_free at args_ih,
      unfold to_is_bound_aux at args_ih,
      simp at args_ih,

      unfold fast_replace_free,
      unfold to_is_bound_aux,
      simp,

      split,
      {
        split_ifs,
        {
          subst h,
          tauto,
        },
        {
          refl,
        }
      },
      {
        tauto,
      }
    },
  },
  case formula.not_ : phi phi_ih binders h1 h2
  {
    unfold fast_admits_aux at h2,

    unfold fast_replace_free,
    unfold to_is_bound_aux,
    congr' 1,
    exact phi_ih binders h1 h2,
  },
  case formula.imp_ : phi psi phi_ih psi_ih binders h1 h2
  {
    unfold fast_admits_aux at h2,
    simp at h2,
    cases h2,

    unfold fast_replace_free,
    unfold to_is_bound_aux,
    congr' 1,
    {
      exact phi_ih binders h1 h2_left,
    },
    {
      exact psi_ih binders h1 h2_right,
    }
  },
  case formula.forall_ : x phi phi_ih binders h1 h2
  {
    unfold fast_admits_aux at h2,
    simp at h2,

    unfold fast_replace_free,
    split_ifs,
    {
      refl,
    },
    {
      unfold to_is_bound_aux,
      simp only [eq_self_iff_true, true_and],
      apply phi_ih,
      {
        simp only [finset.mem_union, finset.mem_singleton],
        tauto,
      },
      {
        tauto,
      }
    }
  },
end


lemma free_and_bound_unchanged_imp_fast_admits_aux
  (F : formula)
  (v u : var_name)
  (binders : finset var_name)
  (h1 : v ∉ binders)
  (h2 : to_is_bound_aux binders F = to_is_bound_aux binders (fast_replace_free v u F)) :
  fast_admits_aux v u binders F :=
begin
  induction F generalizing binders,
  case formula.true_ : binders h1 h2
  {
    unfold fast_admits_aux,
    simp,
  },
  case formula.pred_ : X xs binders h1 h2
  {
    induction xs,
    case list.nil
    {
      unfold fast_admits_aux,
      simp,
    },
    case list.cons : args_hd args_tl args_ih
    {
      unfold fast_replace_free at h2,
      unfold to_is_bound_aux at h2,
      simp at h2,
      cases h2,

      unfold fast_admits_aux at args_ih,
      unfold fast_replace_free at args_ih,
      unfold to_is_bound_aux at args_ih,
      simp at args_ih,

      unfold fast_admits_aux,
      simp,
      intros a1,
      cases a1,
      {
        subst a1,
        simp only [eq_self_iff_true, if_true] at h2_left,
        tauto,
      },
      {
        tauto,
      }
    },
  },
  case formula.not_ : phi phi_ih binders h1 h2
  {
    unfold fast_replace_free at h2,
    unfold to_is_bound_aux at h2,
    simp only at h2,

    unfold fast_admits_aux,
    exact phi_ih binders h1 h2,
  },
  case formula.imp_ : phi psi phi_ih psi_ih binders h1 h2
  {
    unfold fast_replace_free at h2,
    unfold to_is_bound_aux at h2,
    simp at h2,
    cases h2,

    unfold fast_admits_aux,
    simp,
    tauto,
  },
  case formula.forall_ : x phi phi_ih binders h1 h2
  {
    unfold fast_replace_free at h2,

    unfold fast_admits_aux,
    simp,
    split_ifs at h2,
    {
      left,
      exact h,
    },
    {
      right,
      apply phi_ih,
      {
        simp only [finset.mem_union, finset.mem_singleton],
        tauto,
      },
      {
        unfold to_is_bound_aux at h2,
        simp only [eq_self_iff_true, true_and] at h2,
        exact h2,
      }
    }
  },
end


example
  (F : formula)
  (v u : var_name) :
  fast_admits v u F ↔ to_is_bound F = to_is_bound (fast_replace_free v u F) :=
begin
  unfold fast_admits,
  unfold to_is_bound,
  split,
  {
    apply fast_admits_aux_imp_free_and_bound_unchanged,
    simp only [finset.not_mem_empty, not_false_iff],
  },
  {
    apply free_and_bound_unchanged_imp_fast_admits_aux,
    simp only [finset.not_mem_empty, not_false_iff],
  }
end


-- admits


lemma admits_aux_self
  (F : formula)
  (v : var_name)
  (binders : finset var_name) :
  admits_aux v v binders F :=
begin
  induction F generalizing binders,
  case fol.formula.true_ : binders
  {
    unfold admits_aux,
    simp,
  },
  case fol.formula.pred_ : X xs binders
  {
    unfold admits_aux,
    simp,
  },
  case fol.formula.not_ : phi phi_ih binders
  {
    unfold admits_aux,
    exact phi_ih binders,
  },
  case fol.formula.imp_ : phi psi phi_ih psi_ih binders
  {
    unfold admits_aux,
    simp,
    tauto,
  },
  case fol.formula.forall_ : x phi phi_ih binders
  {
    unfold admits_aux,
    tauto,
  },
end


theorem admits_self
  (F : formula)
  (v : var_name) :
  admits v v F :=
begin
  unfold admits,
  apply admits_aux_self,
end

--

lemma not_is_free_in_imp_admits_aux
  (F : formula)
  (v u : var_name)
  (binders : finset var_name)
  (h1 : ¬ is_free_in v F) :
  admits_aux v u binders F :=
begin
  induction F generalizing binders,
  case formula.true_ : binders
  {
    unfold admits_aux,
    simp,
  },
  case formula.pred_ : X xs binders
  {
    unfold is_free_in at h1,
    simp at h1,

    unfold admits_aux,
    simp,
    tauto,
  },
  case fol.formula.not_ : phi phi_ih binders
  {
    unfold is_free_in at h1,

    unfold admits_aux,
    exact phi_ih h1 binders,
  },
  case fol.formula.imp_ : phi psi phi_ih psi_ih binders
  {
    unfold is_free_in at h1,
    simp at h1,
    push_neg at h1,
    cases h1,

    unfold admits_aux,
    simp,
    split,
    {
      exact phi_ih h1_left binders,
    },
    {
      exact psi_ih h1_right binders,
    }
  },
  case formula.forall_ : x phi phi_ih binders
  {
    unfold is_free_in at h1,
    simp only [bool.of_to_bool_iff, not_and] at h1,

    unfold admits_aux,
    by_cases c1 : v = x,
    {
      apply mem_binders_imp_admits_aux,
      simp only [finset.mem_union, finset.mem_singleton],
      tauto,
    },
    {
      tauto,
    },
  },
end


theorem not_is_free_in_imp_admits
  (F : formula)
  (v u : var_name)
  (h1 : ¬ is_free_in v F) :
  admits v u F :=
begin
  unfold admits,
  apply not_is_free_in_imp_admits_aux,
  exact h1,
end

--

lemma not_is_bound_in_imp_admits_aux
  (F : formula)
  (v u : var_name)
  (binders : finset var_name)
  (h1 : ¬ is_bound_in u F)
  (h2 : u ∉ binders) :
  admits_aux v u binders F :=
begin
  induction F generalizing binders,
  case formula.true_ : binders h2
  {
    unfold admits_aux,
    simp,
  },
  case formula.pred_ : X xs binders h2
  {
    unfold admits_aux,
    simp,
    tauto,
  },
  case formula.not_ : phi phi_ih binders h2
  {
    unfold is_bound_in at h1,

    unfold admits_aux,
    tauto,
  },
  case formula.imp_ : phi psi phi_ih psi_ih binders h2
  {
    unfold is_bound_in at h1,
    simp at h1,

    unfold admits_aux,
    simp,
    tauto,
  },
  case formula.forall_ : x phi phi_ih binders h2
  {
    unfold is_bound_in at h1,
    simp at h1,
    push_neg at h1,
    cases h1,

    unfold admits_aux,
    apply phi_ih h1_right,
    simp only [finset.mem_union, finset.mem_singleton],
    tauto,
  },
end


theorem not_is_bound_in_imp_admits
  (F : formula)
  (v u : var_name)
  (h1 : ¬ is_bound_in u F) :
  admits v u F :=
begin
  unfold admits,
  apply not_is_bound_in_imp_admits_aux,
  {
    exact h1,
  },
  {
    simp only [finset.not_mem_empty, not_false_iff],
  }
end

--

lemma replace_free_aux_admits_aux
  (F : formula)
  (v t : var_name)
  (binders : finset var_name)
  (h1 : ¬ occurs_in t F) :
  admits_aux t v binders (replace_free_aux v t binders F) :=
begin
  induction F generalizing binders,
  case formula.true_ : binders
  {
    unfold replace_free_aux,
    unfold admits_aux,
    simp,
  },
  case formula.pred_ : X xs binders
  {
    unfold occurs_in at h1,
    simp only [list.mem_to_finset] at h1,
    simp at h1,

    unfold replace_free_aux,
    unfold admits_aux,
    simp only [list.mem_map, not_and, not_not, and_imp, forall_exists_index],
    simp only [bool.of_to_bool_iff],
    intros x a1 a2 a3,

    by_cases c1 : x = v ∧ x ∉ binders,
    {
      cases c1,
      subst c1_left,
      exact c1_right,
    },
    {
      simp only [if_neg c1] at a2,
      subst a2,
      contradiction,
    }
  },
  case formula.not_ : phi phi_ih binders
  {
    unfold occurs_in at h1,

    unfold replace_free_aux,
    unfold admits_aux,
    tauto,
  },
  case formula.imp_ : phi psi phi_ih psi_ih binders
  {
    unfold occurs_in at h1,
    simp at h1,

    unfold replace_free_aux,
    unfold admits_aux,
    simp,
    tauto,
  },
  case formula.forall_ : x phi phi_ih binders
  {
    unfold occurs_in at h1,
    simp at h1,

    unfold replace_free_aux,
    unfold admits_aux,
    tauto,
  },
end


theorem replace_free_admits
  (F : formula)
  (v t : var_name)
  (h1 : ¬ occurs_in t F) :
  admits t v (replace_free v t F) :=
begin
  unfold replace_free,
  unfold admits,
  apply replace_free_aux_admits_aux,
  exact h1,
end

--

lemma admits_aux_add_binders
  (F : formula)
  (v u : var_name)
  (S T : finset var_name)
  (h1 : admits_aux v u S F)
  (h2 : u ∉ T) :
  admits_aux v u (S ∪ T) F :=
begin
  induction F generalizing S,
  case formula.true_ : S h1
  {
    unfold admits_aux,
    simp,
  },
  case formula.pred_ : X xs S h1
  {
    unfold admits_aux at h1,
    simp at h1,

    unfold admits_aux,
    simp,
    tauto,
  },
  case formula.not_ : phi phi_ih S h1
  {
    unfold admits_aux at h1,

    unfold admits_aux,
    tauto,
  },
  case formula.imp_ : phi psi phi_ih psi_ih S h1
  {
    unfold admits_aux at h1,
    simp at h1,

    unfold admits_aux,
    simp,
    tauto,
  },
  case formula.forall_ : x phi phi_ih S h1
  {
    unfold admits_aux at h1,

    unfold admits_aux,
    simp only [finset.union_right_comm S T {x}],
    tauto,
  },
end


lemma admits_aux_del_binders
  (F : formula)
  (v u : var_name)
  (S T : finset var_name)
  (h1 : admits_aux v u (S ∪ T) F)
  (h2 : v ∉ T) :
  admits_aux v u S F :=
begin
  induction F generalizing S,
  case formula.true_ : S h1
  {
    unfold admits_aux,
    simp,
  },
  case formula.pred_ : X xs S h1
  {
    unfold admits_aux at h1,
    simp at h1,

    unfold admits_aux,
    simp,
    tauto,
  },
  case formula.not_ : phi phi_ih S h1
  {
    unfold admits_aux at h1,

    unfold admits_aux,
    tauto,
  },
  case formula.imp_ : phi psi phi_ih psi_ih S h1
  {
    unfold admits_aux at h1,
    simp at h1,
    cases h1,

    unfold admits_aux,
    simp,
    tauto,
  },
  case formula.forall_ : x phi phi_ih S h1
  {
    unfold admits_aux at h1,
    simp only [finset.union_right_comm S T {x}] at h1,

    unfold admits_aux,
    tauto,
  },
end


lemma admits_aux_is_free_in
  (F : formula)
  (v u : var_name)
  (binders : finset var_name)
  (h1 : admits_aux v u binders F)
  (h2 : is_free_in v F)
  (h3 : v ∉ binders) :
  u ∉ binders :=
begin
  induction F generalizing binders,
  case formula.true_ : binders h1
  {
    unfold is_free_in at h2,

    contradiction,
  },
  case formula.pred_ : X xs binders h1
  {
    unfold admits_aux at h1,
    simp at h1,

    unfold is_free_in at h2,
    simp at h2,

    tauto,
  },
  case formula.not_ : phi phi_ih binders h1
  {
    unfold admits_aux at h1,

    unfold is_free_in at h2,

    exact phi_ih h2 binders h1 h3,
  },
  case formula.imp_ : phi psi phi_ih psi_ih binders h1
  {
    unfold admits_aux at h1,
    simp at h1,
    cases h1,

    unfold is_free_in at h2,
    simp at h2,

    cases h2,
    {
      exact phi_ih h2 binders h1_left h3,
    },
    {
      exact psi_ih h2 binders h1_right h3,
    }
  },
  case formula.forall_ : x phi phi_ih binders h1
  {
    unfold admits_aux at h1,

    unfold is_free_in at h2,
    simp at h2,
    cases h2,

    apply phi_ih h2_right,
    {
      apply admits_aux_del_binders phi v u binders {x},
      {
        exact h1,
      },
      {
        simp only [finset.mem_singleton],
        exact h2_left,
      },
    },
    {
      exact h3,
    },
  },
end


/--
  is_free_sub F v t F' := True if and only if F' is the result of replacing in F each free occurrence of v by a free occurrence of t.
-/
inductive is_free_sub : formula → var_name → var_name → formula → Prop
| true_
  (v t : var_name) :
  is_free_sub true_ v t true_

| pred_
  (X : pred_name) (xs : list var_name)
  (v t : var_name) :
    is_free_sub (pred_ X xs) v t (pred_ X (xs.map (fun (x : var_name), if x = v then t else x)))

| not_
  (phi : formula)
  (v t : var_name)
  (phi' : formula) :
  is_free_sub phi v t phi' →
  is_free_sub phi.not_ v t phi'.not_

| imp_
  (phi psi : formula)
  (v t : var_name)
  (phi' psi' : formula) :
  is_free_sub phi v t phi' →
  is_free_sub psi v t psi' →
  is_free_sub (phi.imp_ psi) v t (phi'.imp_ psi')

| forall_not_free_in
  (x : var_name) (phi : formula)
  (v t : var_name) :
  ¬ is_free_in v (forall_ x phi) →
  is_free_sub (forall_ x phi) v t (forall_ x phi)

| forall_free_in
  (x : var_name) (phi : formula)
  (v t : var_name)
  (phi' : formula) :
  is_free_in v (forall_ x phi) →
  ¬ x = t →
  is_free_sub phi v t phi' →
  is_free_sub (forall_ x phi) v t (forall_ x phi')


lemma fast_admits_aux_and_fast_replace_free_imp_is_free_sub
  (F F' : formula)
  (v u : var_name)
  (binders : finset var_name)
  (h1 : fast_admits_aux v u binders F)
  (h2 : fast_replace_free v u F = F') :
  is_free_sub F v u F' :=
begin
  subst h2,
  induction F generalizing binders,
  case formula.true_ : binders h1
  {
    unfold fast_replace_free,
    apply is_free_sub.true_,
  },
  case formula.pred_ : X xs binders h1
  {
    unfold fast_replace_free,
    apply is_free_sub.pred_,
  },
  case formula.not_ : phi phi_ih binders h1
  {
    unfold fast_admits_aux at h1,

    apply is_free_sub.not_,
    exact phi_ih binders h1,
  },
  case formula.imp_ : phi psi phi_ih psi_ih binders h1
  {
    unfold fast_admits_aux at h1,
    squeeze_simp at h1,
    cases h1,

    apply is_free_sub.imp_,
    {
      exact phi_ih binders h1_left,
    },
    {
      exact psi_ih binders h1_right,
    }
  },
  case formula.forall_ : x phi phi_ih binders h1
  {
    unfold fast_admits_aux at h1,
    squeeze_simp at h1,

    unfold fast_replace_free,
    cases h1,
    {
      split_ifs,
      apply is_free_sub.forall_not_free_in,
      subst h1,
      unfold is_free_in,
      squeeze_simp,
    },
    {
      split_ifs,
      {
        apply is_free_sub.forall_not_free_in,
        subst h,
        unfold is_free_in,
        squeeze_simp,
      },
      {
        by_cases c1 : ↥(is_free_in v phi),
        {
          apply is_free_sub.forall_free_in,
          {
            unfold is_free_in,
            squeeze_simp,
            split,
            {
              exact h,
            },
            {
              exact c1,
            }
          },
          {
            obtain s1 := fast_admits_aux_is_free_in phi v u (binders ∪ {x}) h1 c1,
            simp only [finset.mem_union, finset.mem_singleton] at s1,
            push_neg at s1,
            cases s1,

            simp only [eq_comm],
            exact s1_right,
          },
          {
            exact phi_ih (binders ∪ {x}) h1,
          },
        },
        {
          have s1 : fast_replace_free v u phi = phi,
          apply not_free_in_fast_replace_free_self,
          exact c1,

          simp only [s1],
          apply is_free_sub.forall_not_free_in,
          unfold is_free_in,
          squeeze_simp,
          intros a1,
          squeeze_simp at c1,
          exact c1,
        },
      },
    },
  },
end


lemma is_free_sub_imp_fast_admits_aux
  (F : formula)
  (v u : var_name)
  (binders : finset var_name)
  (h1 : ∃ (F' : formula), is_free_sub F v u F')
  (h2 : u ∉ binders) :
  fast_admits_aux v u binders F :=
begin
  apply exists.elim h1,
  intros F' h1_1,
  clear h1,

  induction h1_1 generalizing binders,
  case is_free_sub.true_ : h1_1_v h1_1_t binders h2
  {
    unfold fast_admits_aux,
    squeeze_simp,
  },
  case is_free_sub.pred_ : h1_1_X h1_1_xs h1_1_v h1_1_t binders h2
  {
    unfold fast_admits_aux,
    squeeze_simp,
    intros a1,
    exact h2,
  },
  case is_free_sub.not_ : h1_1_phi h1_1_v h1_1_t h1_1_phi' h1_1_1 h1_1_ih binders h2
  {
    unfold fast_admits_aux,
    exact h1_1_ih binders h2,
  },
  case is_free_sub.imp_ : h1_1_phi h1_1_psi h1_1_v h1_1_t h1_1_phi' h1_1_psi' h1_1_1 h1_1_2 h1_1_ih_1 h1_1_ih_2 binders h2
  {
    unfold fast_admits_aux,
    squeeze_simp,
    split,
    {
      exact h1_1_ih_1 binders h2,
    },
    {
      exact h1_1_ih_2 binders h2,
    }
  },
  case is_free_sub.forall_not_free_in : h1_1_x h1_1_phi h1_1_v h1_1_t h1_1_1 binders h2
  {
    unfold is_free_in at h1_1_1,
    simp only [bool.of_to_bool_iff, not_and] at h1_1_1,

    unfold fast_admits_aux,
    squeeze_simp,
    by_cases c1 : h1_1_v = h1_1_x,
    {
      left,
      exact c1,
    },
    {
      right,
      apply not_is_free_in_imp_fast_admits_aux,
      exact h1_1_1 c1,
    },
  },
  case is_free_sub.forall_free_in : h1_1_x h1_1_phi h1_1_v h1_1_t h1_1_phi' h1_1_1 h1_1_2 h1_1_3 h1_1_ih binders h2
  {
    unfold is_free_in at h1_1_1,
    squeeze_simp at h1_1_1,
    cases h1_1_1,

    unfold fast_admits_aux,
    squeeze_simp,
    right,
    apply h1_1_ih,
    simp only [finset.mem_union, finset.mem_singleton],
    push_neg,
    split,
    {
      exact h2,
    },
    {
      simp only [ne_comm],
      exact h1_1_2,
    }
  },
end


lemma is_free_sub_imp_fast_replace_free
  (F F' : formula)
  (v u : var_name)
  (h1 : is_free_sub F v u F') :
  fast_replace_free v u F = F' :=
begin
  induction h1,
  case is_free_sub.true_ : h1_v h1_t
  {
    refl,
  },
  case is_free_sub.pred_ : h1_X h1_xs h1_v h1_t
  {
    unfold fast_replace_free,
  },
  case is_free_sub.not_ : h1_phi h1_v h1_t h1_phi' h1_1 h1_ih
  {
    unfold fast_replace_free,
    congr,
    exact h1_ih,
  },
  case is_free_sub.imp_ : h1_phi h1_psi h1_v h1_t h1_phi' h1_psi' h1_1 h1_2 h1_ih_1 h1_ih_2
  {
    unfold fast_replace_free,
    congr,
    {
      exact h1_ih_1,
    },
    {
      exact h1_ih_2,
    }
  },
  case is_free_sub.forall_not_free_in : h1_x h1_phi h1_v h1_t h1_1
  {
    unfold is_free_in at h1_1,
    simp only [bool.of_to_bool_iff, not_and] at h1_1,

    unfold fast_replace_free,
    split_ifs,
    {
      simp only [eq_self_iff_true, and_self],
    },
    {
      split,
      {
        refl,
      },
      {
        apply not_free_in_fast_replace_free_self,
        exact h1_1 h,
      }
    }
  },
  case is_free_sub.forall_free_in : h1_x h1_phi h1_v h1_t h1_phi' h1_1 h1_2 h1_3 h1_ih
  {
    unfold is_free_in at h1_1,
    squeeze_simp at h1_1,
    cases h1_1,

    unfold fast_replace_free,
    split_ifs,
    split,
    {
      refl,
    },
    {
      exact h1_ih,
    }
  },
end


example
  (F F' : formula)
  (v u : var_name) :
  is_free_sub F v u F' ↔
    (fast_admits v u F ∧ fast_replace_free v u F = F') :=
begin
  unfold fast_admits,
  split,
  {
    intros a1,
    split,
    {
      apply is_free_sub_imp_fast_admits_aux,
      {
        apply exists.intro F',
        exact a1,
      },
      {
        simp only [finset.not_mem_empty, not_false_iff],
      }
    },
    {
      apply is_free_sub_imp_fast_replace_free,
      exact a1,
    }
  },
  {
    intros a1,
    cases a1,
    exact fast_admits_aux_and_fast_replace_free_imp_is_free_sub F F' v u ∅ a1_left a1_right,
  }
end


/--
  Helper function for replace_free_fun.
-/
def replace_free_fun_aux (σ : var_name → var_name) : finset var_name → formula → formula
| _ true_ := true_
| binders (pred_ X xs) :=
    pred_
    X
    (xs.map (fun (x : var_name), if x ∈ binders then x else σ x))
| binders (not_ phi) := not_ (replace_free_fun_aux binders phi)
| binders (imp_ phi psi) :=
    imp_
    (replace_free_fun_aux binders phi)
    (replace_free_fun_aux binders psi)
| binders (forall_ x phi) :=
    forall_ x (replace_free_fun_aux (binders ∪ {x}) phi)


/--
  replace_free_fun σ F := The simultaneous replacement of each free occurence of any variable v in the formula F by σ v.
-/
def replace_free_fun (σ : var_name → var_name) (F : formula) : formula := replace_free_fun_aux σ ∅ F


/--
  fast_replace_free_fun σ F := The simultaneous replacement of each free occurence of any variable v in the formula F by σ v.
-/
def fast_replace_free_fun : (var_name → var_name) → formula → formula
| _ true_ := true_
| σ (pred_ X xs) := pred_ X (xs.map σ)
| σ (not_ phi) := not_ (fast_replace_free_fun σ phi)
| σ (imp_ phi psi) := imp_ (fast_replace_free_fun σ phi) (fast_replace_free_fun σ psi)
| σ (forall_ x phi) := forall_ x (fast_replace_free_fun (function.update_ite σ x x) phi)



lemma fast_replace_free_fun_id
  (F : formula) :
  fast_replace_free_fun id F = F :=
begin
  induction F,
  case formula.true_
  {
    refl,
  },
  case formula.pred_ : X xs
  {
    unfold fast_replace_free_fun,
    simp only [list.map_id, eq_self_iff_true, and_self],
  },
  case formula.not_ : phi phi_ih
  {
    solve_by_elim,
  },
  case formula.imp_ : phi psi phi_ih psi_ih
  {
    unfold fast_replace_free_fun,
    congr,
    {
      exact phi_ih,
    },
    {
      exact psi_ih,
    }
  },
  case formula.forall_ : x phi phi_ih
  {
    unfold fast_replace_free_fun,
    simp only [eq_self_iff_true, true_and],
    simp only [function.update_ite_id],
    exact phi_ih,
  },
end


example
  (F : formula)
  (v t : var_name) :
  fast_replace_free_fun (function.update_ite id v t) F = fast_replace_free v t F :=
begin
  induction F,
  case formula.true_
  {
    refl,
  },
  case formula.pred_ : X xs
  {
    refl,
  },
  case formula.not_ : phi phi_ih
  {
    unfold fast_replace_free_fun,
    unfold fast_replace_free,
    congr,
    exact phi_ih,
  },
  case formula.imp_ : phi psi phi_ih psi_ih
  {
    unfold fast_replace_free_fun,
    unfold fast_replace_free,
    congr,
    {
      exact phi_ih,
    },
    {
      exact psi_ih,
    }
  },
  case formula.forall_ : x phi phi_ih
  {
    unfold fast_replace_free_fun,
    unfold fast_replace_free,
    split_ifs,
    {
      subst h,
      simp only [eq_self_iff_true, function.update_ite_idem, true_and],

      simp only [function.update_ite_id],
      apply fast_replace_free_fun_id,
    },
    {
      have s1 : (function.update_ite (function.update_ite (id : var_name → var_name) v t) x x) = function.update_ite id v t,
      funext,
      unfold function.update_ite,
      split_ifs,
      {
        subst h_1,
        tauto,
      },
      {
        subst h_1,
        simp only [id.def],
      },
      {
        refl,
      },
      {
        refl,
      },

      simp only [eq_self_iff_true, true_and],
      simp only [s1],
      exact phi_ih,
    }
  },
end


lemma fast_replace_free_fun_same_on_free
  (F : formula)
  (σ σ' : var_name → var_name)
  (h1 : ∀ (v : var_name), is_free_in v F → σ v = σ' v) :
  fast_replace_free_fun σ F =
    fast_replace_free_fun σ' F :=
begin
  induction F generalizing σ σ',
  case formula.true_ : σ σ' h1
  {
    unfold fast_replace_free_fun,
  },
  case formula.pred_ : X xs σ σ' h1
  {
    unfold is_free_in at h1,
    squeeze_simp at h1,

    unfold fast_replace_free_fun,
    congr' 1,
    simp only [list.map_eq_map_iff],
    intros x a1,
    exact h1 x a1,
  },
  case formula.not_ : phi phi_ih σ σ' h1
  {
    unfold is_free_in at h1,

    unfold fast_replace_free_fun,
    congr' 1,
    exact phi_ih σ σ' h1,
  },
  case formula.imp_ : phi psi phi_ih psi_ih σ σ' h1
  {
    unfold is_free_in at h1,
    squeeze_simp at h1,

    unfold fast_replace_free_fun,
    congr' 1,
    {
      apply phi_ih,
      intros v a1,
      apply h1,
      left,
      exact a1,
    },
    {
      apply psi_ih,
      intros v a1,
      apply h1,
      right,
      exact a1,
    },
  },
  case formula.forall_ : x phi phi_ih σ σ' h1
  {
    unfold fast_replace_free_fun,
    congr' 1,
    apply phi_ih,
    intros v a1,
    unfold function.update_ite,
    split_ifs,
    {
      refl,
    },
    {
      apply h1,
      unfold is_free_in,
      squeeze_simp,
      split,
      {
        exact h,
      },
      {
        exact a1,
      }
    }
  },
end


lemma replace_free_fun_aux_same_on_free
  (F : formula)
  (σ σ' : var_name → var_name)
  (binders : finset var_name)
  (h1 : ∀ (v : var_name), v ∉ binders → σ v = σ' v) :
  replace_free_fun_aux σ binders F =
    replace_free_fun_aux σ' binders F :=
begin
  induction F generalizing binders,
  case formula.true_ : binders h1
  {
    refl,
  },
  case formula.pred_ : X xs binders h1
  {
    unfold replace_free_fun_aux,
    congr' 1,
    simp only [list.map_eq_map_iff],
    intros x a1,
    split_ifs,
    {
      refl,
    },
    {
      exact h1 x h,
    }
  },
  case formula.not_ : phi phi_ih binders h1
  {
    unfold replace_free_fun_aux,
    congr' 1,
    exact phi_ih binders h1,
  },
  case formula.imp_ : phi psi phi_ih psi_ih binders h1
  {
    unfold replace_free_fun_aux,
    congr' 1,
    {
      exact phi_ih binders h1,
    },
    {
      exact psi_ih binders h1,
    }
  },
  case formula.forall_ : x phi phi_ih binders h1
  {
    unfold replace_free_fun_aux,
    congr' 1,
    apply phi_ih,
    intros v a1,
    simp only [finset.mem_union, finset.mem_singleton] at a1,
    push_neg at a1,
    cases a1,
    apply h1 v a1_left,
  },
end


example
  (F : formula)
  (σ : var_name → var_name)
  (binders : finset var_name)
  (h1 : ∀ (v : var_name), v ∈ binders → v = σ v) :
  replace_free_fun_aux σ binders F =
    fast_replace_free_fun σ F :=
begin
  induction F generalizing binders σ,
  case formula.true_ : binders h1
  {
    refl,
  },
  case formula.pred_ : X xs binders σ h1
  {
    unfold fast_replace_free_fun,
    unfold replace_free_fun_aux,
    congr' 1,
    simp only [list.map_eq_map_iff],
    intros x a1,
    split_ifs,
    {
      exact h1 x h,
    },
    {
      refl,
    }
  },
  case formula.not_ : phi phi_ih binders σ h1
  {
    unfold fast_replace_free_fun,
    unfold replace_free_fun_aux,
    congr,
    exact phi_ih binders σ h1,
  },
  case formula.imp_ : phi psi phi_ih psi_ih binders σ h1
  {
    unfold fast_replace_free_fun,
    unfold replace_free_fun_aux,
    congr,
    {
      exact phi_ih binders σ h1,
    },
    {
      exact psi_ih binders σ h1,
    }
  },
  case formula.forall_ : x phi phi_ih binders σ h1
  {
    unfold fast_replace_free_fun,
    unfold replace_free_fun_aux,
    congr,

    rewrite replace_free_fun_aux_same_on_free phi σ (function.update_ite σ x x),

    apply phi_ih,
    {
      intros v a1,
      unfold function.update_ite,
      split_ifs,
      {
        exact h,
      },
      {
        simp only [finset.mem_union, finset.mem_singleton] at a1,
        tauto,
      },
    },
    {
      simp only [finset.mem_union, finset.mem_singleton, eq_self_iff_true, or_true],
      push_neg,
      intros v a1,
      cases a1,
      unfold function.update_ite,
      split_ifs,
      {
        contradiction,
      },
      {
        refl,
      },
    }
  },
end


#lint

end fol
