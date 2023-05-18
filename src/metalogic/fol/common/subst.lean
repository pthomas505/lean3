import .binders
import metalogic.fol.aux.misc_list
import metalogic.fol.aux.function_update_ite
import .semantics

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
    simp at h1,
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
    simp at h1,

    unfold fast_replace_free,
    cases h1,
    {
      split_ifs,
      apply is_free_sub.forall_not_free_in,
      subst h1,
      unfold is_free_in,
      simp,
    },
    {
      split_ifs,
      {
        apply is_free_sub.forall_not_free_in,
        subst h,
        unfold is_free_in,
        simp,
      },
      {
        by_cases c1 : ↥(is_free_in v phi),
        {
          apply is_free_sub.forall_free_in,
          {
            unfold is_free_in,
            simp,
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
          simp,
          intros a1,
          simp at c1,
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
    simp,
  },
  case is_free_sub.pred_ : h1_1_X h1_1_xs h1_1_v h1_1_t binders h2
  {
    unfold fast_admits_aux,
    simp,
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
    simp,
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
    simp,
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
    simp at h1_1_1,
    cases h1_1_1,

    unfold fast_admits_aux,
    simp,
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
    simp at h1_1,
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


lemma substitution_theorem_aux
  {D : Type}
  (I : interpretation D)
  (V V' : valuation D)
  (v t : var_name)
  (binders : finset var_name)
  (F : formula)
  (h1 : fast_admits_aux v t binders F)
  (h2 : ∀ (v : var_name), ¬ v ∈ binders → V' v = V v) :
  holds D I (function.update_ite V v (V' t)) F ↔
    holds D I V (fast_replace_free v t F) :=
begin
  induction F generalizing binders V,
  case fol.formula.true_ : binders V h1 h2
  {
    unfold fast_replace_free,
    unfold holds,
  },
  case formula.pred_ : X xs binders V h1
  {
    unfold fast_admits_aux at h1,
    squeeze_simp at h1,

    unfold fast_replace_free,
    unfold holds,
    congr' 2,
    squeeze_simp,
    simp only [list.map_eq_map_iff],
    intros x a1,
    unfold function.update_ite,
    squeeze_simp,
    split_ifs,
    {
      subst h,
      apply h2,
      exact h1 a1,
    },
    {
      refl,
    }
  },
  case formula.not_ : phi phi_ih binders V h1
  {
    unfold fast_admits_aux at h1,

    unfold fast_replace_free,
    unfold holds,
    apply not_congr,
    apply phi_ih binders,
    exact h1,
    exact h2,
  },
  case formula.imp_ : phi psi phi_ih psi_ih binders V h1
  {
    unfold fast_admits_aux at h1,
    squeeze_simp at h1,
    cases h1,

    unfold fast_replace_free,
    unfold holds,
    apply imp_congr,
    {
      apply phi_ih binders,
      exact h1_left,
      exact h2,
    },
    {
      apply psi_ih binders,
      exact h1_right,
      exact h2,
    }
  },
  case formula.forall_ : x phi phi_ih binders V h1
  {
    unfold fast_admits_aux at h1,
    squeeze_simp at h1,

    unfold fast_replace_free,
    split_ifs,
    {
      unfold holds,
      apply forall_congr,
      intros d,
      subst h,
      congr' 2,
      funext,
      unfold function.update_ite,
      split_ifs;
      refl,
    },
    {
      unfold holds,
      apply forall_congr,
      intros d,
      specialize phi_ih (binders ∪ {x}),

      rewrite <- phi_ih,
      congr' 2,
      funext,
      unfold function.update_ite,
      split_ifs,
      subst h_1,
      subst h_2,
      contradiction,
      refl,
      refl,
      refl,
      cases h1,
      contradiction,
      exact h1,
      unfold function.update_ite,
      intros a,
      split_ifs,
      cases h1,
      contradiction,
      subst h_1,
      simp only [finset.mem_union, finset.mem_singleton, eq_self_iff_true, or_true, not_true, is_empty.forall_iff],
      intros a1,
      apply h2,
      simp only [finset.mem_union, finset.mem_singleton] at a1,
      push_neg at a1,
      cases a1,
      exact a1_left,
    }
  },
end


theorem substitution_theorem
  {D : Type}
  (I : interpretation D)
  (V : valuation D)
  (v t : var_name)
  (F : formula)
  (h1 : fast_admits v t F) :
  holds D I (function.update_ite V v (V t)) F ↔
    holds D I V (fast_replace_free v t F) :=
begin
  unfold fast_admits at h1,
  apply substitution_theorem_aux,
  exact h1,
  simp only [finset.not_mem_empty, not_false_iff, eq_self_iff_true, forall_const],
end


example
  (v t : var_name)
  (F : formula)
  (h1 : fast_admits v t F)
  (h2 : F.is_valid) :
  (fast_replace_free v t F).is_valid :=
begin
  unfold formula.is_valid at h2,

  unfold formula.is_valid,
  intros D I V,
  rewrite <- substitution_theorem,
  apply h2,
  exact h1,
end


theorem substitution_theorem_ind
  {D : Type}
  (I : interpretation D)
  (V : valuation D)
  (v t : var_name)
  (F F' : formula)
  (h1 : is_free_sub F v t F') :
  holds D I (function.update_ite V v (V t)) F ↔
    holds D I V F' :=
begin
  induction h1 generalizing V,
  case fol.is_free_sub.true_ : h1_v h1_t V
  {
    unfold holds,
  },
  case is_free_sub.pred_ : h1_X h1_xs h1_v h1_t
  {
    unfold holds,
    congr' 2,
    simp only [list.map_map],
    simp only [list.map_eq_map_iff],
    intros x a1,
    unfold function.update_ite,
    split_ifs,
    {
      squeeze_simp,
      simp only [if_pos h],
    },
    {
      squeeze_simp,
      simp only [if_neg h],
    }
  },
  case is_free_sub.not_ : h1_phi h1_v h1_t h1_phi' h1_1 h1_ih
  {
    unfold holds,
    apply not_congr,
    apply h1_ih,
  },
  case is_free_sub.imp_ : h1_phi h1_psi h1_v h1_t h1_phi' h1_psi' h1_1 h1_2 h1_ih_1 h1_ih_2
  {
    unfold holds,
    apply imp_congr,
    apply h1_ih_1,
    apply h1_ih_2,
  },
  case is_free_sub.forall_not_free_in : h1_x h1_phi h1_v h1_t h1_1
  {
    unfold is_free_in at h1_1,
    squeeze_simp at h1_1,

    unfold holds,
    apply forall_congr,
    intros d,
    apply holds_congr_var,
    intros x a1,
    unfold function.update_ite,
    split_ifs,
    refl,
    subst h_1,
    specialize h1_1 h,
    rewrite h1_1 at a1,
    contradiction,
    refl,
  },
  case is_free_sub.forall_free_in : h1_x h1_phi h1_v h1_t h1_phi' h1_1 h1_2 h1_3 h1_ih
  {
    unfold is_free_in at h1_1,
    squeeze_simp at h1_1,
    cases h1_1,

    unfold holds,
    apply forall_congr,
    intros d,

    specialize h1_ih (function.update_ite V h1_x d),

    rewrite <- h1_ih,
    apply holds_congr_var,
    intros x a1,
    funext,
    unfold function.update_ite,
    split_ifs,
    refl,
    subst h_1,
    contradiction,
    refl,
    subst h_2,
    contradiction,
    refl,
    refl,
  },
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
    simp at h1,

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
    simp at h1,

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
      simp,
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


@[derive decidable]
def admits_fun_aux (σ : var_name → var_name) :
  finset var_name → formula → bool
| _ true_ := tt
| binders (pred_ X xs) :=
    ∀ (v : var_name), v ∈ xs → v ∉ binders → σ v ∉ binders 
| binders (not_ phi) := admits_fun_aux binders phi
| binders (imp_ phi psi) := admits_fun_aux binders phi ∧ admits_fun_aux binders psi
| binders (forall_ x phi) := admits_fun_aux (binders ∪ {x}) phi

@[derive decidable]
def admits_fun (σ : var_name → var_name) (phi : formula) : bool :=
  admits_fun_aux σ ∅ phi


lemma substitution_fun_theorem_aux
  {D : Type}
  (I : interpretation D)
  (V V' : valuation D)
  (σ σ' : var_name → var_name)
  (binders : finset var_name)
  (F : formula)
  (h1 : admits_fun_aux σ binders F)
  (h2 : ∀ (v : var_name), v ∈ binders ∨ σ' v ∉ binders → (V v = V' (σ' v)))
  (h2' : ∀ (v : var_name), v ∈ binders → v = σ' v)
  (h3 : ∀ (v : var_name), v ∉ binders → σ' v = σ v) :
  holds D I V F ↔
    holds D I V' (fast_replace_free_fun σ' F) :=
begin
  induction F generalizing binders V V' σ σ',
  case formula.true_ : binders V V' σ σ' h1 h2 h2' h3
  {
    unfold fast_replace_free_fun,
    unfold holds,
  },
  case formula.pred_ : X xs binders V V' σ σ' h1 h2 h2' h3
  {
    unfold admits_fun_aux at h1,
    simp only [bool.of_to_bool_iff] at h1,

    unfold fast_replace_free_fun,
    unfold holds,
    congr' 2,
    simp only [list.map_map],
    simp only [list.map_eq_map_iff],
    intros v a1,
    apply h2,
    by_cases c1 : v ∈ binders,
    {
      left,
      exact c1,
    },
    {
      right,
      simp only [h3 v c1],
      exact h1 v a1 c1,
    }
  },
  case formula.not_ : phi phi_ih binders V V' σ σ' h1 h2 h2' h3
  {
    unfold admits_fun_aux at h1,

    unfold fast_replace_free_fun,
    unfold holds,
    apply not_congr,
    exact phi_ih binders V V' σ σ' h1 h2 h2' h3,
  },
  case formula.imp_ : phi psi phi_ih psi_ih binders V V' σ σ' h1 h2 h2' h3
  {
    unfold admits_fun_aux at h1,
    simp only [bool.of_to_bool_iff] at h1,
    cases h1,

    unfold holds,
    apply imp_congr,
    {
      exact phi_ih binders V V' σ σ' h1_left h2 h2' h3,
    },
    {
      exact psi_ih binders V V' σ σ' h1_right h2 h2' h3,
    }
  },
  case formula.forall_ : x phi phi_ih binders V V' σ σ' h1 h2 h2' h3
  {
    unfold admits_fun_aux at h1,

    unfold fast_replace_free_fun,
    unfold holds,
    apply forall_congr,
    intros d,

    apply phi_ih (binders ∪ {x}) (function.update_ite V x d) (function.update_ite V' x d) σ (function.update_ite σ' x x) h1,
    {
      intros v a1,
      unfold function.update_ite at a1,
      simp only [finset.mem_union, finset.mem_singleton, ite_eq_left_iff] at a1,
      push_neg at a1,

      unfold function.update_ite,
      split_ifs,
      {
        refl,
      },
      {
        subst h_1,
        tauto,
      },
      {
        simp only [if_neg h] at a1,
        apply h2,
        tauto,
      },
    },
    {
      intros v a1,
      simp only [finset.mem_union, finset.mem_singleton] at a1,

      unfold function.update_ite,
      split_ifs,
      {
        exact h,
      },
      {
        tauto,
      },
    },
    {
      intros v a1,
      simp only [finset.mem_union, finset.mem_singleton] at a1,
      push_neg at a1,
      cases a1,
      unfold function.update_ite,
      simp only [if_neg a1_right],
      exact h3 v a1_left,
    },
  },
end


theorem substitution_fun_theorem
  {D : Type}
  (I : interpretation D)
  (V : valuation D)
  (σ : var_name → var_name)
  (F : formula)
  (h1 : admits_fun σ F) :
  holds D I (V ∘ σ) F ↔
    holds D I V (fast_replace_free_fun σ F) :=
begin
  apply substitution_fun_theorem_aux I (V ∘ σ) V σ σ ∅ F h1,
  {
    simp only [finset.not_mem_empty, not_false_iff, false_or, eq_self_iff_true, forall_const],
  },
  {
    simp only [finset.not_mem_empty, is_empty.forall_iff, forall_const],
  },
  {
    simp only [finset.not_mem_empty, not_false_iff, eq_self_iff_true, forall_const],
  },
end


theorem substitution_fun_valid
  (σ : var_name → var_name)
  (F : formula)
  (h1 : admits_fun σ F)
  (h2 : F.is_valid) :
  (fast_replace_free_fun σ F).is_valid :=
begin
  unfold formula.is_valid at h2,

  unfold formula.is_valid,
  intros D I V,
  rewrite <- substitution_fun_theorem I V σ F h1,
  exact h2 D I (V ∘ σ),
end


-- proposition substitution

/--
  The recursive simultaneous uniform substitution of all of the propositional variables in a formula.
-/
def replace_prop_fun
  (τ : pred_name → pred_name) : formula → formula
| true_ := true_
| (pred_ P ts) := ite (ts = list.nil) (pred_ (τ P) list.nil) (pred_ P ts)
| (not_ phi) := not_ (replace_prop_fun phi)
| (imp_ phi psi) := imp_ (replace_prop_fun phi) (replace_prop_fun psi)
| (forall_ x phi) := forall_ x (replace_prop_fun phi)


lemma prop_sub_aux
  (D : Type)
  (I : interpretation D)
  (V : valuation D)
  (τ : pred_name → pred_name)
  (F : formula) :
  holds D I V (replace_prop_fun τ F) ↔
    holds D
    ⟨
      I.nonempty,
      fun (P : pred_name) (xs : list D),
        if (xs = list.nil) = tt
        then holds D I V (pred_ (τ P) list.nil)
        else I.pred P xs
    ⟩
    V F :=
begin
  induction F generalizing V,
  case formula.true_ : V
  {
    unfold replace_prop_fun,
    unfold holds,
  },
  case formula.pred_ : X xs V
  {
    unfold replace_prop_fun,
    split_ifs,
    {
      unfold holds,
      simp only [list.map_nil, list.map_eq_nil],
      simp only [coe_sort_tt, eq_iff_iff, iff_true],
      simp only [if_pos h],
    },
    {
      unfold holds,
      simp only [list.map_eq_nil, list.map_nil],
      simp only [coe_sort_tt, eq_iff_iff, iff_true],
      simp only [if_neg h],
    }
  },
  case formula.not_ : phi phi_ih V
  {
    unfold replace_prop_fun,
    unfold holds,
    apply not_congr,
    apply phi_ih,
  },
  case formula.imp_ : phi psi phi_ih psi_ih V
  {
    unfold replace_prop_fun,
    unfold holds,
    apply imp_congr,
    {
      apply phi_ih,
    },
    {
      apply psi_ih,
    }
  },
  case formula.forall_ : x phi phi_ih V
  {
    unfold replace_prop_fun,
    unfold holds,
    apply forall_congr,
    intros d,
    apply phi_ih,
  },
end


theorem prop_sub_is_valid
  (phi : formula)
  (h1 : phi.is_valid)
  (τ : pred_name → pred_name) :
  (replace_prop_fun τ phi).is_valid :=
begin
  unfold formula.is_valid at h1,

  unfold formula.is_valid,
  intros D I V,
  simp only [prop_sub_aux D I V τ phi],
  apply h1,
end


-- predicate substitution

-- single

-- https://math.stackexchange.com/a/1374989

/--
  The recursive simultaneous uniform substitution of a single predicate variable in a formula.
-/
def replace_pred
  (P : pred_name) (zs : list var_name) (H : formula) : formula → formula
| true_ := true_
| (pred_ X ts) :=
  if X = P ∧ ts.length = zs.length
  then
  fast_replace_free_fun
    (function.update_list_ite id zs ts) H
  else pred_ X ts
| (not_ phi) := not_ (replace_pred phi)
| (imp_ phi psi) := imp_ (replace_pred phi) (replace_pred psi)
| (forall_ x phi) := forall_ x (replace_pred phi)


@[derive decidable]
def admits_pred_aux (P : pred_name) (zs : list var_name) (H : formula) : finset var_name → formula → bool
| _ true_ := tt
| binders (pred_ X ts) :=
  if X = P ∧ ts.length = zs.length
  then
  (admits_fun (function.update_list_ite id zs ts) H) ∧

  /-
    Suppose F is the formula that the predicate X ts occurs in.
    Ensures that the free variables in H that are not being replaced by a variable in ts do not become bound variables in F. The bound variables in F are in the 'binders' set.
    The zs are the free variables in H that are being replaced by the variables in ts.
   (is_free_in x H ∧ x ∉ zs) := x is a free variable in H that is not being replaced by a variable in ts.
  -/
  (∀ (x : var_name), x ∈ binders → ¬ (is_free_in x H ∧ x ∉ zs))
  else true
| binders (not_ phi) := admits_pred_aux binders phi
| binders (imp_ phi psi) := admits_pred_aux binders phi ∧ admits_pred_aux binders psi
| binders (forall_ x phi) := admits_pred_aux (binders ∪ {x}) phi


lemma pred_sub_single_aux
  (D : Type)
  (I : interpretation D)
  (V V' : valuation D)
  (F : formula)
  (P : pred_name)
  (zs : list var_name)
  (H : formula)
  (binders : finset var_name)
  (h1 : admits_pred_aux P zs H binders F)
  (h2 : ∀ (x : var_name), x ∉ binders → V x = V' x) :
  holds
    D
    ⟨
      I.nonempty,
      fun (Q : pred_name) (ds : list D),
      if Q = P ∧ ds.length = zs.length
      then holds D I (function.update_list_ite V' zs ds) H
      else I.pred Q ds
    ⟩
    V F ↔
    holds D I V (replace_pred P zs H F) :=
begin
  induction F generalizing binders V,
  case formula.true_ : binders V h1 h2
  {
    unfold replace_pred,
    unfold holds,
  },
  case formula.pred_ : X xs binders V h1 h2
  {
    unfold admits_pred_aux at h1,

    unfold replace_pred,
    unfold holds,
    simp only [list.length_map],

    split_ifs at h1,
    {
      simp only [not_and, not_not, bool.of_to_bool_iff] at h1,
      cases h1,
      unfold admits_fun at h1_left,

      split_ifs,

      obtain s1 := substitution_fun_theorem I V (function.update_list_ite id zs xs) H h1_left,
      simp only [function.update_list_ite_comp] at s1,
      simp only [function.comp.right_id] at s1,

      have s2 : holds D I (function.update_list_ite V zs (list.map V xs)) H ↔ holds D I (function.update_list_ite V' zs (list.map V xs)) H,
      {
        apply holds_congr_var,
        intros v a1,
        by_cases c1 : v ∈ zs,
        {
          specialize h2 v,
          apply function.update_list_ite_mem_eq_len V V' v zs (list.map V xs) c1,
          cases h,
          simp only [list.length_map],
          symmetry,
          exact h_right,
        },
        {
          by_cases c2 : v ∈ binders,
          {
            specialize h1_right v c2 a1,
            contradiction,
          },
          {
            specialize h2 v c2,
            apply function.update_list_ite_mem',
            exact h2,
          },
        },
      },

      simp only [s2] at s1,
      exact s1,
    },
    {
      split_ifs,
      unfold holds,
    }
  },
  case formula.not_ : phi phi_ih binders V h1 h2
  {
    unfold admits_pred_aux at h1,

    unfold replace_pred,
    unfold holds,
    apply not_congr,
    exact phi_ih binders V h1 h2,
  },
  case formula.imp_ : phi psi phi_ih psi_ih binders V h1 h2
  {
    unfold admits_pred_aux at h1,
    simp only [bool.of_to_bool_iff] at h1,
    cases h1,

    unfold replace_pred,
    unfold holds,
    apply imp_congr,
    {
      exact phi_ih binders V h1_left h2,
    },
    {
      exact psi_ih binders V h1_right h2,
    },
  },
  case formula.forall_ : x phi phi_ih binders V h1 h2
  {
    unfold admits_pred_aux at h1,

    unfold replace_pred,
    unfold holds,
    apply forall_congr,
    intros d,
    apply phi_ih (binders ∪ {x}) (function.update_ite V x d) h1,
    intros v a1,
    unfold function.update_ite,
    simp only [finset.mem_union, finset.mem_singleton] at a1,
    push_neg at a1,
    cases a1,
    simp only [if_neg a1_right],
    exact h2 v a1_left,
  },
end


theorem pred_sub_single_valid
  (phi : formula)
  (P : pred_name)
  (zs : list var_name)
  (H : formula)
  (h1 : admits_pred_aux P zs H ∅ phi)
  (h2 : phi.is_valid) :
  (replace_pred P zs H phi).is_valid :=
begin
  unfold formula.is_valid at h2,

  unfold formula.is_valid,
  intros D I V,

  obtain s1 := pred_sub_single_aux D I V V phi P zs H ∅ h1,
  simp only [eq_self_iff_true, forall_const] at s1,

  rewrite <- s1,
  apply h2,
end


/--
  The inductive simultaneous uniform substitution of a single predicate variable in a formula.

  is_pred_sub A P zs H B := The formula A is said to be transformed into the formula B by a substitution of H* for P z₁ ... zₙ, abbreviated: Sub A (P zⁿ / H*) B, iff B is obtained from A upon replacing in A each occurrence of a derivative of the name form P z₁ ... zₙ by the corresponding derivative of the substituend H*, provided that: (i) P does not occur in a component formula (∀ x A₁) of A if x is a parameter of H*, and (ii) the name variable zₖ, k = 1, ..., n, is not free in a component formula (∀ x H) of H* if P t₁ ... tₙ occurs in A with x occurring in tₖ. If conditions (i) and (ii) are not satisfied, then the indicated substitution for predicate variables is left undefined.
-/
inductive is_pred_sub (P : pred_name) (zs : list var_name) (H : formula) : formula → formula → Prop

| true_ :
  is_pred_sub true_ true_

/-
  If A is an atomic formula not containing P then Sub A (P zⁿ / H*) A.
-/
| pred_not_occurs_in
  (X : pred_name) (ts : list var_name) :
  ¬ (X = P ∧ ts.length = zs.length) →
  is_pred_sub (pred_ X ts) (pred_ X ts)

  /-
  If A = P t₁ ... tₙ and Sf H* (zⁿ / tⁿ) B, then Sub A (P zⁿ / H*) B.

  Sf H* (zⁿ / tⁿ) B :=
    admits_fun (function.update_list_ite id zs.to_list ts.to_list) H* ∧ 
    fast_replace_free_fun (function.update_list_ite id zs.to_list ts.to_list) H* = B
  -/
| pred_occurs_in
  (X : pred_name) (ts : list var_name) :
  X = P ∧ ts.length = zs.length →
  admits_fun (function.update_list_ite id zs ts) H →
  is_pred_sub (pred_ P ts) (fast_replace_free_fun (function.update_list_ite id zs ts) H)

/-
  If A = (¬ A₁) and Sub A₁ (P zⁿ / H*) B₁, then Sub A (P zⁿ / H*) (¬ B₁).
-/
| not_
  (phi : formula)
  (phi' : formula) :
  is_pred_sub phi phi' →
  is_pred_sub phi.not_ phi'.not_

/-
  If A = (A₁ → A₂), Sub A₁ (P zⁿ / H*) B₁, and Sub A₂ (P zⁿ / H*) B₂, then Sub A (P zⁿ / H*) (B₁ → B₁).
-/
| imp_
  (phi psi : formula)
  (phi' psi' : formula) :
  is_pred_sub phi phi' →
  is_pred_sub psi psi' →
  is_pred_sub (phi.imp_ psi) (phi'.imp_ psi')

/-
  If A = (∀ x A₁) and P does not occur in A then Sub A (P zⁿ / H*) A.

  If A = (∀ x A₁), P occurs in A, x is not free in H*, and Sub A₁ (P zⁿ / H*) B₁, then Sub A (P zⁿ / H*) (∀ x B₁).
-/
| forall_
  (x : var_name)
  (phi : formula)
  (phi' : formula) :
  ¬ is_free_in x H →
  is_pred_sub phi phi' →
  is_pred_sub (forall_ x phi) (forall_ x phi')


theorem is_pred_sub_theorem
  (D : Type)
  (I J : interpretation D)
  (V : valuation D)
  (A : formula)
  (P : pred_name)
  (zs : list var_name)
  (H : formula)
  (B : formula)
  (h1 : is_pred_sub P zs H A B)
  (h2 : ∀ (Q : pred_name) (ds : list D), (Q = P ∧ ds.length = zs.length) → (holds D I (function.update_list_ite V zs ds) H ↔ J.pred P ds))
  (h3 : ∀ (Q : pred_name) (ds : list D), ¬ (Q = P ∧ ds.length = zs.length) → (I.pred Q ds ↔ J.pred Q ds)) :
  holds D I V B ↔ holds D J V A :=
begin
  induction h1 generalizing V,
  case is_pred_sub.true_ : V h2
  {
    unfold holds,
  },
  case is_pred_sub.pred_not_occurs_in : h1_X h1_ts h1_1 V h2
  {
    simp only [not_and] at h1_1,

    apply coincidence_theorem,
    unfold coincide,
    split,
    {
      unfold pred.occurs_in,
      intros X ds a1,
      simp only [bool.of_to_bool_iff] at a1,
      cases a1,
      subst a1_left,
      apply h3,
      simp only [not_and],
      intros a2,
      subst a2,
      simp only [eq_self_iff_true, forall_true_left] at h1_1,
      intros contra,
      apply h1_1,
      exact eq.trans a1_right contra,
    },
    {
      simp only [eq_self_iff_true, implies_true_iff],
    }
  },
  case is_pred_sub.pred_occurs_in : h1_X h1_ts h1_1 h1_2 V h2
  {
    obtain s1 := substitution_fun_theorem I V (function.update_list_ite id zs h1_ts) H h1_2,

    obtain s2 := function.update_list_ite_comp id V zs h1_ts,

    simp only [s2] at s1,
    simp only [function.comp.right_id] at s1,

    unfold holds,
    specialize h2 h1_X (list.map V h1_ts),
    simp only [s1] at h2,
    apply h2,
    {
      simp only [list.length_map],
      exact h1_1,
    },
  },
  case is_pred_sub.not_ : h1_phi h1_phi' h1_1 h1_ih V h2
  {
    unfold holds,
    apply not_congr,
    exact h1_ih V h2,
  },
  case is_pred_sub.imp_ : h1_phi h1_psi h1_phi' h1_psi' h1_1 h1_2 h1_ih_1 h1_ih_2 V h2
  {
    unfold holds,
    apply imp_congr,
    {
      exact h1_ih_1 V h2,
    },
    {
      exact h1_ih_2 V h2,
    },
  },
  case is_pred_sub.forall_ : h1_x h1_phi h1_phi' h1_1 h1_2 h1_ih V h2
  {
    unfold holds,
    apply forall_congr,
    intros d,
    apply h1_ih,
    intros Q ds a1,
    specialize h2 Q ds a1,

    have s1 : holds D I (function.update_list_ite (function.update_ite V h1_x d) zs ds) H ↔ holds D I (function.update_list_ite V zs ds) H,
    {
      apply coincidence_theorem,
      unfold coincide,
      split,
      {
        simp only [eq_iff_iff, iff_self, implies_true_iff, forall_const],
      },
      {
        intros v a1,
        apply function.update_list_ite_update_ite,
        intros contra,
        subst contra,
        contradiction,
      }
    },

    simp only [h2] at s1,
    exact s1,
  },
end


theorem is_pred_sub_valid
  (phi phi' : formula)
  (P : pred_name)
  (zs : list var_name)
  (H : formula)
  (h1 : is_pred_sub P zs H phi phi')
  (h2 : phi.is_valid) :
  phi'.is_valid :=
begin
  unfold formula.is_valid at h2,

  unfold formula.is_valid,
  intros D I V,

  let J : interpretation D := {
    nonempty := I.nonempty,
    pred := fun (Q : pred_name) (ds : list D), ite (Q = P ∧ ds.length = zs.length) (holds D I (function.update_list_ite V zs ds) H) (I.pred Q ds)
  },

  obtain s1 := is_pred_sub_theorem D I J V phi P zs H phi' h1,
  simp only [eq_self_iff_true, true_and] at s1,

  have s2 : holds D I V phi' ↔ holds D J V phi,
  {
    apply s1,
    {
      intros Q ds a1,
      cases a1,
      simp only [if_pos a1_right],
    },
    {
      intros Q ds a1,
      simp only [if_neg a1],
    },
  },

  simp only [s2],
  apply h2,
end


-- multiple

/--
  The recursive simultaneous uniform substitution of all of the predicate variables in a formula.
-/
def replace_pred_fun
  (τ : pred_name → ℕ → list var_name × formula) : formula → formula
| true_ := true_
| (pred_ P ts) :=
  if ts.length = (τ P ts.length).fst.length
  then
  fast_replace_free_fun
    (function.update_list_ite id (τ P ts.length).fst ts) (τ P ts.length).snd
  else
  pred_ P ts
| (not_ phi) := not_ (replace_pred_fun phi)
| (imp_ phi psi) := imp_ (replace_pred_fun phi) (replace_pred_fun psi)
| (forall_ x phi) := forall_ x (replace_pred_fun phi)


@[derive decidable]
def admits_pred_fun_aux (τ : pred_name → ℕ → list var_name × formula) :
  finset var_name → formula → bool
| _ true_ := tt
| binders (pred_ P ts) :=
  (admits_fun (function.update_list_ite id (τ P ts.length).fst ts) (τ P ts.length).snd) ∧
 (∀ (x : var_name), x ∈ binders → ¬ (is_free_in x (τ P ts.length).snd ∧ x ∉ (τ P ts.length).fst)) ∧
  ts.length = (τ P ts.length).fst.length
| binders (not_ phi) := admits_pred_fun_aux binders phi
| binders (imp_ phi psi) := admits_pred_fun_aux binders phi ∧ admits_pred_fun_aux binders psi
| binders (forall_ x phi) := admits_pred_fun_aux (binders ∪ {x}) phi


lemma pred_sub_aux
  (D : Type)
  (I : interpretation D)
  (V V' : valuation D)
  (τ : pred_name → ℕ → list var_name × formula)
  (binders : finset var_name)
  (F : formula)
  (h1 : admits_pred_fun_aux τ binders F)
  (h2 : ∀ (x : var_name), x ∉ binders → V x = V' x) :
  holds
    D
    ⟨
      I.nonempty,
      fun (P : pred_name) (ds : list D),
      if ds.length = (τ P ds.length).fst.length
      then holds D I (function.update_list_ite V' (τ P ds.length).fst ds) (τ P ds.length).snd
      else I.pred P ds
    ⟩
    V F ↔
    holds D I V (replace_pred_fun τ F) :=
begin
  induction F generalizing binders V,
  case formula.true_ : binders V h1 h2
  {
    unfold replace_pred_fun,
    unfold holds,
  },
  case formula.pred_ : X xs binders V h1 h2
  {
    unfold admits_pred_fun_aux at h1,
    simp only [not_and, not_not, bool.of_to_bool_iff] at h1,
    cases h1,
    cases h1_right,

    obtain s1 := substitution_fun_theorem I V (function.update_list_ite id (τ X xs.length).fst xs) (τ X xs.length).snd h1_left,
    simp only [function.update_list_ite_comp] at s1,
    simp only [function.comp.right_id] at s1,

    have s2 : holds D I (function.update_list_ite V (τ X xs.length).fst (list.map V xs)) (τ X xs.length).snd ↔ holds D I (function.update_list_ite V' (τ X xs.length).fst (list.map V xs)) (τ X xs.length).snd,
    {
      apply holds_congr_var,

      intros v a1,
      by_cases c1 : v ∈ (τ X xs.length).fst,
      {
        apply function.update_list_ite_mem_eq_len V V' v (τ X xs.length).fst (list.map V xs) c1,
        simp only [list.length_map],
        symmetry,
        exact h1_right_right,
      },
      {
        by_cases c2 : v ∈ binders,
        {
          specialize h1_right_left v c2 a1,
          contradiction,
        },
        {
          specialize h2 v c2,
          apply function.update_list_ite_mem',
          exact h2,
        },
      },
    },

    simp only [s2] at s1,
    clear s2,

    unfold holds,
    unfold replace_pred_fun,
    simp only [list.length_map],
    split_ifs,
    exact s1,
  },
  case formula.not_ : phi phi_ih binders V h1 h2
  {
    unfold admits_pred_fun_aux at h1,

    unfold replace_pred_fun,
    unfold holds,
    apply not_congr,
    exact phi_ih binders V h1 h2,
  },
  case formula.imp_ : phi psi phi_ih psi_ih binders V h1 h2
  {
    unfold admits_pred_fun_aux at h1,
    simp only [bool.of_to_bool_iff] at h1,
    cases h1,

    unfold replace_pred_fun,
    unfold holds,
    apply imp_congr,
    {
      exact phi_ih binders V h1_left h2,
    },
    {
      exact psi_ih binders V h1_right h2,
    },
  },
  case formula.forall_ : x phi phi_ih binders V h1 h2
  {
    unfold admits_pred_fun_aux at h1,

    unfold replace_pred_fun,
    unfold holds,
    apply forall_congr,
    intros d,
    apply phi_ih (binders ∪ {x}) (function.update_ite V x d) h1,
    intros v a1,
    unfold function.update_ite,
    simp only [finset.mem_union, finset.mem_singleton] at a1,
    push_neg at a1,
    cases a1,
    simp only [if_neg a1_right],
    exact h2 v a1_left,
  },
end


theorem pred_sub_valid
  (phi : formula)
  (τ : pred_name → ℕ → list var_name × formula)
  (h1 : admits_pred_fun_aux τ ∅ phi)
  (h2 : phi.is_valid) :
  (replace_pred_fun τ phi).is_valid :=
begin
  unfold formula.is_valid at h2,

  unfold formula.is_valid,
  intros D I V,

  obtain s1 := pred_sub_aux D I V V τ ∅ phi h1,
  simp only [eq_self_iff_true, forall_const] at s1,

  rewrite <- s1,
  apply h2,
end


#lint

end fol
