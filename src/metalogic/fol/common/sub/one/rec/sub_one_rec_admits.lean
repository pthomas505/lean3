import .sub_one_rec_replace_free
import metalogic.fol.common.semantics


set_option pp.parens true


namespace fol

open formula


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



lemma substitution_theorem_aux
  {D : Type}
  (I : interpretation' D)
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
    simp only [bool.of_to_bool_iff] at h1,

    unfold fast_replace_free,
    unfold holds,
    congr' 2,
    simp only [list.map_map],
    simp only [list.map_eq_map_iff],
    intros x a1,
    unfold function.update_ite,
    simp only [function.comp_app],
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
    simp only [bool.of_to_bool_iff] at h1,
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
    simp only [bool.of_to_bool_iff] at h1,

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
  (I : interpretation' D)
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


#lint

end fol
