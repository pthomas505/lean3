import .prop


set_option pp.parens true


open formula


def proof_equiv (P Q : formula) : Prop := is_proof (P.iff_ Q)


/--
is_repl_of_var_in_list u v l_u l_v := True if and only if l_v is the result of replacing one or more specified occurrences (but not necessarily all occurrences) of u in l_u by occurrences of v.
-/
def is_repl_of_var_in_list_fun (u v : variable_) : list variable_ → list variable_ → Prop
| [] [] := true
| (hd_u :: tl_u) (hd_v :: tl_v) := (hd_u = hd_v ∨ (hd_u = u ∧ hd_v = v)) ∧ is_repl_of_var_in_list_fun tl_u tl_v
| _ _ := false


/--
is_repl_of_var_in_formula_fun u v P_u P_v := True if and only if P_v is the result of replacing one or more specified occurrences (but not necessarily all occurrences) of u in P_u by occurrences of v.
-/
def is_repl_of_var_in_formula_fun (u v : variable_) : formula → formula → Prop
| true_ true_ := true
| (pred_ name_u args_u) (pred_ name_v args_v) := name_u = name_v ∧ is_repl_of_var_in_list_fun u v args_u args_v
| (eq_ x_u y_u) (eq_ x_v y_v) := (x_u = x_v ∨ (x_u = u ∧ x_v = v)) ∧ (y_u = y_v ∨ (y_u = u ∧ y_v = v))
| (not_ P_u) (not_ P_v) := is_repl_of_var_in_formula_fun P_u P_v
| (imp_ P_u Q_u) (imp_ P_v Q_v) := is_repl_of_var_in_formula_fun P_u P_v ∧ is_repl_of_var_in_formula_fun Q_u Q_v
| (forall_ x P_u) (forall_ x' P_v) := x = x' ∧ is_repl_of_var_in_formula_fun P_u P_v
| _ _ := false


/--
is_repl_of_var_in_formula u v P_u P_v := True if and only if P_v is the result of replacing one or more specified occurrences (but not necessarily all occurrences) of u in P_u by occurrences of v.
-/
inductive is_repl_of_var_in_formula (u v : variable_) : formula → formula → Prop
| true_ :
  is_repl_of_var_in_formula true_ true_

| pred_
  (name : pred_name_)
  (n : ℕ)
  (args_u args_v : fin n → variable_) :
  (∀ (i : fin n), (args_u i = args_v i) ∨ (args_u i = u ∧ args_v i = v)) →
  is_repl_of_var_in_formula (pred_ name (list.of_fn args_u)) (pred_ name (list.of_fn args_v))

| eq_
  (x_u y_u : variable_)
  (x_v y_v : variable_) :
  (x_u = x_v) ∨ (x_u = u ∧ x_v = v) →
  (y_u = y_v) ∨ (y_u = u ∧ y_v = v) →
  is_repl_of_var_in_formula (eq_ x_u y_u) (eq_ x_v y_v)

| not_
  (P_u P_v : formula) :
  is_repl_of_var_in_formula P_u P_v →
  is_repl_of_var_in_formula P_u.not_ P_v.not_

| imp_
  (P_u Q_u : formula)
  (P_v Q_v : formula) :
  is_repl_of_var_in_formula P_u P_v →
  is_repl_of_var_in_formula Q_u Q_v →
  is_repl_of_var_in_formula (P_u.imp_ Q_u) (P_v.imp_ Q_v)

| forall_
  (x : variable_)
  (P_u P_v : formula) :
  is_repl_of_var_in_formula P_u P_v →
  is_repl_of_var_in_formula (forall_ x P_u) (forall_ x P_v)


/--
is_repl_of_formula_in_formula_fun U V P_u P_v := True if and only if P_v is the result of replacing one or more specified occurrences (but not necessarily all occurrences) of U in P_u by occurrences of V.
-/
def is_repl_of_formula_in_formula_fun (U V : formula) : formula → formula → Prop
| (not_ P_u) (not_ P_v) := is_repl_of_formula_in_formula_fun P_u P_v
| (imp_ P_u Q_u) (imp_ P_v Q_v) := is_repl_of_formula_in_formula_fun P_u P_v ∧ is_repl_of_formula_in_formula_fun Q_u Q_v
| (forall_ x P_u) (forall_ x' P_v) := x = x' ∧ is_repl_of_formula_in_formula_fun P_u P_v
| P_u P_v := P_u = P_v ∨ (P_u = U ∧ P_v = V)


/--
is_repl_of_formula_in_formula U V P_u P_v := True if and only if P_v is the result of replacing one or more specified occurrences (but not necessarily all occurrences) of U in P_u by occurrences of V.
-/
inductive is_repl_of_formula_in_formula (U V : formula) : formula → formula → Prop
-- not replacing an occurrence
| same_
  (P_u P_v : formula) :
  P_u = P_v →
  is_repl_of_formula_in_formula P_u P_v

-- replacing an occurrence
| diff_
  (P_u P_v : formula) :
  P_u = U →
  P_v = V →
  is_repl_of_formula_in_formula P_u P_v

| not_
  (P_u P_v : formula) :
  is_repl_of_formula_in_formula P_u P_v →
  is_repl_of_formula_in_formula P_u.not_ P_v.not_

| imp_
  (P_u Q_u : formula)
  (P_v Q_v : formula) :
  is_repl_of_formula_in_formula P_u P_v →
  is_repl_of_formula_in_formula Q_u Q_v →
  is_repl_of_formula_in_formula (P_u.imp_ Q_u) (P_v.imp_ Q_v)

| forall_
  (x : variable_)
  (P_u P_v : formula) :
  is_repl_of_formula_in_formula P_u P_v →
  is_repl_of_formula_in_formula (forall_ x P_u) (forall_ x P_v)


def similar (P_u P_v : formula) (u v : variable_) : Prop :=
  ¬ is_free_in v P_u ∧
  ¬ is_free_in u P_v ∧
  fast_admits u v P_u ∧
  fast_admits v u P_v ∧
  P_v = fast_replace_free u v P_u ∧
  P_u = fast_replace_free v u P_v


-- Universal Elimination
theorem T_17_1
  (P : formula)
  (v t : variable_)
  (Δ : set formula)
  (h1 : is_deduct Δ (forall_ v P))
  (h2 : fast_admits v t P) :
  is_deduct Δ (fast_replace_free v t P) :=
begin
  apply is_deduct.mp_ (forall_ v P),
  {
    apply is_deduct.axiom_,
    apply is_axiom.pred_2_ v t P (fast_replace_free v t P) h2,
    refl,
  },
  {
    exact h1,
  }
end

alias T_17_1 <- spec forall_elim


lemma spec_id
  (v : variable_)
  (P : formula)
  (Δ : set formula)
  (h1 : is_deduct Δ (forall_ v P)) :
  is_deduct Δ P :=
begin
  apply is_deduct.mp_ (forall_ v P),
  {
    apply is_deduct.axiom_,
    apply is_axiom.pred_2_ v v P,
    {
      exact fast_admits_self P v,
    },
    {
      exact fast_replace_free_self P v,
    },
  },
  {
    exact h1,
  }
end

alias spec_id <- forall_elim_id


theorem T_17_3
  (P : formula)
  (v t : variable_)
  (h1 : fast_admits v t P) :
  is_proof ((fast_replace_free v t P).imp_ (exists_ v P)) :=
begin
  unfold fast_admits at h1,

  unfold formula.exists_,
  unfold is_proof,
  apply is_deduct.mp_ ((forall_ v P.not_).imp_ (fast_replace_free v t P).not_),
  {
    apply prop_complete,
    unfold formula.is_tauto_prime,
    simp only [eval_not, eval_imp],
    tauto,
  },
  {
    apply is_deduct.axiom_,
    apply is_axiom.pred_2_ v t,
    {
      unfold fast_admits,
      unfold fast_admits_aux,
      exact h1,
    },
    {
      refl,
    },
  }
end


-- Existential Introduction
theorem T_17_4
  (P : formula)
  (v t : variable_)
  (Δ : set formula)
  (h1 : fast_admits v t P)
  (h2 : is_deduct Δ (fast_replace_free v t P)) :
  is_deduct Δ (exists_ v P) :=
begin
  apply is_deduct.mp_ (fast_replace_free v t P),
  {
    apply proof_imp_deduct,
    apply T_17_3,
    exact h1,
  },
  {
    exact h2,
  }
end

alias T_17_4 <- exists_intro


lemma exists_intro_id
  (P : formula)
  (v : variable_)
  (Δ : set formula)
  (h1 : is_deduct Δ P) :
  is_deduct Δ (exists_ v P) :=
begin
  apply T_17_4 P v v Δ,
  {
    exact fast_admits_self P v,
  },
  {
    simp only [fast_replace_free_self],
    exact h1,
  }
end


theorem T_17_6
  (P : formula)
  (v : variable_) :
  is_proof ((forall_ v P).imp_ (exists_ v P)) :=
begin
  apply deduction_theorem,
  simp only [set.union_singleton, insert_emptyc_eq],
  apply exists_intro_id,
  apply spec_id v,
  apply is_deduct.assume_,
  simp only [set.mem_singleton],
end


theorem T_17_7
  (Q : formula)
  (v : variable_)
  (Δ : set formula)
  (h1 : is_deduct Δ Q)
  (h2 : ∀ (H : formula), H ∈ Δ → ¬ is_free_in v H) :
  is_deduct Δ (forall_ v Q) :=
begin
  induction h1,
  case is_deduct.axiom_ : h1_P h1_1
  {
    apply is_deduct.axiom_,
    apply is_axiom.gen_,
    exact h1_1,
  },
  case is_deduct.assume_ : h1_P h1_1
  {
    apply is_deduct.mp_ h1_P,
    {
      apply is_deduct.axiom_,
      apply is_axiom.pred_3_,
      exact h2 h1_P h1_1,
    },
    {
      apply is_deduct.assume_,
      exact h1_1,
    },
  },
  case is_deduct.mp_ : h1_P h1_Q h1_1 h1_2 h1_ih_1 h1_ih_2
  {
    apply is_deduct.mp_ (forall_ v h1_P),
    {
      apply is_deduct.mp_ (forall_ v (h1_P.imp_ h1_Q)),
      {
        apply is_deduct.axiom_,
        apply is_axiom.pred_1_,
      },
      {
        exact h1_ih_1,
      }
    },
    {
      exact h1_ih_2,
    }
  },
end

alias T_17_7 <- generalization


-- Universal Introduction

example
  (P : formula)
  (v t : variable_)
  (Δ : set formula)
  (h1 : ¬ occurs_in t P)
  (h2 : is_deduct Δ (fast_replace_free v t P))
  (h3 : ∀ (H : formula), H ∈ Δ → ¬ is_free_in t H) :
  is_deduct Δ (forall_ v P) :=
begin
  rewrite <- fast_replace_free_inverse P v t h1,

  apply is_deduct.mp_ (forall_ t (fast_replace_free v t P)),
  {
    apply proof_imp_deduct,
    apply deduction_theorem,
    simp only [set.union_singleton, insert_emptyc_eq],
    apply generalization,
    {
      apply spec,
      {
        apply is_deduct.assume_,
        simp only [set.mem_singleton],
      },
      {
        apply fast_replace_free_fast_admits,
        exact h1,
      },
    },
    {
      simp only [set.mem_singleton_iff, forall_eq],
      unfold is_free_in,
      simp only [not_and],
      intros a1 contra,
      exact not_is_free_in_fast_replace_free P v t a1 contra,
    }
  },
  {
    exact generalization (fast_replace_free v t P) t Δ h2 h3,
  },
end


example
  (P : formula)
  (h1 : is_proof_alt P) :
  is_deduct ∅ P :=
begin
  induction h1,
  case is_proof_alt.prop_true_ :
  {
    apply is_deduct.axiom_,
    apply is_axiom.prop_true_,
  },
  case is_proof_alt.prop_1_ : h1_P h1_Q
  {
    apply is_deduct.axiom_,
    apply is_axiom.prop_1_,
  },
  case is_proof_alt.prop_2_ : h1_P h1_Q h1_R
  {
    apply is_deduct.axiom_,
    apply is_axiom.prop_2_,
  },
  case is_proof_alt.prop_3_ : h1_P h1_Q
  {
    apply is_deduct.axiom_,
    apply is_axiom.prop_3_,
  },
  case is_proof_alt.pred_1_ : h1_v h1_P h1_Q
  {
    apply is_deduct.axiom_,
    apply is_axiom.pred_1_,
  },
  case is_proof_alt.pred_2_ : h1_v h1_t h1_P h1_P' h1_1 h1_ih_1
  {
    apply is_deduct.axiom_,
    exact is_axiom.pred_2_ h1_v h1_t h1_P h1_P' h1_1 h1_ih_1,    
  },
  case is_proof_alt.pred_3_ : h1_v h1_P h1_1
  {
    apply is_deduct.axiom_,
    apply is_axiom.pred_3_,
    exact h1_1,
  },
  case is_proof_alt.eq_1_ : h1
  {
    apply is_deduct.axiom_,
    apply is_axiom.eq_1_,
  },
  case is_proof_alt.eq_2_pred_ : h1_name h1_n h1_xs h1_ys
  {
    apply is_deduct.axiom_,
    apply is_axiom.eq_2_pred_,
  },
  case is_proof_alt.eq_2_eq_ : h1_x_0 h1_y_0 h1_x_1 h1_y_1
  {
    apply is_deduct.axiom_,
    apply is_axiom.eq_2_eq_,
  },
  case is_proof_alt.gen_ : h1_v h1_P h1_1 h1_ih
  {
    apply generalization,
    {
      exact h1_ih,
    },
    {
      simp only [set.mem_empty_eq, is_empty.forall_iff, forall_const],
    }
  },
  case is_proof_alt.mp_ : h1_P h1_Q h1_1 h1_2 h1_ih_1 h1_ih_2
  {
    exact is_deduct.mp_ h1_P h1_Q h1_ih_1 h1_ih_2,
  },
end


example
  (P : formula)
  (h1 : is_deduct ∅ P) :
  is_proof_alt P :=
begin
  induction h1,
  case is_deduct.axiom_ : h1_P h1_1
  {
    induction h1_1,
    case is_axiom.prop_true_ :
    {
      apply is_proof_alt.prop_true_,
    },
    case is_axiom.prop_1_ : h1_1_P h1_1_Q
    {
      apply is_proof_alt.prop_1_,
    },
    case is_axiom.prop_2_ : h1_1_P h1_1_Q h1_1_R
    {
      apply is_proof_alt.prop_2_,
    },
    case is_axiom.prop_3_ : h1_1_P h1_1_Q
    {
      apply is_proof_alt.prop_3_,
    },
    case is_axiom.pred_1_ : h1_1_v h1_1_P h1_1_Q
    {
      apply is_proof_alt.pred_1_,
    },
    case is_axiom.pred_2_ : h1_1_v h1_1_t h1_1_P h1_1_1 h1_1_ih_1 h1_1_ih_2
    {
      apply is_proof_alt.pred_2_ h1_1_v h1_1_t h1_1_P h1_1_1 h1_1_ih_1 h1_1_ih_2,
    },
    case is_axiom.pred_3_ : h1_1_v h1_1_P h1_1_1
    {
      apply is_proof_alt.pred_3_,
      exact h1_1_1,
    },
    case is_axiom.eq_1_ : h1_1
    {
      apply is_proof_alt.eq_1_,
    },
    case is_axiom.eq_2_pred_ : h1_1_name h1_1_n h1_1_xs h1_1_ys
    {
      apply is_proof_alt.eq_2_pred_,
    },
    case is_axiom.eq_2_eq_ : h1_1_x_0 h1_1_y_0 h1_1_x_1 h1_1_y_1
    {
      apply is_proof_alt.eq_2_eq_,
    },
    case is_axiom.gen_ : h1_1_v h1_1_P h1_1_1 h1_1_ih
    {
      apply is_proof_alt.gen_,
      exact h1_1_ih,
    },
  },
  case is_deduct.assume_ : h1_P h1_1
  {
    simp only [set.mem_empty_eq] at h1_1,
    contradiction,
  },
  case is_deduct.mp_ : h1_P h1_Q h1_1 h1_2 h1_ih_1 h1_ih_2
  {
    exact is_proof_alt.mp_ h1_P h1_Q h1_ih_1 h1_ih_2,
  },
end


theorem T_17_10
  (P : formula)
  (u v : variable_) :
  is_proof ((forall_ u (forall_ v P)).imp_ (forall_ v (forall_ u P))) :=
begin
  apply deduction_theorem,
  simp only [set.union_singleton, insert_emptyc_eq],
  apply generalization,
  {
    apply generalization,
    {
      apply spec_id v P,
      apply spec_id u (forall_ v P),
      apply is_deduct.assume_,
      simp only [set.mem_singleton],
    },
    {
      simp only [set.mem_singleton_iff, forall_eq],
      unfold is_free_in,
      simp only [eq_self_iff_true, not_true, false_and, not_false_iff],
    }
  },
  {
    simp only [set.mem_singleton_iff, forall_eq],
    unfold is_free_in,
    simp only [eq_self_iff_true, not_true, false_and, and_false, not_false_iff],
  }
end


theorem T_17_11
  (P Q : formula)
  (v : variable_)
  (h1 : ¬ is_free_in v Q) :
  is_proof ((forall_ v (P.imp_ Q)).imp_ ((exists_ v P).imp_ Q)) :=
begin
  apply deduction_theorem,
  simp only [set.union_singleton, insert_emptyc_eq],
  unfold exists_,
  apply is_deduct.mp_ (Q.not_.imp_ (forall_ v Q.not_)),
  {
    apply is_deduct.mp_ ((forall_ v Q.not_).imp_ (forall_ v P.not_)),
    {
      apply proof_imp_deduct,
      apply prop_complete,
      unfold formula.is_tauto_prime,
      simp only [eval_imp, eval_not],
      tauto,
    },
    {
      apply is_deduct.mp_ (forall_ v (Q.not_.imp_ P.not_)),
      {
        apply is_deduct.axiom_,
        apply is_axiom.pred_1_,
      },
      {
        apply generalization,
        {
          apply is_deduct.mp_ (P.imp_ Q),
          {
            apply proof_imp_deduct,
            apply T_14_7,
          },
          {
            apply spec_id v (P.imp_ Q),
            apply is_deduct.assume_,
            simp only [set.mem_singleton],
          }
        },
        {
          simp only [set.mem_singleton_iff, forall_eq],
          unfold is_free_in,
          simp only [eq_self_iff_true, not_true, false_and, not_false_iff],
        }
      },
    },
  },
  {
    apply is_deduct.axiom_,
    apply is_axiom.pred_3_,
    unfold is_free_in,
    exact h1,
  }
end


-- Rule C

theorem T_17_12
  (P Q : formula)
  (v : variable_)
  (Δ : set formula)
  (h1 : is_deduct Δ (exists_ v P))
  (h2 : is_deduct (Δ ∪ {P}) Q)
  (h3 : ∀ (H : formula), H ∈ Δ → ¬ is_free_in v H)
  (h4 : ¬ is_free_in v Q) :
  is_deduct Δ Q :=
begin
  apply is_deduct.mp_ (exists_ v P),
  {
    apply is_deduct.mp_ (forall_ v (P.imp_ Q)),
    {
      apply proof_imp_deduct,
      exact T_17_11 P Q v h4,
    },
    {
      apply generalization,
      {
        apply deduction_theorem,
        exact h2,
      },
      {
        exact h3,
      }
    },
  },
  {
    exact h1,
  }
end

alias T_17_12 <- rule_C


example
  (P Q : formula)
  (v t : variable_)
  (Δ : set formula)
  (h1 : is_deduct Δ (exists_ v P))
  (h2 : is_deduct (Δ ∪ {fast_replace_free v t P}) Q)
  (h3 : ¬ occurs_in t P)
  (h4 : ¬ occurs_in t Q)
  (h5 : ∀ (H : formula), H ∈ Δ → ¬ is_free_in t H) :
  is_deduct Δ Q :=
begin
  apply is_deduct.mp_ (exists_ t (fast_replace_free v t P)),
  {
    apply deduction_theorem,
    apply rule_C (fast_replace_free v t P) Q t (Δ ∪ {exists_ t (fast_replace_free v t P)}),
    {
      apply is_deduct.assume_,
      squeeze_simp,
    },
    {
      simp only [set.union_assoc],
      simp only [set.union_comm],
      rewrite <- set.union_assoc Δ {fast_replace_free v t P} {exists_ t (fast_replace_free v t P)},
      obtain s5 := T_14_10 Q (Δ ∪ {fast_replace_free v t P}) h2 {exists_ t (fast_replace_free v t P)},
      apply s5,
    },
    {
      intros H a1,
      squeeze_simp at a1,
      cases a1,
      rewrite a1,
      unfold exists_,
      unfold is_free_in,
      squeeze_simp,
      apply h5,
      exact a1,
    },
    {
      intros contra,
      apply h4,
      apply is_free_in_imp_occurs_in,
      exact contra,
    },
  },
  {
    sorry,
  }
end


theorem T_17_14
  (P Q : formula)
  (v : variable_) :
  is_proof ((exists_ v (P.and_ Q)).imp_ ((exists_ v P).and_ (exists_ v Q))) :=
begin
  apply deduction_theorem,
  simp only [set.union_singleton, insert_emptyc_eq],
  apply rule_C (P.and_ Q) ((exists_ v P).and_ (exists_ v Q)) v,
  {
    apply is_deduct.assume_,
    simp only [set.mem_singleton],
  },
  {
    apply is_deduct.mp_ (exists_ v Q),
    {
      apply is_deduct.mp_ (exists_ v P),
      {
        unfold formula.and_,
        apply proof_imp_deduct,
        apply prop_complete,
        unfold formula.is_tauto_prime,
        simp only [eval_not, eval_imp],
        tauto,
      },
      {
        apply exists_intro P v v,
        {
          apply fast_admits_self,
        },
        {
          simp only [fast_replace_free_self],
          apply is_deduct.mp_ (P.and_ Q),
          {
            unfold formula.and_,
            apply proof_imp_deduct,
            apply prop_complete,
            unfold formula.is_tauto_prime,
            simp only [eval_not, eval_imp],
            tauto,
          },
          {
            apply is_deduct.assume_,
            simp only [set.union_singleton, set.mem_insert_iff, eq_self_iff_true, true_or],
          }
        },
      }
    },
    {
      apply exists_intro Q v v,
      {
        apply fast_admits_self,
      },
      {
        simp only [fast_replace_free_self],
        apply is_deduct.mp_ (P.and_ Q),
        {
          unfold formula.and_,
          apply proof_imp_deduct,
          apply prop_complete,
          unfold formula.is_tauto_prime,
          simp only [eval_not, eval_imp],
          tauto,
        },
        {
          apply is_deduct.assume_,
          simp only [set.union_singleton, set.mem_insert_iff, eq_self_iff_true, true_or],
        }
      }
    }
  },
  {
    unfold and_,
    unfold exists_,
    simp only [set.mem_singleton_iff, forall_eq],
    unfold is_free_in,
    simp only [eq_self_iff_true, not_true, false_and, not_false_iff],
  },
  {
    unfold and_,
    unfold exists_,
    unfold is_free_in,
    simp only [eq_self_iff_true, not_true, false_and, or_self, not_false_iff],
  }
end


theorem T_18_1_left
  (P Q : formula)
  (v : variable_) :
  is_proof ((forall_ v (P.iff_ Q)).imp_ ((forall_ v P).imp_ (forall_ v Q))) :=
begin
  unfold iff_,
  apply deduction_theorem,
  apply deduction_theorem,
  simp only [set.union_singleton, insert_emptyc_eq],
  apply generalization,
  {
    apply is_deduct.mp_ P,
    {
      apply is_deduct.mp_ ((P.imp_ Q).and_ (Q.imp_ P)),
      {
        unfold formula.and_,
        apply proof_imp_deduct,
        apply prop_complete,
        unfold formula.is_tauto_prime,
        simp only [eval_not, eval_imp],
        tauto,
      },
      {
        apply spec_id v,
        apply is_deduct.assume_,
        simp only [set.mem_insert_iff, set.mem_singleton, or_true],
      }
    },
    {
      apply spec_id v,
      apply is_deduct.assume_,
      simp only [set.mem_insert_iff, eq_self_iff_true, true_and, true_or],
    }
  },
  {
    simp only [set.mem_insert_iff, set.mem_singleton_iff, forall_eq_or_imp, forall_eq],
    unfold is_free_in,
    simp only [eq_self_iff_true, not_true, false_and, not_false_iff, and_self],
  }
end


theorem T_18_1_right
  (P Q : formula)
  (v : variable_) :
  is_proof ((forall_ v (P.iff_ Q)).imp_ ((forall_ v Q).imp_ (forall_ v P))) :=
begin
  unfold iff_,
  apply deduction_theorem,
  apply deduction_theorem,
  simp only [set.union_singleton, insert_emptyc_eq],
  apply generalization,
  {
    apply is_deduct.mp_ Q,
    {
      apply is_deduct.mp_ ((P.imp_ Q).and_ (Q.imp_ P)),
      {
        unfold formula.and_,
        apply proof_imp_deduct,
        apply prop_complete,
        unfold formula.is_tauto_prime,
        simp only [eval_not, eval_imp],
        tauto,
      },
      {
        apply spec_id v,
        apply is_deduct.assume_,
        simp only [set.mem_insert_iff, set.mem_singleton, or_true],
      }
    },
    {
      apply spec_id v,
      apply is_deduct.assume_,
      simp only [set.mem_insert_iff, eq_self_iff_true, true_and, true_or],
    }
  },
  {
    simp only [set.mem_insert_iff, set.mem_singleton_iff, forall_eq_or_imp, forall_eq],
    unfold is_free_in,
    simp only [eq_self_iff_true, not_true, false_and, not_false_iff, and_self],
  }
end


theorem T_18_1
  (P Q : formula)
  (v : variable_) :
  is_proof ((forall_ v (P.iff_ Q)).imp_ ((forall_ v P).iff_ (forall_ v Q))) :=
begin
  apply is_deduct.mp_ ((forall_ v (P.iff_ Q)).imp_ ((forall_ v Q).imp_ (forall_ v P))),
  {
    apply is_deduct.mp_ ((forall_ v (P.iff_ Q)).imp_ ((forall_ v P).imp_ (forall_ v Q))),
    {
      unfold formula.iff_,
      unfold formula.and_,
      apply prop_complete,
      unfold formula.is_tauto_prime,
      simp only [eval_not, eval_imp],
      tauto,
    },
    {
      apply T_18_1_left,
    }
  },
  {
    apply T_18_1_right,
  }
end


lemma Forall_spec_id
  (xs : list variable_)
  (P : formula) :
  is_proof ((Forall_ xs P).imp_ P) :=
begin
  induction xs,
  case list.nil
  {
    unfold Forall_,
    apply prop_id,
  },
  case list.cons : xs_hd xs_tl xs_ih
  {
    unfold Forall_,
    apply deduction_theorem,
    simp only [list.foldr_cons, set.union_singleton, insert_emptyc_eq],
    apply is_deduct.mp_ (Forall_ xs_tl P),
    apply proof_imp_deduct,
    exact xs_ih,
    apply spec_id xs_hd,
    apply is_deduct.assume_,
    simp only [set.mem_singleton_iff, eq_self_iff_true, true_and],
    refl,
  },
end


lemma Forall_spec_id'
  (xs : list variable_)
  (P : formula)
  (Δ : set formula)
  (h1 : is_deduct Δ (Forall_ xs P)) :
  is_deduct Δ P :=
begin
  induction xs,
  case list.nil
  {
    unfold Forall_ at h1,
    simp only [list.foldr_nil] at h1,
    exact h1,
  },
  case list.cons : xs_hd xs_tl xs_ih
  {
    unfold Forall_ at h1,
    simp only [list.foldr_cons] at h1,

    apply xs_ih,
    unfold Forall_,
    apply spec_id xs_hd,
    exact h1,
  },
end


lemma Forall_is_bound_in
  (P : formula)
  (xs : list variable_)
  (x : variable_) :
  is_bound_in x (Forall_ xs P) ↔ (x ∈ xs ∨ is_bound_in x P) :=
begin
  unfold formula.Forall_,

  induction xs,
  case list.nil
  {
    simp only [list.foldr_nil, list.not_mem_nil, false_or],
  },
  case list.cons : xs_hd xs_tl xs_ih
  {
    simp only [list.foldr_cons, list.mem_cons_iff],
    unfold is_bound_in,
    simp only [xs_ih],
    tauto,
  },
end


lemma Forall_is_free_in
  (P : formula)
  (xs : list variable_)
  (x : variable_) :
  is_free_in x (Forall_ xs P) ↔ (x ∉ xs ∧ is_free_in x P) :=
begin
  unfold formula.Forall_,

  induction xs,
  case list.nil
  {
    simp only [list.foldr_nil, list.not_mem_nil, not_false_iff, true_and],
  },
  case list.cons : xs_hd xs_tl xs_ih
  {
    simp only [list.foldr_cons, list.mem_cons_iff],
    unfold is_free_in,
    simp only [xs_ih],
    tauto,
  },
end


-- The equivalence theorem
theorem T_18_2
  (U V : formula)
  (P_U P_V : formula)
  (l : list variable_)
  (h1 : is_repl_of_formula_in_formula U V P_U P_V)
  (h2 : ∀ (v : variable_), ((is_free_in v U ∨ is_free_in v V) ∧ is_bound_in v P_U) → v ∈ l) :
  is_proof ((Forall_ l (U.iff_ V)).imp_ (P_U.iff_ P_V)) :=
begin
  induction h1,
  case is_repl_of_formula_in_formula.same_ : h1_P h1_P' h1_1
  {
    subst h1_1,
    unfold formula.iff_,
    unfold formula.and_,
    apply prop_complete,
    unfold formula.is_tauto_prime,
    simp only [eval_not, eval_imp],
    tauto,
  },
  case is_repl_of_formula_in_formula.diff_ : h1_P h1_P' h1_1 h1_2
  {
    subst h1_1,
    subst h1_2,
    apply Forall_spec_id,
  },
  case is_repl_of_formula_in_formula.not_ : h1_P h1_P' h1_1 h1_ih
  {
    unfold is_bound_in at h2,

    apply is_deduct.mp_ ((Forall_ l (U.iff_ V)).imp_ (h1_P.iff_ h1_P')),
    {
      unfold formula.iff_,
      unfold formula.and_,
      apply prop_complete,
      unfold formula.is_tauto_prime,
      simp only [eval_not, eval_imp],
      tauto,
    },
    {
      exact h1_ih h2,
    },
  },
  case is_repl_of_formula_in_formula.imp_ : h1_P h1_Q h1_P' h1_Q' h1_1 h1_2 h1_ih_1 h1_ih_2
  {
    unfold is_bound_in at h2,

    apply is_deduct.mp_ ((Forall_ l (U.iff_ V)).imp_ (h1_P.iff_ h1_P')),
    {
      apply is_deduct.mp_ ((Forall_ l (U.iff_ V)).imp_ (h1_Q.iff_ h1_Q')),
      {
        unfold formula.iff_,
        unfold formula.and_,
        apply prop_complete,
        unfold formula.is_tauto_prime,
        simp only [eval_not, eval_imp],
        tauto,
      },
      {
        apply h1_ih_2,
        intros v a2,
        apply h2 v,
        tauto,
      }
    },
    {
      apply h1_ih_1,
      intros v a1,
      apply h2 v,
      tauto,
    },
  },
  case is_repl_of_formula_in_formula.forall_ : h1_x h1_P h1_P' h1_1 h1_ih
  {
    unfold is_bound_in at h2,

    apply deduction_theorem,
    simp only [set.union_singleton, insert_emptyc_eq],
    apply is_deduct.mp_ (forall_ h1_x (h1_P.iff_ h1_P')),
    {
      apply proof_imp_deduct,
      apply T_18_1,
    },
    {
      apply generalization,
      {
        apply is_deduct.mp_ (Forall_ l (U.iff_ V)),
        {
          apply proof_imp_deduct,
          apply h1_ih,
          intros v a1,
          cases a1,
          apply h2 v,
          tauto,
        },
        {
          apply is_deduct.assume_,
          simp only [set.mem_singleton],
        }
      },
      {
        intros H a1,
        simp only [set.mem_singleton_iff] at a1,
        subst a1,
        simp only [Forall_is_free_in],
        unfold formula.iff_,
        unfold formula.and_,
        unfold is_free_in,
        simp only [not_and],
        contrapose,
        push_neg,
        intros a2,
        apply h2,
        tauto,
      }
    }
  },
end


theorem C_18_3
  (U V : formula)
  (P_U P_V : formula)
  (h1 : is_repl_of_formula_in_formula U V P_U P_V)
  (h2 : is_proof (U.iff_ V)) :
  is_proof (P_U.iff_ P_V) :=
begin
  apply is_deduct.mp_ (Forall_ ((U.free_var_set ∪ V.free_var_set) ∩ P_U.bound_var_set).to_list (U.iff_ V)),
  {
    apply T_18_2 U V P_U P_V ((U.free_var_set ∪ V.free_var_set) ∩ P_U.bound_var_set).to_list h1,
    intros v a1,
    simp only [finset.mem_to_list, finset.mem_inter, finset.mem_union],
    simp only [is_free_in_iff_mem_free_var_set, is_bound_in_iff_mem_bound_var_set] at a1,
    exact a1,
  },
  {
    unfold formula.Forall_,
    induction ((U.free_var_set ∪ V.free_var_set) ∩ P_U.bound_var_set).to_list,
    case list.nil
    {
      simp only [list.foldr_nil],
      exact h2,
    },
    case list.cons : hd tl ih
    {
      simp only [list.foldr_cons],
      apply generalization,
      {
        exact ih,
      },
      {
        simp only [set.mem_empty_eq, is_empty.forall_iff, forall_const],
      }
    },
  }
end


-- The replacement theorem
theorem C_18_4
  (U V : formula)
  (P_U P_V : formula)
  (Δ : set formula)
  (h1 : is_repl_of_formula_in_formula U V P_U P_V)
  (h2 : is_proof (U.iff_ V))
  (h3 : is_deduct Δ P_U) :
  is_deduct Δ P_V :=
begin
  apply is_deduct.mp_ P_U,
  {
    apply is_deduct.mp_ (P_U.iff_ P_V),
    {
      unfold formula.iff_,
      unfold formula.and_,
      apply proof_imp_deduct,
      apply prop_complete,
      unfold formula.is_tauto_prime,
      simp only [eval_not, eval_imp],
      tauto,
    },
    {
      apply proof_imp_deduct,
      exact C_18_3 U V P_U P_V h1 h2,
    }
  },
  {
    exact h3,
  }
end


theorem T_18_6
  (P_u P_v : formula)
  (u v : variable_)
  (h1 : similar P_u P_v u v) :
  is_proof ((forall_ u P_u).iff_ (forall_ v P_v)) :=
begin
  unfold similar at h1;
  cases h1, cases h1_right, cases h1_right_right, cases h1_right_right_right, cases h1_right_right_right_right,

  apply is_deduct.mp_ ((forall_ v P_v).imp_ (forall_ u P_u)),
  {
    apply is_deduct.mp_ ((forall_ u P_u).imp_ (forall_ v P_v)),
    {
      unfold formula.iff_,
      unfold formula.and_,
      apply proof_imp_deduct,
      apply prop_complete,
      unfold formula.is_tauto_prime,
      simp only [eval_not, eval_imp],
      tauto,
    },
    {
      apply deduction_theorem,
      simp only [set.union_singleton, insert_emptyc_eq],
      apply generalization,
      {
        subst h1_right_right_right_right_left,
        apply spec,
        {
          apply is_deduct.assume_,
          simp only [set.mem_singleton],
        },
        {
          exact h1_right_right_left,
        }
      },
      {
        intros H a1,
        simp only [set.mem_singleton_iff] at a1,
        subst a1,
        unfold is_free_in,
        simp only [not_and],
        intros a2,
        exact h1_left,
      },
    }
  },
  {
    apply deduction_theorem,
    simp only [set.union_singleton, insert_emptyc_eq],
    apply generalization,
    {
      subst h1_right_right_right_right_right,
      apply spec,
      {
        apply is_deduct.assume_,
        simp only [set.mem_singleton],
      },
      {
        exact h1_right_right_right_left,
      }
    },
    {
      intros H a1,
      simp only [set.mem_singleton_iff] at a1,
      subst a1,
      unfold is_free_in,
      simp only [not_and],
      intros a2,
      exact h1_right_left,
    },
  }
end


-- Change of bound variable
theorem T_18_7
  (P_u P_v Q Q' : formula)
  (u v : variable_)
  (Δ : set formula)
  (h1 : is_deduct Δ Q)
  (h2 : is_repl_of_formula_in_formula (forall_ u P_u) (forall_ v P_v) Q Q')
  (h3 : similar P_u P_v u v) :
  is_deduct Δ Q' :=
begin
  apply C_18_4 (forall_ u P_u) (forall_ v P_v) Q Q' Δ h2,
  {
    apply T_18_6 P_u P_v u v h3,
  },
  {
    exact h1,
  }
end


theorem T_19_1
  (P : formula)
  (v : variable_)
  (h1 : ¬ is_free_in v P) :
  is_proof ((forall_ v P).iff_ P) :=
begin
  apply is_deduct.mp_ ((forall_ v P).imp_ P),
  {
    apply is_deduct.mp_ (P.imp_ (forall_ v P)),
    {
      unfold formula.iff_,
      unfold formula.and_,
      apply proof_imp_deduct,
      apply prop_complete,
      unfold formula.is_tauto_prime,
      simp only [eval_not, eval_imp],
      tauto,
    },
    {
      apply is_deduct.axiom_,
      exact is_axiom.pred_3_ v P h1,
    },
  },
  {
    apply is_deduct.axiom_,
    apply is_axiom.pred_2_ v v P P,
    {
      apply fast_admits_self,
    },
    {
      apply fast_replace_free_self,
    }
  },
end


theorem T_19_2
  (P : formula)
  (u v : variable_) :
  is_proof ((forall_ u (forall_ v P)).iff_ ((forall_ v (forall_ u P)))) :=
begin
  apply is_deduct.mp_ ((forall_ u (forall_ v P)).imp_ ((forall_ v (forall_ u P)))),
  {
    apply is_deduct.mp_ ((forall_ v (forall_ u P)).imp_ ((forall_ u (forall_ v P)))),
    {
      unfold formula.iff_,
      unfold formula.and_,
      apply proof_imp_deduct,
      apply prop_complete,
      unfold formula.is_tauto_prime,
      simp only [eval_not, eval_imp],
      tauto,
    },
    {
      apply T_17_10,
    },
  },
  {
    apply T_17_10,
  },
end


theorem T_19_TS_21_left
  (P Q : formula)
  (v : variable_)
  (h1 : ¬ is_free_in v P) :
  is_proof ((forall_ v (P.imp_ Q)).imp_ (P.imp_ (forall_ v Q))) :=
begin
  apply C_18_4 (forall_ v P) P ((forall_ v (P.imp_ Q)).imp_ ((forall_ v P).imp_ (forall_ v Q))),
  {
    apply is_repl_of_formula_in_formula.imp_,
    {
      apply is_repl_of_formula_in_formula.same_,
      refl,
    },
    {
      apply is_repl_of_formula_in_formula.imp_,
      {
        apply is_repl_of_formula_in_formula.diff_,
        {
          refl,
        },
        {
          refl,
        },
      },
      {
        apply is_repl_of_formula_in_formula.same_,
        refl,
      },
    }
  },
  {
    exact T_19_1 P v h1,
  },
  {
    apply is_deduct.axiom_,
    apply is_axiom.pred_1_,
  },
end


theorem T_19_TS_21_right
  (P Q : formula)
  (v : variable_)
  (h1 : ¬ is_free_in v P) :
  is_proof ((P.imp_ (forall_ v Q)).imp_ (forall_ v (P.imp_ Q))) :=
begin
  apply deduction_theorem,
  simp only [set.union_singleton, insert_emptyc_eq],
  apply generalization,
  {
    apply deduction_theorem,
    apply spec_id v,
    apply is_deduct.mp_ P,
    {
      apply is_deduct.assume_,
      simp only [set.union_singleton, set.mem_insert_iff, set.mem_singleton, or_true],
    },
    {
      apply is_deduct.assume_,
      simp only [set.union_singleton, set.mem_insert_iff, eq_self_iff_true, true_or],
    },
  },
  {
    intros H a1,
    simp only [set.mem_singleton_iff] at a1,
    subst a1,
    unfold is_free_in,
    push_neg,
    split,
    {
      exact h1,
    },
    {
      intros a1,
      contradiction,
    }
  },
end


theorem T_19_TS_21
  (P Q : formula)
  (v : variable_)
  (h1 : ¬ is_free_in v P) :
  is_proof ((forall_ v (P.imp_ Q)).iff_ (P.imp_ (forall_ v Q))) :=
begin
  apply is_deduct.mp_ ((forall_ v (P.imp_ Q)).imp_ (P.imp_ (forall_ v Q))),
  {
    apply is_deduct.mp_ ((P.imp_ (forall_ v Q)).imp_ (forall_ v (P.imp_ Q))),
    {
      unfold formula.iff_,
      unfold formula.and_,
      apply proof_imp_deduct,
      apply prop_complete,
      unfold formula.is_tauto_prime,
      simp only [eval_not, eval_imp],
      tauto,
    },
    {
      exact T_19_TS_21_right P Q v h1,
    },
  },
  {
    exact T_19_TS_21_left P Q v h1,
  },
end


theorem T_21_1
  (x y : variable_) :
  is_proof (forall_ x (forall_ y ((eq_ x y).imp_ (eq_ y x)))) :=
begin
  apply generalization,
  {
    apply generalization,
    {
      apply is_deduct.mp_ (eq_ y y),
      {
        apply is_deduct.mp_ (((eq_ y y).and_ (eq_ x y)).imp_ ((eq_ y x).iff_ (eq_ y y))),
        {
          unfold formula.iff_,
          unfold formula.and_,
          apply proof_imp_deduct,
          apply prop_complete,
          unfold formula.is_tauto_prime,
          simp only [eval_not, eval_imp],
          tauto,
        },
        {
          apply spec_id y,
          apply spec_id y,
          apply spec_id x,
          apply spec_id y,
          apply is_deduct.axiom_,
          exact is_axiom.eq_2_eq_ y x y y,
        }
      },
      {
        apply spec_id y,
        apply is_deduct.axiom_,
        exact is_axiom.eq_1_ y,
      }
    },
    {
      intros H a1,
      simp only [set.mem_empty_eq] at a1,
      contradiction,
    }
  },
  {
    intros H a1,
    simp only [set.mem_empty_eq] at a1,
    contradiction,
  }
end


theorem T_21_2
  (x y z : variable_) :
  is_proof (forall_ x (forall_ y (forall_ z (((eq_ x y).and_ (eq_ y z)).imp_ (eq_ x z))))) :=
begin
  apply generalization,
  {
    apply generalization,
    {
      apply generalization,
      {
        apply is_deduct.mp_ (eq_ z z),
        {
          apply is_deduct.mp_ (((eq_ x y).and_ (eq_ z z)).imp_ ((eq_ x z).iff_ (eq_ y z))),
          {
            unfold formula.iff_,
            unfold formula.and_,
            apply proof_imp_deduct,
            apply prop_complete,
            unfold formula.is_tauto_prime,
            simp only [eval_not, eval_imp],
            tauto,
          },
          {
            apply spec_id z,
            apply spec_id y,
            apply spec_id z,
            apply spec_id x,
            apply is_deduct.axiom_,
            exact is_axiom.eq_2_eq_ x z y z,
          },
        },
        {
          apply spec_id z,
          apply is_deduct.axiom_,
          exact is_axiom.eq_1_ z,
        }
      },
      {
        intros H a1,
        simp only [set.mem_empty_eq] at a1,
        contradiction,
      },
    },
    {
      intros H a1,
      simp only [set.mem_empty_eq] at a1,
      contradiction,
    },
  },
  {
    intros H a1,
    simp only [set.mem_empty_eq] at a1,
    contradiction,
  },
end


theorem T_21_8
  (P_r P_s : formula)
  (r s : variable_)
  (h1 : is_repl_of_var_in_formula r s P_r P_s)
  (h2 : ¬ is_bound_in r P_r)
  (h3 : ¬ is_bound_in s P_r) :
  is_proof ((eq_ r s).imp_ (P_r.iff_ P_s)) :=
begin
  induction h1,
  case is_repl_of_var_in_formula.true_
  {
    unfold formula.iff_,
    unfold formula.and_,
    apply proof_imp_deduct,
    apply prop_complete,
    unfold formula.is_tauto_prime,
    simp only [eval_not, eval_imp],
    tauto,
  },
  case is_repl_of_var_in_formula.pred_ : name n args_u args_v h1_1
  {
    apply is_deduct.mp_ ((eq_ r s).imp_ ((pred_ name (list.of_fn args_u)).iff_ (pred_ name (list.of_fn args_v)))),
    {
      apply proof_imp_deduct,
      apply prop_complete,
      unfold formula.is_tauto_prime,
      simp only [eval_not, eval_imp],
      tauto,
    },
    {
      apply is_deduct.mp_ ((eq_ r s).imp_ (And_ (list.of_fn (λ (i : fin n), eq_ (args_u i) (args_v i))))),
      {
        apply is_deduct.mp_ (((And_ (list.of_fn (λ (i : fin n), eq_ (args_u i) (args_v i))))).imp_ (((pred_ name (list.of_fn args_u)).iff_ (pred_ name (list.of_fn args_v))))),
        {
          unfold formula.iff_,
          unfold formula.and_,
          apply proof_imp_deduct,
          apply prop_complete,
          unfold formula.is_tauto_prime,
          simp only [eval_not, eval_imp],
          tauto,
        },
        {
          apply Forall_spec_id' (list.of_fn args_v),
          apply Forall_spec_id' (list.of_fn args_u),
          apply is_deduct.axiom_,
          exact is_axiom.eq_2_pred_ name n args_u args_v,
        },
      },
      {
        clear h2,
        clear h3,
        unfold And_,
        induction n,
        case nat.zero
        {
          simp only [list.of_fn_zero, list.foldr_nil],
          apply proof_imp_deduct,
          apply prop_complete,
          unfold formula.is_tauto_prime,
          simp only [eval_not, eval_imp],
          tauto,
        },
        case nat.succ : n ih
        {
          simp only [list.of_fn_succ, list.foldr_cons],
          apply is_deduct.mp_ ((eq_ r s).imp_ (list.foldr and_ true_ (list.of_fn (λ (i : fin n), eq_ (args_u i.succ) (args_v i.succ))))),
          {
            apply is_deduct.mp_ ((eq_ r s).imp_ (eq_ (args_u 0) (args_v 0))),
            {
              unfold formula.and_,
              apply proof_imp_deduct,
              apply prop_complete,
              unfold formula.is_tauto_prime,
              simp only [eval_not, eval_imp],
              tauto,
            },
            {
              specialize h1_1 0,
              cases h1_1,
              {
                apply is_deduct.mp_ (eq_ (args_u 0) (args_v 0)),
                {
                  apply proof_imp_deduct,
                  apply prop_complete,
                  unfold formula.is_tauto_prime,
                  simp only [eval_not, eval_imp],
                  tauto,
                },
                {
                  simp only [h1_1],
                  apply spec_id (args_v 0),
                  apply is_deduct.axiom_,
                  apply is_axiom.eq_1_,
                },
              },
              {
                cases h1_1,
                subst h1_1_left,
                subst h1_1_right,

                apply proof_imp_deduct,
                apply prop_complete,
                unfold formula.is_tauto_prime,
                simp only [eval_not, eval_imp],
                tauto,
              }
            }
          },
          {
            apply ih,
            intros i,
            apply h1_1,
          },
        },
      },
    },
  },
  case is_repl_of_var_in_formula.eq_ : x_u y_u x_v y_v h1_1 h1_2
  {
    apply is_deduct.mp_ (((eq_ x_u x_v).and_ (eq_ y_u y_v)).imp_ ((eq_ x_u y_u).iff_ (eq_ x_v y_v))),
    {
      apply is_deduct.mp_ ((eq_ r s).imp_ ((eq_ x_u x_v).and_ (eq_ y_u y_v))),
      {
        unfold formula.iff_,
        unfold formula.and_,
        apply proof_imp_deduct,
        apply prop_complete,
        unfold formula.is_tauto_prime,
        simp only [eval_not, eval_imp],
        tauto,
      },
      {
        cases h1_1,
        {
          subst h1_1,
          cases h1_2,
          {
            subst h1_2,
            apply is_deduct.mp_ (eq_ x_u x_u),
            {
              apply is_deduct.mp_ (eq_ y_u y_u),
              {
                unfold formula.and_,
                apply proof_imp_deduct,
                apply prop_complete,
                unfold formula.is_tauto_prime,
                simp only [eval_not, eval_imp],
                tauto,
              },
              {
                apply spec_id y_u,
                apply is_deduct.axiom_,
                exact is_axiom.eq_1_ y_u,
              }
            },
            {
              apply spec_id x_u,
              apply is_deduct.axiom_,
              exact is_axiom.eq_1_ x_u,
            }
          },
          {
            cases h1_2,
            subst h1_2_left,
            subst h1_2_right,
            apply is_deduct.mp_ (eq_ x_u x_u),
            {
              unfold formula.and_,
              apply proof_imp_deduct,
              apply prop_complete,
              unfold formula.is_tauto_prime,
              simp only [eval_not, eval_imp],
              tauto,
            },
            {
              apply spec_id x_u,
              apply is_deduct.axiom_,
              exact is_axiom.eq_1_ x_u,
            }
          }
        },
        {
          cases h1_1,
          subst h1_1_left,
          subst h1_1_right,
          cases h1_2,
          {
            subst h1_2,
            apply is_deduct.mp_ (eq_ y_u y_u),
            {
              unfold formula.and_,
              apply proof_imp_deduct,
              apply prop_complete,
              unfold formula.is_tauto_prime,
              simp only [eval_not, eval_imp],
              tauto,
            },
            {
              apply spec_id y_u,
              apply is_deduct.axiom_,
              exact is_axiom.eq_1_ y_u,
            }
          },
          {
            cases h1_2,
            subst h1_2_left,
            subst h1_2_right,

            unfold formula.and_,
            apply proof_imp_deduct,
            apply prop_complete,
            unfold formula.is_tauto_prime,
            simp only [eval_not, eval_imp],
            tauto,
          }
        },
      }
    },
    {
      apply spec_id y_v,
      apply spec_id x_v,
      apply spec_id y_u,
      apply spec_id x_u,
      apply is_deduct.axiom_,
      exact is_axiom.eq_2_eq_ x_u y_u x_v y_v,
    }
  },
  case is_repl_of_var_in_formula.not_ : P_u P_v h1_1 h1_ih
  {
    unfold is_bound_in at h2,

    unfold is_bound_in at h3,

    specialize h1_ih h2 h3,
    apply is_deduct.mp_ ((eq_ r s).imp_ (P_u.iff_ P_v)),
    {
      unfold formula.iff_,
      unfold formula.and_,
      apply proof_imp_deduct,
      apply prop_complete,
      unfold formula.is_tauto_prime,
      simp only [eval_not, eval_imp],
      tauto,
    },
    {
      exact h1_ih,
    }
  },
  case is_repl_of_var_in_formula.imp_ : P_u Q_u P_v Q_v h1_1 h1_2 h1_ih_1 h1_ih_2
  {
    unfold is_bound_in at h2,
    push_neg at h2,
    cases h2,

    unfold is_bound_in at h3,
    push_neg at h3,
    cases h3,

    specialize h1_ih_1 h2_left h3_left,
    specialize h1_ih_2 h2_right h3_right,
    apply is_deduct.mp_ ((eq_ r s).imp_ (Q_u.iff_ Q_v)),
    {
      apply is_deduct.mp_ ((eq_ r s).imp_ (P_u.iff_ P_v)),
      {
        unfold formula.iff_,
        unfold formula.and_,
        apply proof_imp_deduct,
        apply prop_complete,
        unfold formula.is_tauto_prime,
        simp only [eval_not, eval_imp],
        tauto,
      },
      {
        exact h1_ih_1,
      }
    },
    {
      exact h1_ih_2,
    }
  },
  case is_repl_of_var_in_formula.forall_ : x P_u P_v h1_1 h1_ih
  {
    unfold is_bound_in at h2,
    push_neg at h2,
    cases h2,

    unfold is_bound_in at h3,
    push_neg at h3,
    cases h3,

    apply deduction_theorem,
    simp only [set.union_singleton, insert_emptyc_eq],
    apply is_deduct.mp_ (forall_ x (P_u.iff_ P_v)),
    {
      apply proof_imp_deduct,
      apply T_18_1,
    },
    {
      apply is_deduct.mp_ (eq_ r s),
      {
        apply proof_imp_deduct,
        apply is_deduct.mp_ (forall_ x ((eq_ r s).imp_ (P_u.iff_ P_v))),
        {
          apply T_19_TS_21_left,
          {
            unfold is_free_in,
            push_neg,
            split,
            {
              simp only [ne_comm],
              exact h2_left,
            },
            {
              simp only [ne_comm],
              exact h3_left,
            },
          },
        },
        {
          apply generalization,
          {
            exact h1_ih h2_right h3_right,
          },
          {
            intros H a1,
            simp only [set.mem_empty_eq] at a1,
            contradiction,
          },
        },
      },
      {
        apply is_deduct.assume_,
        simp only [set.mem_singleton],
      }
    },
  },
end


#lint
