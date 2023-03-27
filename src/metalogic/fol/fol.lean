import .prop


set_option pp.parens true


open formula


def proof_equiv (P Q : formula) : Prop := is_proof (P.iff_ Q)


def is_repl (U V : formula) : formula → formula → Prop
| (not_ P) (not_ P') := is_repl P P'
| (imp_ P Q) (imp_ P' Q') := is_repl P P' ∧ is_repl Q Q'
| (forall_ x P) (forall_ x' P') := x = x' ∧ is_repl P P'
| P P' := P = P' ∨ (P = U ∧ P' = V)


/--
is_repl_of_list r s l l' = True if and only if l' is the result of replacing one or more specified occurrences (but not necessarily all occurrences) of r in l by occurrences of s.
-/
def is_repl_of_list {α : Type} (r s : α) : list α → list α → Prop
| [] [] := true
| (hd :: tl) (hd' :: tl') :=
  (hd = hd' ∨ (hd = r ∧ hd' = s)) ∧ is_repl_of_list tl tl'
| _ _ := false


inductive is_repl_of_var (r s : variable_) : formula → formula → Prop
| true_ :
  is_repl_of_var true_ true_

| pred_
  (name : pred_name_)
  (n : ℕ)
  (args args' : fin n → variable_) :
  (∀ (i : fin n), (args i = args' i) ∨ (args i = r ∧ args' i = s)) →
  is_repl_of_var (pred_ name (list.of_fn args)) (pred_ name (list.of_fn args'))

| eq_
  (x y : variable_)
  (x' y' : variable_) :
  (x = x') ∨ (x = r ∧ x' = s) →
  (y = y') ∨ (y = r ∧ y' = s) →
  is_repl_of_var (eq_ x y) (eq_ x' y')

| not_
  (P P' : formula) :
  is_repl_of_var P P' →
  is_repl_of_var P.not_ P'.not_

| imp_
  (P Q : formula)
  (P' Q' : formula) :
  is_repl_of_var P P' →
  is_repl_of_var Q Q' →
  is_repl_of_var (P.imp_ Q) (P'.imp_ Q')

| forall_
  (x : variable_)
  (P P' : formula) :
  is_repl_of_var P P' →
  is_repl_of_var (forall_ x P) (forall_ x P')


/--
is_repl_of U V P P' = True if and only if P' is the result of replacing one or more specified occurrences (but not necessarily all occurrences) of U in P by occurrences of V.
-/
inductive is_repl_of (U V : formula) : formula → formula → Prop
-- not replacing an occurrence
| same_
  (P P' : formula) :
  P = P' →
  is_repl_of P P'

-- replacing an occurrence
| diff_
  (P P' : formula) :
  P = U →
  P' = V →
  is_repl_of P P'

| not_
  (P P' : formula) :
  is_repl_of P P' →
  is_repl_of P.not_ P'.not_

| imp_
  (P Q : formula)
  (P' Q' : formula) :
  is_repl_of P P' →
  is_repl_of Q Q' →
  is_repl_of (P.imp_ Q) (P'.imp_ Q')

| forall_
  (x : variable_)
  (P P' : formula) :
  is_repl_of P P' →
  is_repl_of (forall_ x P) (forall_ x P')


def similar (P_u P_v : formula) (u v : variable_) : Prop :=
  ¬ u = v ∧
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


lemma SC_1
  (P Q : formula) :
  is_proof ((P.imp_ Q.not_).imp_ (Q.imp_ P.not_)) :=
begin
  apply prop_complete,
  unfold formula.is_tauto_atomic,
  simp only [eval_not, eval_imp],
  tauto,
end


theorem T_17_3
  (P : formula)
  (v t : variable_)
  (h1 : fast_admits v t P) :
  is_proof ((fast_replace_free v t P).imp_ (exists_ v P)) :=
begin
  unfold formula.exists_,
  unfold is_proof,
  apply is_deduct.mp_,
  {
    apply SC_1,
  },
  {
    unfold fast_admits at h1,

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
  apply is_deduct.mp_ (fast_replace_free v t P) (exists_ v P),
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
    apply is_deduct.mp_,
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
      apply is_deduct.mp_,
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
  apply is_deduct.mp_ (forall_ t (fast_replace_free v t P)),
  {
    apply proof_imp_deduct,
    apply deduction_theorem,
    simp only [set.union_singleton, insert_emptyc_eq],
    apply generalization,
    {
      have s1 : is_deduct {forall_ t (fast_replace_free v t P)} (fast_replace_free t v (fast_replace_free v t P)),
      apply spec,
      {
        apply is_deduct.assume_,
        simp only [set.mem_singleton],
      },
      {
        apply fast_replace_free_fast_admits,
        exact h1,
      },

      have s2 : (fast_replace_free t v (fast_replace_free v t P)) = P,
      exact fast_replace_free_inverse P v t h1,

      simp only [s2] at s1,
      exact s1,
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
  case is_proof_alt.eq_2 : h1_name h1_n h1_xs h1_ys
  {
    apply is_deduct.axiom_,
    apply is_axiom.eq_2,
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
    case is_axiom.eq_2 : h1_1_name h1_1_n h1_1_xs h1_1_ys
    {
      apply is_proof_alt.eq_2,
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


lemma SC_2
  (P Q R : formula)
  (Δ : set formula)
  (h1 : is_deduct Δ (Q.imp_ P))
  (h2 : is_deduct Δ (R.not_.imp_ Q)) :
  is_deduct Δ (P.not_.imp_ R) :=
begin
  apply is_deduct.mp_ (R.not_.imp_ Q),
  {
    apply is_deduct.mp_ (Q.imp_ P),
    {
      apply proof_imp_deduct,
      apply prop_complete,
      unfold formula.is_tauto_atomic,
      simp only [eval_imp, eval_not],
      tauto,
    },
    {
      exact h1,
    }
  },
  {
    exact h2,
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
  apply SC_2 (forall_ v P.not_) (forall_ v Q.not_) Q,
  {
    apply is_deduct.mp_,
    {
      apply is_deduct.axiom_,
      apply is_axiom.pred_1_,
    },
    {
      apply generalization,
      {
        apply is_deduct.mp_,
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
  apply is_deduct.mp_,
  {
    apply is_deduct.mp_,
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
  (h2 : is_deduct (Δ ∪ {replace_free v t P}) Q)
  (h3 : ¬ occurs_in t P)
  (h4 : ¬ occurs_in t Q)
  (h5 : ∀ (H : formula), H ∈ Δ → ¬ is_free_in t H) :
  is_deduct Δ Q :=
begin
  sorry,
--  apply rule_C (replace_free v t P) Q t Δ,
end


lemma and_intro
  (P Q : formula)
  (Δ : set formula) :
  is_deduct Δ (P.imp_ (Q.imp_ (P.and_ Q))) :=
begin
  unfold formula.and_,
  apply proof_imp_deduct,
  apply prop_complete,
  unfold formula.is_tauto_atomic,
  simp only [eval_not, eval_imp],
  tauto,
end


lemma and_elim_left
  (P Q : formula)
  (Δ : set formula) :
  is_deduct Δ ((P.and_ Q).imp_ P) :=
begin
  unfold formula.and_,
  apply proof_imp_deduct,
  apply prop_complete,
  unfold formula.is_tauto_atomic,
  simp only [eval_not, eval_imp],
  tauto,
end


lemma and_elim_right
  (P Q : formula)
  (Δ : set formula) :
  is_deduct Δ ((P.and_ Q).imp_ Q) :=
begin
  unfold formula.and_,
  apply proof_imp_deduct,
  apply prop_complete,
  unfold formula.is_tauto_atomic,
  simp only [eval_not, eval_imp],
  tauto,
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
        apply deduction_theorem,
        apply deduction_theorem,
        apply is_deduct.mp_,
        {
          apply is_deduct.mp_,
          {
            apply and_intro,
          },
          {
            apply is_deduct.assume_,
            simp only [set.union_singleton, set.mem_insert_iff, eq_self_iff_true, true_or, or_true],
          }
        },
        {
          apply is_deduct.assume_,
          simp only [set.union_singleton, set.mem_insert_iff, eq_self_iff_true, true_or],
        }
      },
      {
        apply exists_intro P v v,
        {
          apply fast_admits_self,
        },
        {
          simp only [fast_replace_free_self],
          apply is_deduct.mp_,
          {
            apply and_elim_left P Q,
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
        apply is_deduct.mp_,
        {
          apply and_elim_right P Q,
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
        apply and_elim_left,
      },
      {
        apply spec_id v ((P.imp_ Q).and_ (Q.imp_ P)),
        apply is_deduct.assume_,
        simp only [set.mem_insert_iff, set.mem_singleton, or_true],
      }
    },
    {
      apply spec_id v P,
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
        apply and_elim_right,
      },
      {
        apply spec_id v ((P.imp_ Q).and_ (Q.imp_ P)),
        apply is_deduct.assume_,
        simp only [set.mem_insert_iff, set.mem_singleton, or_true],
      }
    },
    {
      apply spec_id v Q,
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
      unfold formula.is_tauto_atomic,
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


lemma prop_iff_id
  (P : formula) :
  is_proof (P.iff_ P) :=
begin
  unfold formula.iff_,
  unfold formula.and_,
  apply prop_complete,
  unfold formula.is_tauto_atomic,
  simp only [eval_not, eval_imp],
  simp only [imp_self, not_true, not_false_iff, forall_const],
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
  (h1 : is_repl_of U V P_U P_V)
  (h2 : ∀ (v : variable_), ((is_free_in v U ∨ is_free_in v V) ∧ is_bound_in v P_U) → v ∈ l) :
  is_proof ((Forall_ l (U.iff_ V)).imp_ (P_U.iff_ P_V)) :=
begin
  induction h1,
  case is_repl_of.same_ : h1_P h1_P' h1_1
  {
    subst h1_1,
    apply deduction_theorem,
    apply proof_imp_deduct,
    apply prop_iff_id,
  },
  case is_repl_of.diff_ : h1_P h1_P' h1_1 h1_2
  {
    subst h1_1,
    subst h1_2,
    apply Forall_spec_id,
  },
  case is_repl_of.not_ : h1_P h1_P' h1_1 h1_ih
  {
    unfold is_bound_in at h2,

    apply is_deduct.mp_ ((Forall_ l (U.iff_ V)).imp_ (h1_P.iff_ h1_P')),
    {
      unfold formula.iff_,
      unfold formula.and_,
      apply prop_complete,
      unfold formula.is_tauto_atomic,
      simp only [eval_not, eval_imp],
      tauto,
    },
    {
      exact h1_ih h2,
    },
  },
  case is_repl_of.imp_ : h1_P h1_Q h1_P' h1_Q' h1_1 h1_2 h1_ih_1 h1_ih_2
  {
    unfold is_bound_in at h2,

    apply is_deduct.mp_ ((Forall_ l (U.iff_ V)).imp_ (h1_P.iff_ h1_P')),
    {
      apply is_deduct.mp_ ((Forall_ l (U.iff_ V)).imp_ (h1_Q.iff_ h1_Q')),
      {
        unfold formula.iff_,
        unfold formula.and_,
        apply prop_complete,
        unfold formula.is_tauto_atomic,
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
  case is_repl_of.forall_ : h1_x h1_P h1_P' h1_1 h1_ih
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
  (h1 : is_repl_of U V P_U P_V)
  (h2 : is_proof (U.iff_ V)) :
  is_proof (P_U.iff_ P_V) :=
begin
  apply is_deduct.mp_,
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
  (h1 : is_repl_of U V P_U P_V)
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
      unfold formula.is_tauto_atomic,
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
  cases h1, cases h1_right, cases h1_right_right, cases h1_right_right_right, cases h1_right_right_right_right, cases h1_right_right_right_right_right,

  have s1 : is_proof ((forall_ u P_u).imp_ (forall_ v P_v)),
  apply deduction_theorem,
  simp only [set.union_singleton, insert_emptyc_eq],
  apply generalization,
  {
    subst h1_right_right_right_right_right_left,
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

  have s2 : is_proof ((forall_ v P_v).imp_ (forall_ u P_u)),
  apply deduction_theorem,
  simp only [set.union_singleton, insert_emptyc_eq],
  apply generalization,
  {
    subst h1_right_right_right_right_right_right,
    apply spec,
    {
      apply is_deduct.assume_,
      simp only [set.mem_singleton],
    },
    {
      exact h1_right_right_right_right_left,
    }
  },
  {
    intros H a1,
    simp only [set.mem_singleton_iff] at a1,
    subst a1,
    unfold is_free_in,
    simp only [not_and],
    intros a2,
    exact h1_right_right_left,
  },

  apply is_deduct.mp_ ((forall_ v P_v).imp_ (forall_ u P_u)),
  {
    apply is_deduct.mp_ ((forall_ u P_u).imp_ (forall_ v P_v)),
    {
      unfold formula.iff_,
      unfold formula.and_,
      apply proof_imp_deduct,
      apply prop_complete,
      unfold formula.is_tauto_atomic,
      simp only [eval_not, eval_imp],
      tauto,
    },
    {
      exact s1,
    }
  },
  {
    exact s2,
  }
end


-- Change of bound variable
theorem T_18_7
  (P_u P_v Q Q' : formula)
  (u v : variable_)
  (Δ : set formula)
  (h1 : is_deduct Δ Q)
  (h2 : is_repl_of (forall_ u P_u) (forall_ v P_v) Q Q')
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


lemma T_21_8_pred
  (name : pred_name_)
  (n : ℕ)
  (args_r args_s : fin n → variable_)
  (r s : variable_)
  (h1 : (∀ (i : fin n), (args_r i = args_s i) ∨ (args_r i = r ∧ args_s i = s))) :
  is_proof ((eq_ r s).imp_ ((pred_ name (list.of_fn args_r)).iff_ (pred_ name (list.of_fn args_s)))) :=
begin
  apply deduction_theorem,
  simp only [set.union_singleton, insert_emptyc_eq],
  apply is_deduct.mp_ ((pred_ name (list.of_fn args_r)).iff_ (pred_ name (list.of_fn args_s))),
  {
    apply proof_imp_deduct,
    apply prop_complete,
    unfold formula.is_tauto_atomic,
    simp only [eval_not, eval_imp],
    tauto,
  },
  {
    apply is_deduct.mp_ (And_ (list.of_fn (λ (i : fin n), eq_ (args_r i) (args_s i)))),
    {
      apply proof_imp_deduct,
      apply is_deduct.mp_ (Forall_ (list.of_fn args_s) ((And_ (list.of_fn (λ (i : fin n), eq_ (args_r i) (args_s i)))).imp_ ((pred_ name (list.of_fn args_r)).iff_ (pred_ name (list.of_fn args_s))))),
      {
        apply Forall_spec_id,
      },
      {
        apply proof_imp_deduct,
        apply is_deduct.mp_ (Forall_ (list.of_fn args_r) (Forall_ (list.of_fn args_s) ((And_ (list.of_fn (λ (i : fin n), eq_ (args_r i) (args_s i)))).imp_ ((pred_ name (list.of_fn args_r)).iff_ (pred_ name (list.of_fn args_s)))))),
        {
          apply Forall_spec_id,
        },
        {
          apply is_deduct.axiom_,
          exact is_axiom.eq_2 name n args_r args_s,
        },
      },
    },
    {
      induction n,
      case nat.zero
      {
        simp only [list.of_fn_zero],
        apply is_deduct.axiom_,
        apply is_axiom.prop_true_,
      },
      case nat.succ : n ih
      {
        unfold And_ at ih,

        unfold And_,
        simp only [list.of_fn_succ, list.foldr_cons],
        apply is_deduct.mp_ (list.foldr and_ true_ (list.of_fn (λ (i : fin n), eq_ (args_r i.succ) (args_s i.succ)))),
        {
          apply is_deduct.mp_ (eq_ (args_r 0) (args_s 0)),
          {
            apply and_intro,
          },
          {
            specialize h1 0,
            cases h1,
            {
              rewrite h1,
              apply spec_id (args_s 0),
              apply is_deduct.axiom_,
              apply is_axiom.eq_1_,
            },
            {
              cases h1,
              subst h1_left,
              subst h1_right,
              apply is_deduct.assume_,
              simp only [set.mem_singleton],
            }
          }
        },
        {
          specialize ih (λ (i : fin n), (args_r i.succ)) (λ (i : fin n), (args_s i.succ)),
          apply ih,
          intros i,
          apply h1,
        },
      },
    },
  },
end


theorem T_21_8
  (P_r P_s : formula)
  (r s : variable_)
  (h1 : is_repl_of_var r s P_r P_s)
  (h2 : occurs_in r P_r)
  (h3 : ¬ is_bound_in r P_r)
  (h4 : ¬ is_bound_in s P_r) :
  is_proof ((eq_ r s).imp_ (P_r.iff_ P_s)) :=
begin
  induction h1,
  case is_repl_of_var.true_
  { admit },
  case is_repl_of_var.pred_ : h1_name h1_n h1_args h1_args' h1_1
  {
    exact T_21_8_pred h1_name h1_n h1_args h1_args' r s h1_1,
  },
  case is_repl_of_var.eq_ : h1_x h1_y h1_x' h1_y' h1_ᾰ h1_ᾰ_1
  { admit },
  case is_repl_of_var.not_ : h1_P h1_P' h1_ᾰ h1_ih
  { admit },
  case is_repl_of_var.imp_ : h1_P h1_Q h1_P' h1_Q' h1_ᾰ h1_ᾰ_1 h1_ih_ᾰ h1_ih_ᾰ_1
  { admit },
  case is_repl_of_var.forall_ : h1_x h1_P h1_P' h1_ᾰ h1_ih
  { admit },
end


#lint
