import .prop


set_option pp.parens true


open formula


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


theorem eval_and
  (P Q : formula)
  (val : valuation) :
  formula.eval_atomic val (and_ P Q) = bool.tt ↔
    ((formula.eval_atomic val P = bool.tt) ∧ (formula.eval_atomic val Q = bool.tt)) :=
begin
  unfold formula.and_,
  unfold formula.eval_atomic,
  cases formula.eval_atomic val P;
  cases formula.eval_atomic val Q;
  exact dec_trivial,
end


lemma and_intro
  (P Q : formula)
  (Δ : set formula) :
  is_deduct Δ (P.imp_ (Q.imp_ (P.and_ Q))) :=
begin
  apply proof_imp_deduct,
  apply prop_complete,
  unfold formula.is_tauto_atomic,
  simp only [eval_and, eval_imp],
  tauto,
end


lemma and_elim_left
  (P Q : formula)
  (Δ : set formula) :
  is_deduct Δ ((P.and_ Q).imp_ P) :=
begin
  apply proof_imp_deduct,
  apply prop_complete,
  unfold formula.is_tauto_atomic,
  simp only [eval_and, eval_imp],
  tauto,
end


lemma and_elim_right
  (P Q : formula)
  (Δ : set formula) :
  is_deduct Δ ((P.and_ Q).imp_ Q) :=
begin
  apply proof_imp_deduct,
  apply prop_complete,
  unfold formula.is_tauto_atomic,
  simp only [eval_and, eval_imp],
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


def proof_equiv (P Q : formula) : Prop := is_proof (P.iff_ Q)


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


lemma iff_intro
  (P Q R : formula) :
  is_proof ((P.imp_ Q).imp_ ((Q.imp_ P).imp_ (P.iff_ Q))) :=
begin
  unfold formula.iff_,
  apply prop_complete,
  unfold formula.is_tauto_atomic,
  simp only [eval_and, eval_imp],
  tauto,
end


theorem T_18_1
  (P Q : formula)
  (v : variable_) :
  is_proof ((forall_ v (P.iff_ Q)).imp_ ((forall_ v P).iff_ (forall_ v Q))) :=
begin
  sorry,
end


def is_repl (U V : formula) : formula → formula → Prop
| (not_ P) (not_ P') := is_repl P P'
| (imp_ P Q) (imp_ P' Q') := is_repl P P' ∧ is_repl Q Q'
| (forall_ x P) (forall_ x' P') := x = x' ∧ is_repl P P'
| P P' := P = P' ∨ (P = U ∧ P' = V)


inductive is_repl_of (U V : formula) : formula → formula → Prop
| same_
  (P P' : formula) :
  P = P' →
  is_repl_of P P'

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


lemma Forall_spec_id
  (xs : list variable_)
  (P : formula) :
  is_proof ((formula.Forall_ xs P).imp_ P) :=
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
    squeeze_simp,
    apply is_deduct.mp_ (Forall_ xs_tl P),
    apply proof_imp_deduct,
    exact xs_ih,
    apply spec_id xs_hd,
    apply is_deduct.assume_,
    squeeze_simp,
    sorry,
  },
end


lemma prop_iff_id
  (P : formula) :
  is_proof (P.iff_ P) :=
begin
  unfold formula.iff_,
  apply prop_complete,
  unfold formula.is_tauto_atomic,
  simp only [eval_and, eval_imp],
  squeeze_simp,
end


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
    sorry,
  },
  case is_repl_of.imp_ : h1_P h1_Q h1_P' h1_Q' h1_ᾰ h1_ᾰ_1 h1_ih_ᾰ h1_ih_ᾰ_1
  { admit },
  case is_repl_of.forall_ : h1_x h1_P h1_P' h1_ᾰ h1_ih
  { admit },
end


#lint
