import .deduct


set_option pp.parens true


open formula


lemma pred_1_mp
  (P Q : formula)
  (v : variable_)
  (Δ : set formula)
  (h1 : is_deduct Δ (forall_ v (P.imp_ Q)))
  (h2 : is_deduct Δ (forall_ v P)) :
  is_deduct Δ (forall_ v Q) :=
begin
  apply is_deduct.mp_,
  {
    apply is_deduct.mp_,
    {
      apply is_deduct.axiom_,
      exact is_axiom.pred_1_ P Q v,
    },
    {
      exact h1,
    }
  },
  {
    exact h2,
  }
end


lemma pred_2_mp
  (v : variable_)
  (P : formula)
  (t : variable_)
  (Δ : set formula)
  (h1 : admits v t P)
  (h2 : is_deduct Δ (forall_ v P)) :
  is_deduct Δ (replace_free v t P) :=
begin
  apply is_deduct.mp_,
  {
    apply is_deduct.axiom_,
    exact is_axiom.pred_2_ v P t h1,
  },
  {
    exact h2,
  }
end


lemma pred_3_mp
  (P : formula)
  (v : variable_)
  (Δ : set formula)
  (h1 : ¬ is_free_in v P)
  (h2 : is_deduct Δ P) :
  is_deduct Δ (forall_ v P) :=
begin
  apply is_deduct.mp_,
  {
    apply is_deduct.axiom_,
    exact is_axiom.pred_3_ P v h1,
  },
  {
    exact h2,
  }
end


lemma proof_imp_deduct
  (P : formula)
  (h1 : is_proof P) :
  ∀ (Δ : set formula), is_deduct Δ P :=
begin
  intros Δ,
  unfold is_proof at h1,
  induction h1,
  case is_deduct.axiom_ : h1_P h1_1
  {
    apply is_deduct.axiom_,
    exact h1_1,
  },
  case is_deduct.assume_ : h1_P h1_1
  {
    simp only [set.mem_empty_eq] at h1_1,
    contradiction,
  },
  case is_deduct.mp_ : h1_P h1_Q h1_1 h1_2 h1_ih_1 h1_ih_2
  {
    exact is_deduct.mp_ h1_P h1_Q h1_ih_1 h1_ih_2,
  },
end


theorem T_13_5
  (P : formula) :
  is_proof (P.imp_ P) :=
begin
  unfold is_proof,

  apply is_deduct.mp_,
  {
    apply is_deduct.mp_,
    {
      apply is_deduct.axiom_,
      exact is_axiom.prop_2_ P (P.imp_ P) P,
    },
    {
      apply is_deduct.axiom_,
      exact is_axiom.prop_1_ P (P.imp_ P),
    }
  },
  {
    apply is_deduct.axiom_,
    exact is_axiom.prop_1_ P P,
  },
end


theorem T_13_6
  (P Q : formula) :
  is_proof (P.not_.imp_ (P.imp_ Q)) :=
begin
  unfold is_proof,

  apply is_deduct.mp_,
  {
    apply is_deduct.mp_,
    {
      apply is_deduct.axiom_,
      exact is_axiom.prop_2_ P.not_ (Q.not_.imp_ P.not_) (P.imp_ Q),
    },
    {
      apply is_deduct.mp_,
      {
        apply is_deduct.axiom_,
        exact is_axiom.prop_1_ ((Q.not_.imp_ P.not_).imp_ (P.imp_ Q)) P.not_,
      },
      {
        apply is_deduct.axiom_,
        exact is_axiom.prop_3_ Q P,
      }
    }
  },
  {
    apply is_deduct.axiom_,
    exact is_axiom.prop_1_ P.not_ Q.not_,
  },
end


-- Deduction Theorem

theorem T_14_3
  (P Q : formula)
  (Δ : set formula)
  (h1 : is_deduct (Δ ∪ {P}) Q) :
  is_deduct Δ (P.imp_ Q) :=
begin
  induction h1,
  case is_deduct.axiom_ : h1_P h1_1
  {
    -- Case 1

    apply is_deduct.mp_,
    {
      apply is_deduct.axiom_,
      exact is_axiom.prop_1_ h1_P P,
    },
    {
      apply is_deduct.axiom_,
      exact h1_1,
    },
  },
  case is_deduct.assume_ : h1_P h1_1
  {
    simp only [set.union_singleton, set.mem_insert_iff] at h1_1,
    cases h1_1,
    {
      -- Case 3

      rewrite h1_1,
      apply proof_imp_deduct,
      exact T_13_5 P,
    },
    {
      -- Case 2

      apply is_deduct.mp_,
      {
        apply is_deduct.axiom_,
        exact is_axiom.prop_1_ h1_P P,
      },
      {
        apply is_deduct.assume_,
        exact h1_1,
      },
    }
  },
  case is_deduct.mp_ : h1_P h1_Q h1_1 h1_2 h1_ih_1 h1_ih_2
  {
    -- Case 4

    apply is_deduct.mp_,
    {
      apply is_deduct.mp_,
      {
        apply is_deduct.axiom_,
        exact is_axiom.prop_2_ P h1_P h1_Q,
      },
      {
        exact h1_ih_1,
      }
    },
    {
      exact h1_ih_2,
    },
  },
end

alias T_14_3 <- deduction_theorem


example
  (P Q : formula) :
  is_proof (P.not_.imp_ (P.imp_ Q)) :=
begin
  unfold is_proof,

  apply deduction_theorem,
  apply is_deduct.mp_,
  {
    apply is_deduct.axiom_,
    exact is_axiom.prop_3_ Q P,
  },
  {
    apply is_deduct.mp_,
    {
      apply is_deduct.axiom_,
      exact is_axiom.prop_1_ P.not_ Q.not_,
    },
    {
      apply is_deduct.assume_,
      simp only [set.union_singleton, insert_emptyc_eq, set.mem_singleton],
    },
  },
end


theorem T_14_5
  (P : formula) :
  is_proof (P.not_.not_.imp_ P) :=
begin
  unfold is_proof,

  apply deduction_theorem,
  apply is_deduct.mp_,
  {
    apply is_deduct.mp_,
    {
      apply is_deduct.axiom_,
      apply is_axiom.prop_3_,
    },
    {
      apply is_deduct.mp_,
      {
        apply proof_imp_deduct,
        apply T_13_6,
      },
      {
        apply is_deduct.assume_,
        simp only [set.union_singleton, insert_emptyc_eq, set.mem_singleton],
      }
    }
  },
  {
    apply is_deduct.assume_,
    simp only [set.union_singleton, insert_emptyc_eq, set.mem_singleton_iff],
  }
end


theorem T_14_6
  (P : formula) :
  is_proof (P.imp_ P.not_.not_) :=
begin
  unfold is_proof,

  apply is_deduct.mp_,
  {
    apply is_deduct.axiom_,
    apply is_axiom.prop_3_,
  },
  {
    apply proof_imp_deduct,
    apply T_14_5,
  }
end


theorem T_14_7
  (P Q : formula) :
  is_proof ((P.imp_ Q).imp_ (Q.not_.imp_ P.not_)) :=
begin
  unfold is_proof,

  apply deduction_theorem,
  apply is_deduct.mp_,
  {
    apply is_deduct.axiom_,
    apply is_axiom.prop_3_,
  },
  {
    apply deduction_theorem,
    apply is_deduct.mp_,
    {
      apply proof_imp_deduct,
      apply T_14_6,
    },
    {
      apply is_deduct.mp_,
      {
        apply is_deduct.assume_,
        simp only [set.union_singleton, insert_emptyc_eq, set.mem_insert_iff, set.mem_singleton_iff, eq_self_iff_true, and_true,
  false_or],
      },
      {
        apply is_deduct.mp_,
        {
          apply proof_imp_deduct,
          apply T_14_5,
        },
        {
          apply is_deduct.assume_,
          simp only [set.union_singleton, insert_emptyc_eq, set.mem_insert_iff, set.mem_singleton_iff, or_false],
        }
      }
    }
  }
end


theorem T_14_8
  (Q R : formula) :
  is_proof (Q.imp_ (R.not_.imp_ ((Q.imp_ R).not_))) :=
begin
  unfold is_proof,

  apply deduction_theorem,
  apply is_deduct.mp_,
  {
    apply proof_imp_deduct,
    apply T_14_7,
  },
  {
    apply deduction_theorem,
    apply is_deduct.mp_ Q R,
    {
      apply is_deduct.assume_,
      simp only [set.union_singleton, set.mem_insert_iff, eq_self_iff_true, and_self, true_or],
    },
    {
      apply is_deduct.assume_,
      simp only [set.union_singleton, insert_emptyc_eq, set.mem_insert_iff, set.mem_singleton, or_true],
    }
  }
end


theorem T_14_9
  (P S : formula) :
  is_proof ((S.imp_ P).imp_ ((S.not_.imp_ P).imp_ P)) :=
begin
  unfold is_proof,

  apply deduction_theorem,
  apply is_deduct.mp_,
  {
    apply is_deduct.axiom_,
    apply is_axiom.prop_3_,
  },
  {
    apply deduction_theorem,
    apply is_deduct.mp_,
    {
      apply is_deduct.mp_,
      {
        apply proof_imp_deduct,
        apply T_14_8,
      },
      {
        apply is_deduct.mp_,
        {
          apply is_deduct.mp_ (S.imp_ P),
          {
            apply proof_imp_deduct,
            apply T_14_7,
          },
          {
            apply is_deduct.assume_,
            simp only [set.union_singleton, insert_emptyc_eq, set.mem_insert_iff, set.mem_singleton, false_or],
          }
        },
        {
          apply is_deduct.assume_,
          simp only [set.union_singleton, insert_emptyc_eq, set.mem_insert_iff, set.mem_singleton_iff, or_false],
        }
      }
    },
    {
      apply is_deduct.assume_,
      simp only [set.union_singleton, insert_emptyc_eq, set.mem_insert_iff, set.mem_singleton_iff, or_false],
    }
  }
end


theorem T_14_10
  (Q : formula)
  (Δ : set formula)
  (h1 : is_deduct Δ Q) :
  ∀ (Γ : set formula), is_deduct (Δ ∪ Γ) Q :=
begin
  intros Γ,
  induction h1,
  case is_deduct.axiom_ : h1_P h1_1
  {
    apply is_deduct.axiom_,
    exact h1_1,
  },
  case is_deduct.assume_ : h1_P h1_1
  {
    apply is_deduct.assume_,
    simp only [set.mem_union_eq],
    apply or.intro_left,
    exact h1_1,
  },
  case is_deduct.mp_ : h1_P h1_Q h1_1 h1_2 h1_ih_1 h1_ih_2
  {
    apply is_deduct.mp_ h1_P h1_Q,
    {
      exact h1_ih_1,
    },
    {
      exact h1_ih_2,
    }
  },
end


theorem deduction_theorem_converse
  (P Q : formula)
  (Δ : set formula)
  (h1 : is_deduct Δ (P.imp_ Q)) :
  is_deduct (Δ ∪ {P}) Q :=
begin
  have s1 : is_deduct (Δ ∪ {P}) (P.imp_ Q),
  exact T_14_10 (P.imp_ Q) Δ h1 {P},

  have s2 : is_deduct (Δ ∪ {P}) P,
  apply is_deduct.assume_,
  simp only [set.union_singleton, set.mem_insert_iff, eq_self_iff_true, true_or],

  exact is_deduct.mp_ P Q s1 s2,
end


theorem C_14_11
  (Q : formula)
  (h1 : is_proof Q) :
  ∀ (Γ : set formula), is_deduct Γ Q :=
begin
  unfold is_proof at h1,

  intros Γ,
  rewrite <- set.union_empty Γ,
  rewrite set.union_comm,
  exact T_14_10 Q ∅ h1 Γ,
end


example :
  C_14_11 = proof_imp_deduct :=
begin
  refl,
end


theorem T_14_12
  (P Q : formula)
  (Δ Γ : set formula)
  (h1 : is_deduct Δ P)
  (h2 : is_deduct Γ (P.imp_ Q)) :
  is_deduct (Δ ∪ Γ) Q :=
begin
  have s1 : is_deduct (Δ ∪ Γ) P,
  apply T_14_10,
  exact h1,

  have s2 : is_deduct (Δ ∪ Γ) (P.imp_ Q),
  rewrite set.union_comm,
  apply T_14_10,
  exact h2,

  exact is_deduct.mp_ P Q s2 s1,
end


theorem C_14_13
  (P Q : formula)
  (Δ : set formula)
  (h1 : is_deduct Δ P)
  (h2 : is_deduct Δ (P.imp_ Q)) :
  is_deduct Δ Q :=
begin
  have s1 : is_deduct (Δ ∪ Δ) Q, 
  exact T_14_12 P Q Δ Δ h1 h2,

  simp only [set.union_self] at s1,
  exact s1,
end


theorem C_14_13'
  (P Q : formula)
  (Δ : set formula)
  (h1 : is_deduct Δ P)
  (h2 : is_deduct Δ (P.imp_ Q)) :
  is_deduct Δ Q :=
begin
  exact is_deduct.mp_ P Q h2 h1,
end


theorem C_14_14
  (P Q : formula)
  (Γ : set formula)
  (h1 : is_proof P)
  (h2 : is_deduct Γ (P.imp_ Q)) :
  is_deduct Γ Q :=
begin
  have s1 : is_deduct Γ P,
  exact C_14_11 P h1 Γ,

  exact is_deduct.mp_ P Q h2 s1,
end

alias C_14_14 <- mp_proof_deduct


theorem C_14_15
  (P Q : formula)
  (Δ : set formula)
  (h1 : is_deduct Δ P)
  (h2 : is_proof (P.imp_ Q)) :
  is_deduct Δ Q :=
begin
  have s1 : is_deduct Δ (P.imp_ Q),
  exact C_14_11 (P.imp_ Q) h2 Δ,

  exact is_deduct.mp_ P Q s1 h1,
end

alias C_14_15 <- mp_deduct_proof


theorem T_14_16
  (Q : formula)
  (Δ Γ : set formula)
  (h1 : is_deduct Γ Q)
  (h2 : ∀ (P : formula), P ∈ Γ → is_deduct Δ P) :
  is_deduct Δ Q :=
begin
  induction h1,
  case is_deduct.axiom_ : h1_P h1_1
  {
    apply is_deduct.axiom_,
    exact h1_1,
  },
  case is_deduct.assume_ : h1_P h1_1
  {
    exact h2 h1_P h1_1,
  },
  case is_deduct.mp_ : h1_P h1_Q h1_1 h1_2 h1_ih_1 h1_ih_2
  {
    exact is_deduct.mp_ h1_P h1_Q h1_ih_1 h1_ih_2,
  },
end


theorem C_14_17
  (Q : formula)
  (Δ Γ : set formula)
  (h1 : is_deduct Γ Q)
  (h2 : ∀ (P : formula), P ∈ Γ → is_proof P) :
  is_proof Q :=
begin
  unfold is_proof at h2,

  unfold is_proof,
  exact T_14_16 Q ∅ Γ h1 h2,
end


def formula.is_prime : formula → Prop
| (pred_ name args) := true
| (not_ P) := false
| (imp_ P Q) := false
| (forall_ x P) := true

def formula.prime_constituent_set : formula → finset formula
| (pred_ name args) := {pred_ name args}
| (not_ P) := P.prime_constituent_set
| (imp_ P Q) := P.prime_constituent_set ∪ Q.prime_constituent_set
| (forall_ x P) := {forall_ x P}


def valuation : Type := formula → bool

def formula.eval (val : valuation) : formula → bool
| (pred_ name args) := val (pred_ name args)
| (not_ P) := ! P.eval
| (imp_ P Q) := (! P.eval) || Q.eval
| (forall_ x P) := val (forall_ x P)

def formula.is_tauto (P : formula) : Prop :=
  ∀ (val : valuation), P.eval val = bool.tt


theorem eval_not
  (P : formula)
  (val : valuation) :
  formula.eval val (not_ P) = bool.tt ↔
    ¬ (formula.eval val P = bool.tt) :=
begin
  unfold formula.eval,
  cases formula.eval val P;
  exact dec_trivial,
end


theorem eval_imp
  (P Q : formula)
  (val : valuation) :
  formula.eval val (imp_ P Q) = bool.tt ↔
    ((formula.eval val P = bool.tt) → (formula.eval val Q = bool.tt)) :=
begin
  unfold formula.eval,
  cases formula.eval val P;
  cases formula.eval val Q;
  exact dec_trivial,
end


theorem is_tauto_prop_1
  (P Q : formula) :
  (P.imp_ (Q.imp_ P)).is_tauto :=
begin
  unfold formula.is_tauto,
  intro val,
  simp only [eval_imp],
  intros a1 a2,
  exact a1,
end


theorem is_tauto_prop_2
  (P Q R : formula) :
  ((P.imp_ (Q.imp_ R)).imp_ ((P.imp_ Q).imp_ (P.imp_ R))).is_tauto :=
begin
  unfold formula.is_tauto,
  intro val,
  simp only [eval_imp],
  intros a1 a2 a3,
  apply a1,
  {
    exact a3,
  },
  {
    apply a2,
    exact a3,
  },
end


theorem is_tauto_prop_3
  (P Q : formula) :
  (((not_ P).imp_ (not_ Q)).imp_ (Q.imp_ P)).is_tauto :=
begin
  unfold formula.is_tauto,
  intro val,
  simp only [eval_not, eval_imp],
  intros a1 a2,
  by_contradiction contra,
  apply a1,
  {
    exact contra,
  },
  {
    exact a2,
  }
end


theorem is_tauto_mp
  (P Q : formula)
  (h1 : (P.imp_ Q).is_tauto)
  (h2 : P.is_tauto) :
  Q.is_tauto :=
begin
  unfold formula.is_tauto at h1,
  unfold formula.is_tauto at h2,

  unfold formula.is_tauto,
  intro val,
  simp only [eval_imp] at h1,
  apply h1,
  exact h2 val,
end


example
  (P : formula)
  (h1 : is_prop_proof P) :
  P.is_tauto :=
begin
  induction h1,
  case is_prop_deduct.axiom_ : h1_P h1_1
  {
    induction h1_1,
    case is_prop_axiom.prop_1_ : h1_1_P h1_1_Q
    {
      exact is_tauto_prop_1 h1_1_P h1_1_Q,
    },
    case is_prop_axiom.prop_2_ : h1_1_P h1_1_Q h1_1_R
    {
      exact is_tauto_prop_2 h1_1_P h1_1_Q h1_1_R,
    },
    case is_prop_axiom.prop_3_ : h1_1_P h1_1_Q
    {
      exact is_tauto_prop_3 h1_1_P h1_1_Q,
    },
  },
  case is_prop_deduct.assume_ : h1_P h1_1
  {
    simp only [set.mem_empty_eq] at h1_1,
    contradiction,
  },
  case is_prop_deduct.mp_ : h1_P h1_Q h1_1 h1_2 h1_ih_1 h1_ih_2
  {
    exact is_tauto_mp h1_P h1_Q h1_ih_1 h1_ih_2,
  },
end


theorem prop_complete
  (P : formula)
  (h1 : P.is_tauto) :
  is_proof P := sorry


theorem T_17_1
  (P : formula)
  (v t : variable_)
  (Δ : set formula)
  (h1 : is_deduct Δ (forall_ v P))
  (h2 : admits v t P) :
  is_deduct Δ (replace_free v t P) :=
begin
  exact pred_2_mp v P t Δ h2 h1,
end

alias T_17_1 <- spec forall_elim


lemma spec_id
  (P : formula)
  (v : variable_)
  (Δ : set formula)
  (h1 : is_deduct Δ (forall_ v P)) :
  is_deduct Δ P :=
begin
  have s1 : is_deduct Δ (replace_free v v P),
  apply pred_2_mp v P v Δ,
  {
    exact admits_id P v,
  },
  {
    exact h1,
  },

  simp only [replace_free_id] at s1,
  exact s1,
end

alias spec_id <- forall_elim_id


lemma SC_1
  (P Q : formula) :
  is_proof ((P.imp_ Q.not_).imp_ (Q.imp_ P.not_)) :=
begin
  apply prop_complete,
  unfold formula.is_tauto,
  simp only [eval_not, eval_imp],
  intros val a1 a2 contra,
  exact a1 contra a2,
end


theorem T_17_3
  (P : formula)
  (v t : variable_)
  (h1 : admits v t P) :
  is_proof ((replace_free v t P).imp_ (exists_ v P)) :=
begin
  unfold formula.exists_,
  unfold is_proof,
  apply is_deduct.mp_,
  {
    apply SC_1,
  },
  {
    unfold admits at h1,

    apply is_deduct.axiom_,
    apply is_axiom.pred_2_,
    unfold admits,
    unfold admits_aux,
    exact h1,
  }
end


theorem T_17_4
  (P : formula)
  (v t : variable_)
  (Δ : set formula)
  (h1 : admits v t P)
  (h2 : is_deduct Δ (replace_free v t P)) :
  is_deduct Δ (exists_ v P) :=
begin
  apply is_deduct.mp_ (replace_free v t P) (exists_ v P),
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
    exact admits_id P v,
  },
  {
    simp only [replace_free_id],
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
  apply spec_id P v,
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
    apply pred_3_mp h1_P v Δ,
    {
      exact h2 h1_P h1_1,
    },
    {
      apply is_deduct.assume_,
      exact h1_1,
    },
  },
  case is_deduct.mp_ : h1_P h1_Q h1_1 h1_2 h1_ih_1 h1_ih_2
  {
    exact pred_1_mp h1_P h1_Q v Δ h1_ih_1 h1_ih_2,
  },
end

alias T_17_7 <- generalization


example
  (P : formula)
  (h1 : is_proof_alt P) :
  is_deduct ∅ P :=
begin
  induction h1,
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
  case is_proof_alt.pred_1_ : h1_P h1_Q h1_v
  {
    apply is_deduct.axiom_,
    apply is_axiom.pred_1_,
  },
  case is_proof_alt.pred_2_ : h1_v h1_P h1_t h1_1
  {
    apply is_deduct.axiom_,
    apply is_axiom.pred_2_,
    exact h1_1,
  },
  case is_proof_alt.pred_3_ : h1_P h1_v h1_1
  {
    apply is_deduct.axiom_,
    apply is_axiom.pred_3_,
    exact h1_1,
  },
  case is_proof_alt.gen_ : h1_P h1_v h1_1 h1_ih
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
    case is_axiom.pred_1_ : h1_1_P h1_1_Q h1_1_v
    {
      apply is_proof_alt.pred_1_,
    },
    case is_axiom.pred_2_ : h1_1_v h1_1_P h1_1_t h1_1_1
    {
      apply is_proof_alt.pred_2_,
      exact h1_1_1,
    },
    case is_axiom.pred_3_ : h1_1_P h1_1_v h1_1_1
    {
      apply is_proof_alt.pred_3_,
      exact h1_1_1,
    },
    case is_axiom.gen_ : h1_1_P h1_1_v h1_1_1 h1_1_ih
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
      apply spec_id P v,
      apply spec_id (forall_ v P) u,
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
  sorry,
end


theorem T_17_11
  (P Q : formula)
  (v : variable_)
  (h1 : ¬ is_free_in v Q) :
  is_proof ( (forall_ v (P.imp_ Q)).imp_ ((exists_ v P).imp_ Q) ) :=
begin
  apply deduction_theorem,
  squeeze_simp,
  unfold exists_,
  apply SC_2 (forall_ v P.not_) (forall_ v Q.not_) Q,
  {
    sorry,
  },
  {
    sorry,
  }
end
