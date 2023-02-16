import metalogic.fol.current.binders


set_option pp.parens true


open formula


inductive is_axiom : formula → Prop

-- ⊢ P → (Q → P)
| prop_1_
  (P Q : formula) :
  is_axiom (P.imp_ (Q.imp_ P))

-- ⊢ (P → (Q → R)) → ((P → Q) → (P → R))
| prop_2_
  (P Q R : formula) :
  is_axiom ((P.imp_ (Q.imp_ R)).imp_ ((P.imp_ Q).imp_ (P.imp_ R)))

-- ⊢ (¬ P → ¬ Q) → (Q → P)
| prop_3_
  (P Q : formula) :
  is_axiom (((not_ P).imp_ (not_ Q)).imp_ (Q.imp_ P))

-- ⊢ (∀ v (P → Q)) → ((∀ v P) → (∀ v Q))
| pred_1_
  (P Q : formula) (v : variable_) :
  is_axiom ((forall_ v (P.imp_ Q)).imp_ ((forall_ v P).imp_ (forall_ v Q)))

-- ⊢ (∀ v P) → P(t/v)  provided P admits t for v
| pred_2_
  (v : variable_) (P : formula) (t : variable_) :
  admits v t P →
  is_axiom ((forall_ v P).imp_ (replace_free v t P))

-- ⊢ P → (∀ v P)  provided v is not free in P
| pred_3_
  (P : formula) (v : variable_) :
  ¬ is_free_in v P →
  is_axiom (P.imp_ (forall_ v P))

-- ⊢ P ⇒ ⊢ ∀ v P
| gen_
  (P : formula) (v : variable_) :
  is_axiom P →
  is_axiom (forall_ v P)


inductive is_deduct (Δ : set formula) : formula → Prop

| axiom_
  (P : formula) :
  is_axiom P →
  is_deduct P

| assume_
  (P : formula) :
  P ∈ Δ →
  is_deduct P

| mp_
  (P Q : formula) :
  is_deduct (P.imp_ Q) →
  is_deduct P →
  is_deduct Q


def is_proof (P : formula) : Prop := is_deduct ∅ P


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
  is_proof ((not_ P).imp_ (P.imp_ Q)) :=
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


theorem deduction_theorem
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


example
  (P Q : formula) :
  is_proof ((not_ P).imp_ (P.imp_ Q)) :=
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
  is_proof ((not_ (not_ P)).imp_ P) :=
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
  is_proof (P.imp_ (not_ (not_ P))) :=
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
  is_proof ((P.imp_ Q).imp_ ((not_ Q).imp_ (not_ P))) :=
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
  is_proof (Q.imp_((not_ R).imp_ (not_ (Q.imp_ R)))) :=
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
  is_proof ( (S.imp_ P).imp_ (((not_ S).imp_ P).imp_ P) ) :=
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
  apply T_14_10,
  exact h1,

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
  apply T_14_10 Q ∅ h1 Γ,
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
  apply T_14_12 P Q Δ Δ h1 h2,

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
  apply is_deduct.mp_ P Q h2 h1,
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
    apply h2,
    exact h1_1,
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
  apply h2,
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


inductive is_proof_alt : formula → Prop

-- ⊢ P → (Q → P)
| prop_1_
  (P Q : formula) :
  is_proof_alt (P.imp_ (Q.imp_ P))

-- ⊢ (P → (Q → R)) → ((P → Q) → (P → R))
| prop_2_
  (P Q R : formula) :
  is_proof_alt ((P.imp_ (Q.imp_ R)).imp_ ((P.imp_ Q).imp_ (P.imp_ R)))

-- ⊢ (¬ P → ¬ Q) → (Q → P)
| prop_3_
  (P Q : formula) :
  is_proof_alt (((not_ P).imp_ (not_ Q)).imp_ (Q.imp_ P))

-- ⊢ (∀ v (P → Q)) → ((∀ v P) → (∀ v Q))
| pred_1_
  (P Q : formula) (v : variable_) :
  is_proof_alt ((forall_ v (P.imp_ Q)).imp_ ((forall_ v P).imp_ (forall_ v Q)))

-- ⊢ (∀ v P) → P(t/v)  provided P admits t for v
| pred_2_
  (v : variable_) (P : formula) (t : variable_) :
  admits v t P →
  is_proof_alt ((forall_ v P).imp_ (replace_free v t P))

-- ⊢ P → (∀ v P)  provided v is not free in P
| pred_3_
  (P : formula) (v : variable_) :
  ¬ is_free_in v P →
  is_proof_alt (P.imp_ (forall_ v P))

-- ⊢ P ⇒ ⊢ ∀ v P
| gen_
  (P : formula) (v : variable_) :
  is_proof_alt P →
  is_proof_alt (forall_ v P)

-- ⊢ P → Q ⇒ ⊢ P ⇒ ⊢ Q
| mp_
  (P Q : formula) :
  is_proof_alt (P.imp_ Q) →
  is_proof_alt P →
  is_proof_alt Q


lemma generalization
  (P : formula)
  (v : variable_)
  (Δ : set formula)
  (h1 : is_deduct Δ P)
  (h2 : ∀ (H : formula), H ∈ Δ → v ∉ H.free_var_set) :
  is_deduct Δ (forall_ v P) := sorry


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
