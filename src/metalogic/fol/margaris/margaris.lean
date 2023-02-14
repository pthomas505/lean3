/-
Reference:
First Order Mathematical Logic (Dover Books on Mathematics)
by Angelo Margaris
-/


import metalogic.fol.margaris.binders

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

-- ⊢ P → Q ⇒ ⊢ P ⇒ ⊢ Q 
| mp_
  (P Q : formula) :
  -- major premise
  is_axiom (P.imp_ Q) →
  -- minor premise
  is_axiom P →
  is_axiom Q


inductive is_deduct (Δ : finset formula) : formula → Prop
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
  ∀ (Δ : finset formula), is_deduct Δ P :=
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
    simp only [finset.not_mem_empty] at h1_1,
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


theorem DT
  (P Q : formula)
  (Δ : finset formula)
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
    simp only [finset.mem_union, finset.mem_singleton] at h1_1,
    cases h1_1,
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
    },
    {
      -- Case 3

      rewrite h1_1,
      apply proof_imp_deduct,
      exact T_13_5 P,
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

  apply DT,

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
    simp only [finset.empty_union, finset.mem_singleton],
    },
  },
end


theorem T_14_5
  (P : formula) :
  is_proof ((not_ (not_ P)).imp_ P) :=
begin
  unfold is_proof,

  apply DT,
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
        simp only [finset.empty_union, finset.mem_singleton],
      }
    }
  },
  {
    apply is_deduct.assume_,
    simp only [finset.empty_union, finset.mem_singleton],
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

  apply DT,
  apply is_deduct.mp_,
  {
    apply is_deduct.axiom_,
    apply is_axiom.prop_3_,
  },
  {
    apply DT,
    apply is_deduct.mp_,
    {
      apply proof_imp_deduct,
      apply T_14_6,
    },
    {
      apply is_deduct.mp_,
      {
        apply is_deduct.assume_,
        simp only [finset.empty_union, finset.mem_union, finset.mem_singleton, eq_self_iff_true, and_true, or_false],
      },
      {
        apply is_deduct.mp_,
        {
          apply proof_imp_deduct,
          apply T_14_5,
        },
        {
          apply is_deduct.assume_,
          simp only [finset.empty_union, finset.mem_union, finset.mem_singleton, false_or],
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

  apply DT,
  apply is_deduct.mp_,
  {
    apply proof_imp_deduct,
    apply T_14_7,
  },
  {
    apply DT,
    apply is_deduct.mp_ Q R,
    {
      apply is_deduct.assume_,
      simp only [finset.mem_union, finset.mem_singleton, eq_self_iff_true, and_self, or_true],
    },
    {
      apply is_deduct.assume_,
      simp only [finset.empty_union, finset.mem_union, finset.mem_singleton, eq_self_iff_true, true_or],
    }
  }
end


theorem T_14_9
  (P S : formula) :
  is_proof ( (S.imp_ P).imp_ (((not_ S).imp_ P).imp_ P) ) :=
begin
  unfold is_proof,

  apply DT,
  apply is_deduct.mp_,
  {
    apply is_deduct.axiom_,
    apply is_axiom.prop_3_,
  },
  {
    apply DT,
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
            simp only [finset.empty_union, finset.mem_union, finset.mem_singleton, eq_self_iff_true, and_self, or_false],
          }
        },
        {
          apply is_deduct.assume_,
          simp only [finset.empty_union, finset.mem_union, finset.mem_singleton, false_or],
        }
      }
    },
    {
      apply is_deduct.assume_,
      simp only [finset.empty_union, finset.mem_union, finset.mem_singleton, false_or],
    }
  }
end


theorem T_14_10
  (Q : formula)
  (Δ : finset formula)
  (h1 : is_deduct Δ Q) :
  ∀ (Γ : finset formula), is_deduct (Δ ∪ Γ) Q :=
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
    simp only [finset.mem_union],
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


theorem C_14_11
  (Q : formula)
  (h1 : is_proof Q) :
  ∀ (Γ : finset formula), is_deduct Γ Q :=
begin
  unfold is_proof at h1,

  intros Γ,
  rewrite <- finset.union_empty Γ,
  rewrite finset.union_comm,
  apply T_14_10 Q ∅ h1 Γ,
end


theorem T_14_12
  (P Q : formula)
  (Δ Γ : finset formula)
  (h1 : is_deduct Δ P)
  (h2 : is_deduct Γ (P.imp_ Q)) :
  is_deduct (Δ ∪ Γ) Q :=
begin
  have s1 : is_deduct (Δ ∪ Γ) P,
  apply T_14_10,
  exact h1,

  have s2 : is_deduct (Δ ∪ Γ) (P.imp_ Q),
  rewrite finset.union_comm,
  apply T_14_10,
  exact h2,

  exact is_deduct.mp_ P Q s2 s1,
end
