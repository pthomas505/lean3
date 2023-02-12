/-
Reference:
First Order Mathematical Logic (Dover Books on Mathematics)
by Angelo Margaris
-/


import metalogic.fol.margaris.binders

open formula


inductive is_proof (Δ : set formula) : formula → Prop

-- ⊢ P → (Q → P)
| prop_1_
  (P Q : formula) :
  is_proof (P.imp_ (Q.imp_ P))

-- ⊢ (P → (Q → R)) → ((P → Q) → (P → R))
| prop_2_
  (P Q R : formula) :
  is_proof ((P.imp_ (Q.imp_ R)).imp_ ((P.imp_ Q).imp_ (P.imp_ R)))

-- ⊢ (¬ P → ¬ Q) → (Q → P)
| prop_3_
  (P Q : formula) :
  is_proof (((not_ P).imp_ (not_ Q)).imp_ (Q.imp_ P))

-- ⊢ (∀ v (P → Q)) → ((∀ v P) → (∀ v Q))
| pred_1_
  (P Q : formula) (v : variable_) :
  is_proof ((forall_ v (P.imp_ Q)).imp_ ((forall_ v P).imp_ (forall_ v Q)))

-- ⊢ (∀ v P) → P(t/v)  provided P admits t for v
| pred_2_
  (v : variable_) (P : formula) (t : variable_) :
  admits v t P →
  is_proof ((forall_ v P).imp_ (replace_free v t P))

-- ⊢ P → (∀ v P)  provided v is not free in P
| pred_3_
  (P : formula) (v : variable_) :
  ¬ is_free_in v P →
  is_proof (P.imp_ (forall_ v P))

-- ⊢ P ⇒ ⊢ ∀ v P  provided v is not free in the hypotheses
| gen_
  (P : formula) (v : variable_) :
  ∀ (H : formula), H ∈ Δ → v ∉ H.free_var_set →
  is_proof P →
  is_proof (forall_ v P)

-- ⊢ P → Q ⇒ ⊢ P ⇒ ⊢ Q 
| mp_
  {P Q : formula} :
  -- major premise
  is_proof (P.imp_ Q) →
  -- minor premise
  is_proof P →
  is_proof Q

-- Δ ∪ {P} ⊢ P
| assume_
  (P : formula) :
  P ∈ Δ →
  is_proof P


theorem thm_5
  (P : formula) :
  is_proof ∅ (P.imp_ P) :=
begin
  have s1 : is_proof ∅ ((P.imp_ ((P.imp_ P).imp_ P)).imp_ ((P.imp_ (P.imp_ P)).imp_ (P.imp_ P))),
  apply is_proof.prop_2_,

  have s2 : is_proof ∅ (P.imp_ ((P.imp_ P).imp_ P)),
  apply is_proof.prop_1_ P (P.imp_ P),

  have s3 : is_proof ∅ ((P.imp_ (P.imp_ P)).imp_ (P.imp_ P)),
  exact is_proof.mp_ s1 s2,

  have s4 : is_proof ∅ (P.imp_ (P.imp_ P)),
  apply is_proof.prop_1_ P P,

  have s5 : is_proof ∅ (P.imp_ P),
  exact is_proof.mp_ s3 s4,

  exact s5,
end


theorem thm_6
  (P Q : formula) :
  is_proof ∅ ((not_ P).imp_ (P.imp_ Q)) :=
begin
  have s1 : is_proof ∅ ((Q.not_.imp_ P.not_).imp_ (P.imp_ Q)),
  apply is_proof.prop_3_,

  have s2 : is_proof ∅ (((Q.not_.imp_ P.not_).imp_ (P.imp_ Q)).imp_ (P.not_.imp_ ((Q.not_.imp_ P.not_).imp_ (P.imp_ Q)))),
  apply is_proof.prop_1_,

  have s3 : is_proof ∅ (P.not_.imp_ ((Q.not_.imp_ P.not_).imp_ (P.imp_ Q))),
  exact is_proof.mp_ s2 s1,

  have s4 : is_proof ∅ ((P.not_.imp_ ((Q.not_.imp_ P.not_).imp_ (P.imp_ Q))).imp_ ((P.not_.imp_ (Q.not_.imp_ P.not_)).imp_ (P.not_.imp_ (P.imp_ Q)))),
  apply is_proof.prop_2_,

  have s5 : is_proof ∅ ((P.not_.imp_ (Q.not_.imp_ P.not_)).imp_ (P.not_.imp_ (P.imp_ Q))),
  exact is_proof.mp_ s4 s3,

  have s6 : is_proof ∅ (P.not_.imp_ (Q.not_.imp_ P.not_)),
  apply is_proof.prop_1_,

  have s7 : is_proof ∅ (P.not_.imp_ (P.imp_ Q)),
  exact is_proof.mp_ s5 s6,

  exact s7,
end


example
  (P Q : formula)
  (Δ : finset formula)
  (h1 : is_proof (Δ ∪ {P}) Q) :
  is_proof Δ (P.imp_ Q) :=
begin
  induction h1,
  case is_proof.prop_1_ : h1_P h1_Q
  {
    apply is_proof.mp_,
    apply is_proof.prop_1_,
    apply is_proof.prop_1_,
  },
  case is_proof.prop_2_ : h1_P h1_Q h1_S
  { admit },
  case is_proof.prop_3_ : h1_P h1_Q
  { admit },
  case is_proof.pred_1_ : h1_P h1_Q h1_v
  { admit },
  case is_proof.pred_2_ : h1_v h1_P h1_t h1_ᾰ
  { admit },
  case is_proof.pred_3_ : h1_P h1_v h1_ᾰ
  { admit },
  case is_proof.gen_ : h1_P h1_v h1_H h1_ᾰ h1_ᾰ_1 h1_ᾰ_2 h1_ᾰ_3 h1_ih
  { admit },
  case is_proof.assume_ : h1_P h1_ᾰ
  { admit },
  case is_proof.mp_ : h1_P h1_Q h1_ᾰ h1_ᾰ_1 h1_ih_ᾰ h1_ih_ᾰ_1
  { admit },
end

/-
theorem proofion_theorem
  (P Q : formula)
  (Δ : finset formula)
  (h1 : is_proof (Δ ∪ {P}) Q) :
  is_proof Δ (P.imp_ Q) :=
begin
  induction h1,
  case is_proof.axiom_ : h1_P h1_1
  {
    -- Case 1

    have s1 : is_proof Δ h1_P,
    apply is_proof.axiom_,
    apply h1_1,

    have s2 : is_proof Δ (h1_P.imp_ (P.imp_ h1_P)),
    apply is_proof.axiom_,
    apply is_axiom.prop_1_,

    exact is_proof.mp_ s2 s1,
  },
  case is_proof.assumption_ : h1_P h1_1
  {
    simp only [finset.mem_union, finset.mem_singleton] at h1_1,
    cases h1_1,
    {
      -- Case 2

      have s1 : is_proof Δ h1_P,
      apply is_proof.assumption_,
      exact h1_1,

      have s2 : is_proof Δ (h1_P.imp_ (P.imp_ h1_P)),
      apply is_proof.axiom_,
      apply is_axiom.prop_1_,

      exact is_proof.mp_ s2 s1,
    },
    {
      -- Case 3

      rewrite h1_1,
      apply proof_imp_proof,
      exact thm_5 P,
    }
  },
  case is_proof.mp_ : h1_P h1_Q h1_1 h1_2 h1_ih_1 h1_ih_2
  {
    -- Case 4

    have s1 : is_proof Δ ((P.imp_ (h1_P.imp_ h1_Q)).imp_ ((P.imp_ h1_P).imp_ (P.imp_ h1_Q))),
    apply is_proof.axiom_,
    apply is_axiom.prop_2_,

    have s2 : is_proof Δ ((P.imp_ h1_P).imp_ (P.imp_ h1_Q)),
    exact is_proof.mp_ s1 h1_ih_1,

    exact is_proof.mp_ s2 h1_ih_2,
  },
end


example
  (P Q : formula) :
  is_proof ((not_ P).imp_ (P.imp_ Q)) :=
begin
  have s1 : is_proof (∅ ∪ {P.not_}) P.not_,
  apply is_proof.assumption_,
  simp only [finset.empty_union, finset.mem_singleton],

  have s2 : is_proof (∅ ∪ {P.not_}) (P.not_.imp_ (Q.not_.imp_ P.not_)),
  apply is_proof.axiom_,
  apply is_axiom.prop_1_,

  have s3 : is_proof (∅ ∪ {P.not_}) (Q.not_.imp_ P.not_),
  exact is_proof.mp_ s2 s1,

  have s4 : is_proof (∅ ∪ {P.not_}) ((Q.not_.imp_ P.not_).imp_ (P.imp_ Q)),
  apply is_proof.axiom_,
  apply is_axiom.prop_3_,

  have s5 : is_proof (∅ ∪ {P.not_}) (P.imp_ Q),
  exact is_proof.mp_ s4 s3,

  apply proofion_theorem,
  exact s5,
end
-/
