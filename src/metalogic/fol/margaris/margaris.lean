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
  {P Q : formula} :
  -- major premise
  is_axiom (P.imp_ Q) →
  -- minor premise
  is_axiom P →
  is_axiom Q


inductive is_deduct (Δ : finset formula) : formula → Prop
| axiom_ (P : formula) :
  is_axiom P →
  is_deduct P

| assume_ (P : formula) :
  P ∈ Δ →
  is_deduct P

| mp_ {P Q : formula} :
  -- major premise
  is_deduct (P.imp_ Q) →
  -- minor premise
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
    exact is_deduct.mp_ h1_ih_1 h1_ih_2,
  },
end


theorem thm_5
  (P : formula) :
  is_proof (P.imp_ P) :=
begin
  have s1 : is_deduct ∅ ((P.imp_ ((P.imp_ P).imp_ P)).imp_ ((P.imp_ (P.imp_ P)).imp_ (P.imp_ P))),
  apply is_deduct.axiom_,
  apply is_axiom.prop_2_,

  have s2 : is_deduct ∅ (P.imp_ ((P.imp_ P).imp_ P)),
  apply is_deduct.axiom_,
  apply is_axiom.prop_1_,

  have s3 : is_deduct ∅ ((P.imp_ (P.imp_ P)).imp_ (P.imp_ P)),
  exact is_deduct.mp_ s1 s2,

  have s4 : is_deduct ∅ (P.imp_ (P.imp_ P)),
  apply is_deduct.axiom_,
  apply is_axiom.prop_1_,

  have s5 : is_deduct ∅ (P.imp_ P),
  exact is_deduct.mp_ s3 s4,

  unfold is_proof,
  exact s5,
end


theorem thm_6
  (P Q : formula) :
  is_proof ((not_ P).imp_ (P.imp_ Q)) :=
begin
  have s1 : is_deduct ∅ ((Q.not_.imp_ P.not_).imp_ (P.imp_ Q)),
  apply is_deduct.axiom_,
  apply is_axiom.prop_3_,

  have s2 : is_deduct ∅ (((Q.not_.imp_ P.not_).imp_ (P.imp_ Q)).imp_ (P.not_.imp_ ((Q.not_.imp_ P.not_).imp_ (P.imp_ Q)))),
  apply is_deduct.axiom_,
  apply is_axiom.prop_1_,

  have s3 : is_deduct ∅ (P.not_.imp_ ((Q.not_.imp_ P.not_).imp_ (P.imp_ Q))),
  exact is_deduct.mp_ s2 s1,

  have s4 : is_deduct ∅ ((P.not_.imp_ ((Q.not_.imp_ P.not_).imp_ (P.imp_ Q))).imp_ ((P.not_.imp_ (Q.not_.imp_ P.not_)).imp_ (P.not_.imp_ (P.imp_ Q)))),
  apply is_deduct.axiom_,
  apply is_axiom.prop_2_,

  have s5 : is_deduct ∅ ((P.not_.imp_ (Q.not_.imp_ P.not_)).imp_ (P.not_.imp_ (P.imp_ Q))),
  exact is_deduct.mp_ s4 s3,

  have s6 : is_deduct ∅ (P.not_.imp_ (Q.not_.imp_ P.not_)),
  apply is_deduct.axiom_,
  apply is_axiom.prop_1_,

  have s7 : is_deduct ∅ (P.not_.imp_ (P.imp_ Q)),
  exact is_deduct.mp_ s5 s6,

  unfold is_proof,
  exact s7,
end


theorem deduction_theorem
  (P Q : formula)
  (Δ : finset formula)
  (h1 : is_deduct (Δ ∪ {P}) Q) :
  is_deduct Δ (P.imp_ Q) :=
begin
  induction h1,
  case is_deduct.axiom_ : h1_P h1_1
  {
    -- Case 1

    have s1 : is_deduct Δ h1_P,
    apply is_deduct.axiom_,
    apply h1_1,

    have s2 : is_deduct Δ (h1_P.imp_ (P.imp_ h1_P)),
    apply is_deduct.axiom_,
    apply is_axiom.prop_1_,

    exact is_deduct.mp_ s2 s1,
  },
  case is_deduct.assume_ : h1_P h1_1
  {
    simp only [finset.mem_union, finset.mem_singleton] at h1_1,
    cases h1_1,
    {
      -- Case 2

      have s1 : is_deduct Δ h1_P,
      apply is_deduct.assume_,
      exact h1_1,

      have s2 : is_deduct Δ (h1_P.imp_ (P.imp_ h1_P)),
      apply is_deduct.axiom_,
      apply is_axiom.prop_1_,

      exact is_deduct.mp_ s2 s1,
    },
    {
      -- Case 3

      rewrite h1_1,
      apply proof_imp_deduct,
      exact thm_5 P,
    }
  },
  case is_deduct.mp_ : h1_P h1_Q h1_1 h1_2 h1_ih_1 h1_ih_2
  {
    -- Case 4

    have s1 : is_deduct Δ ((P.imp_ (h1_P.imp_ h1_Q)).imp_ ((P.imp_ h1_P).imp_ (P.imp_ h1_Q))),
    apply is_deduct.axiom_,
    apply is_axiom.prop_2_,

    have s2 : is_deduct Δ ((P.imp_ h1_P).imp_ (P.imp_ h1_Q)),
    exact is_deduct.mp_ s1 h1_ih_1,

    exact is_deduct.mp_ s2 h1_ih_2,
  },
end


example
  (P Q : formula) :
  is_proof ((not_ P).imp_ (P.imp_ Q)) :=
begin
  have s1 : is_deduct (∅ ∪ {P.not_}) P.not_,
  apply is_deduct.assume_,
  simp only [finset.empty_union, finset.mem_singleton],

  have s2 : is_deduct (∅ ∪ {P.not_}) (P.not_.imp_ (Q.not_.imp_ P.not_)),
  apply is_deduct.axiom_,
  apply is_axiom.prop_1_,

  have s3 : is_deduct (∅ ∪ {P.not_}) (Q.not_.imp_ P.not_),
  exact is_deduct.mp_ s2 s1,

  have s4 : is_deduct (∅ ∪ {P.not_}) ((Q.not_.imp_ P.not_).imp_ (P.imp_ Q)),
  apply is_deduct.axiom_,
  apply is_axiom.prop_3_,

  have s5 : is_deduct (∅ ∪ {P.not_}) (P.imp_ Q),
  exact is_deduct.mp_ s4 s3,

  apply deduction_theorem,
  exact s5,
end
