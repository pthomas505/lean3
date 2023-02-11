/-
Reference:
First Order Mathematical Logic (Dover Books on Mathematics)
by Angelo Margaris
-/


import metalogic.fol.margaris.binders

open formula


inductive is_deduct (Δ : set formula) : formula → Prop

| prop_1 (P Q : formula) :
  is_deduct (P.imp_ (Q.imp_ P))

| prop_2 (P Q S : formula) :
  is_deduct ((S.imp_ (P.imp_ Q)).imp_ ((S.imp_ P).imp_ (S.imp_ Q)))

| prop_3 (P Q : formula) :
  is_deduct (((not_ Q).imp_ (not_ P)).imp_ (P.imp_ Q))

| pred_1 (P Q : formula) (v : variable_) :
  is_deduct ((forall_ v (P.imp_ Q)).imp_ ((forall_ v P).imp_ (forall_ v Q)))

| pred_2 (v : variable_) (P : formula) (t : variable_) :
  -- $P$ admits $t$ for $v$
  admits v t P →
  -- $P(t/v)$
  is_deduct ((forall_ v P).imp_ (replace_free v t P))

| pred_3 (P : formula) (v : variable_) :
  -- $v$ is not free in $P$
  ¬ is_free_in v P →
  is_deduct (P.imp_ (forall_ v P))

| gen (P : formula) (v : variable_) :
  ∀ (H : formula), H ∈ Δ → v ∉ H.free_var_set →
  v ∈ P.free_var_set →
  is_deduct P →
  is_deduct (forall_ v P)

| assumption_ (P : formula) :
  P ∈ Δ →
  is_deduct P

| mp_ {P Q : formula} :
  -- major premise
  is_deduct (P.imp_ Q) →
  -- minor premise
  is_deduct P →
  is_deduct Q

def is_proof (P : formula) : Prop := is_deduct ∅ P


theorem thm_5
  (P : formula) :
  is_proof (P.imp_ P) :=
begin
  have s1 : is_deduct ∅ ((P.imp_ ((P.imp_ P).imp_ P)).imp_ ((P.imp_ (P.imp_ P)).imp_ (P.imp_ P))),
  apply is_deduct.prop_2,

  have s2 : is_deduct ∅ (P.imp_ ((P.imp_ P).imp_ P)),
  apply is_deduct.prop_1,

  have s3 : is_deduct ∅ ((P.imp_ (P.imp_ P)).imp_ (P.imp_ P)),
  exact is_deduct.mp_ s1 s2,

  have s4 : is_deduct ∅ (P.imp_ (P.imp_ P)),
  apply is_deduct.prop_1,

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
  apply is_deduct.prop_3,

  have s2 : is_deduct ∅ (((Q.not_.imp_ P.not_).imp_ (P.imp_ Q)).imp_ (P.not_.imp_ ((Q.not_.imp_ P.not_).imp_ (P.imp_ Q)))),
  apply is_deduct.prop_1,

  have s3 : is_deduct ∅ (P.not_.imp_ ((Q.not_.imp_ P.not_).imp_ (P.imp_ Q))),
  exact is_deduct.mp_ s2 s1,

  have s4 : is_deduct ∅ ((P.not_.imp_ ((Q.not_.imp_ P.not_).imp_ (P.imp_ Q))).imp_ ((P.not_.imp_ (Q.not_.imp_ P.not_)).imp_ (P.not_.imp_ (P.imp_ Q)))),
  apply is_deduct.prop_2,

  have s5 : is_deduct ∅ ((P.not_.imp_ (Q.not_.imp_ P.not_)).imp_ (P.not_.imp_ (P.imp_ Q))),
  exact is_deduct.mp_ s4 s3,

  have s6 : is_deduct ∅ (P.not_.imp_ (Q.not_.imp_ P.not_)),
  apply is_deduct.prop_1,

  have s7 : is_deduct ∅ (P.not_.imp_ (P.imp_ Q)),
  exact is_deduct.mp_ s5 s6,

  unfold is_proof,
  exact s7,
end


example
  (P Q : formula)
  (Δ : finset formula)
  (h1 : is_deduct (Δ ∪ {P}) Q) :
  is_deduct Δ (P.imp_ Q) :=
begin
  induction h1,
  case is_deduct.prop_1 : h1_P h1_Q
  {
    apply is_deduct.mp_,
    apply is_deduct.prop_1,
    apply is_deduct.prop_1,
  },
  case is_deduct.prop_2 : h1_P h1_Q h1_S
  { admit },
  case is_deduct.prop_3 : h1_P h1_Q
  { admit },
  case is_deduct.pred_1 : h1_P h1_Q h1_v
  { admit },
  case is_deduct.pred_2 : h1_v h1_P h1_t h1_ᾰ
  { admit },
  case is_deduct.pred_3 : h1_P h1_v h1_ᾰ
  { admit },
  case is_deduct.gen : h1_P h1_v h1_H h1_ᾰ h1_ᾰ_1 h1_ᾰ_2 h1_ᾰ_3 h1_ih
  { admit },
  case is_deduct.assumption_ : h1_P h1_ᾰ
  { admit },
  case is_deduct.mp_ : h1_P h1_Q h1_ᾰ h1_ᾰ_1 h1_ih_ᾰ h1_ih_ᾰ_1
  { admit },
end

/-
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
    apply is_axiom.prop_1,

    exact is_deduct.mp_ s2 s1,
  },
  case is_deduct.assumption_ : h1_P h1_1
  {
    simp only [finset.mem_union, finset.mem_singleton] at h1_1,
    cases h1_1,
    {
      -- Case 2

      have s1 : is_deduct Δ h1_P,
      apply is_deduct.assumption_,
      exact h1_1,

      have s2 : is_deduct Δ (h1_P.imp_ (P.imp_ h1_P)),
      apply is_deduct.axiom_,
      apply is_axiom.prop_1,

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
    apply is_axiom.prop_2,

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
  apply is_deduct.assumption_,
  simp only [finset.empty_union, finset.mem_singleton],

  have s2 : is_deduct (∅ ∪ {P.not_}) (P.not_.imp_ (Q.not_.imp_ P.not_)),
  apply is_deduct.axiom_,
  apply is_axiom.prop_1,

  have s3 : is_deduct (∅ ∪ {P.not_}) (Q.not_.imp_ P.not_),
  exact is_deduct.mp_ s2 s1,

  have s4 : is_deduct (∅ ∪ {P.not_}) ((Q.not_.imp_ P.not_).imp_ (P.imp_ Q)),
  apply is_deduct.axiom_,
  apply is_axiom.prop_3,

  have s5 : is_deduct (∅ ∪ {P.not_}) (P.imp_ Q),
  exact is_deduct.mp_ s4 s3,

  apply deduction_theorem,
  exact s5,
end
-/
