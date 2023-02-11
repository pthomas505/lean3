/-
Reference:
First Order Mathematical Logic (Dover Books on Mathematics)
by Angelo Margaris
-/


import metalogic.fol.margaris.binders

open formula


inductive is_axiom : formula → Prop

| prop_1 (P Q : formula) :
  is_axiom (P.imp_ (Q.imp_ P))

| prop_2 (P Q S : formula) :
  is_axiom ((S.imp_ (P.imp_ Q)).imp_ ((S.imp_ P).imp_ (S.imp_ Q)))

| prop_3 (P Q : formula) :
  is_axiom (((not_ Q).imp_ (not_ P)).imp_ (P.imp_ Q))

| pred_1 (P Q : formula) (v : variable_) :
  is_axiom ((forall_ v (P.imp_ Q)).imp_ ((forall_ v P).imp_ (forall_ v Q)))

| pred_2 (v : variable_) (P : formula) (t : variable_) :
  -- $P$ admits $t$ for $v$
  admits v t P →
  -- $P(t/v)$
  is_axiom ((forall_ v P).imp_ (replace_free v t P))

| pred_3 (P : formula) (v : variable_) :
  -- $v$ is not free in $P$
  ¬ is_free_in v P →
  is_axiom (P.imp_ (forall_ v P))

| gen (P : formula) (v : variable_) :
  is_axiom P →
  v ∈ P.free_var_set →
  is_axiom (forall_ v P)


inductive is_deduct (Δ : finset formula) : formula → Prop
| axiom_ (P : formula) :
  is_axiom P →
  is_deduct P

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
  case is_deduct.assumption_ : h1_P h1_1
  {
    simp only [finset.not_mem_empty] at h1_1,
    contradiction,
  },
  case is_deduct.mp_ : h1_P h1_Q h1_1 h1_2 h1_ih_1 h1_ih_2
  {
    exact is_deduct.mp_ h1_ih_1 h1_ih_2,
  },
end


inductive is_deduct_simp (Δ : finset formula) : formula → Prop

| prop_1 (P Q : formula) :
  is_deduct_simp (P.imp_ (Q.imp_ P))

| prop_2 (P Q S : formula) :
  is_deduct_simp ((S.imp_ (P.imp_ Q)).imp_ ((S.imp_ P).imp_ (S.imp_ Q)))

| prop_3 (P Q : formula) :
  is_deduct_simp (((not_ Q).imp_ (not_ P)).imp_ (P.imp_ Q))

| pred_1 (P Q : formula) (v : variable_) :
  is_deduct_simp ((forall_ v (P.imp_ Q)).imp_ ((forall_ v P).imp_ (forall_ v Q)))

| pred_2 (v : variable_) (P : formula) (t : variable_) :
  -- $P$ admits $t$ for $v$
  admits v t P →
  -- $P(t/v)$
  is_deduct_simp ((forall_ v P).imp_ (replace_free v t P))

| pred_3 (P : formula) (v : variable_) :
  -- $v$ is not free in $P$
  ¬ is_free_in v P →
  is_deduct_simp (P.imp_ (forall_ v P))

| gen (P : formula) (v : variable_) :
  is_deduct_simp P →
  v ∈ P.free_var_set →
  is_deduct_simp (forall_ v P)

| assumption_ (P : formula) :
  P ∈ Δ →
  is_deduct_simp P

| mp_ {P Q : formula} :
  -- major premise
  is_deduct_simp (P.imp_ Q) →
  -- minor premise
  is_deduct_simp P →
  is_deduct_simp Q


example
  (Δ : finset formula)
  (P : formula)
  (h1 : is_deduct_simp Δ P) :
  is_deduct Δ P :=
begin
  induction h1,
  case is_deduct_simp.prop_1 : h1_P h1_Q
  {
    apply is_deduct.axiom_,
    apply is_axiom.prop_1,
  },
  case is_deduct_simp.prop_2 : h1_P h1_Q h1_S
  { admit },
  case is_deduct_simp.prop_3 : h1_P h1_Q
  { admit },
  case is_deduct_simp.pred_1 : h1_P h1_Q h1_v
  { admit },
  case is_deduct_simp.pred_2 : h1_v h1_P h1_t h1_ᾰ
  { admit },
  case is_deduct_simp.pred_3 : h1_P h1_v h1_ᾰ
  { admit },
  case is_deduct_simp.gen : h1_P h1_v h1_ᾰ h1_ᾰ_1 h1_ih
  { admit },
  case is_deduct_simp.assumption_ : h1_P h1_1
  {
    exact is_deduct.assumption_ h1_P h1_1,
  },
  case is_deduct_simp.mp_ : h1_P h1_Q h1_1 h1_2 h1_ih_1 h1_ih_2
  {
    exact is_deduct.mp_ h1_ih_1 h1_ih_2,
  },
end


example
  (Δ : finset formula)
  (P : formula)
  (h1 : is_deduct Δ P) :
  is_deduct_simp Δ P :=
begin
  induction h1,
  case is_deduct.axiom_ : h1_P h1_1
  {
    induction h1_1,
    case is_axiom.prop_1 : h1_1_P h1_1_Q
    { admit },
    case is_axiom.prop_2 : h1_1_P h1_1_Q h1_1_S
    { admit },
    case is_axiom.prop_3 : h1_1_P h1_1_Q
    { admit },
    case is_axiom.pred_1 : h1_1_P h1_1_Q h1_1_v
    { admit },
    case is_axiom.pred_2 : h1_1_v h1_1_P h1_1_t h1_1_ᾰ
    { admit },
    case is_axiom.pred_3 : h1_1_P h1_1_v h1_1_ᾰ
    { admit },
    case is_axiom.gen : h1_1_P h1_1_v h1_1_ᾰ h1_1_ᾰ_1 h1_1_ih
    { admit },
  },
  case is_deduct.assumption_ : h1_P h1_ᾰ
  { admit },
  case is_deduct.mp_ : h1_P h1_Q h1_ᾰ h1_ᾰ_1 h1_ih_ᾰ h1_ih_ᾰ_1
  { admit },
end


theorem thm_5
  (P : formula) :
  is_proof (P.imp_ P) :=
begin
  have s1 : is_deduct ∅ ((P.imp_ ((P.imp_ P).imp_ P)).imp_ ((P.imp_ (P.imp_ P)).imp_ (P.imp_ P))),
  apply is_deduct.axiom_,
  apply is_axiom.prop_2,

  have s2 : is_deduct ∅ (P.imp_ ((P.imp_ P).imp_ P)),
  apply is_deduct.axiom_,
  apply is_axiom.prop_1,

  have s3 : is_deduct ∅ ((P.imp_ (P.imp_ P)).imp_ (P.imp_ P)),
  exact is_deduct.mp_ s1 s2,

  have s4 : is_deduct ∅ (P.imp_ (P.imp_ P)),
  apply is_deduct.axiom_,
  apply is_axiom.prop_1,

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
  apply is_axiom.prop_3,

  have s2 : is_deduct ∅ (((Q.not_.imp_ P.not_).imp_ (P.imp_ Q)).imp_ (P.not_.imp_ ((Q.not_.imp_ P.not_).imp_ (P.imp_ Q)))),
  apply is_deduct.axiom_,
  apply is_axiom.prop_1,

  have s3 : is_deduct ∅ (P.not_.imp_ ((Q.not_.imp_ P.not_).imp_ (P.imp_ Q))),
  exact is_deduct.mp_ s2 s1,

  have s4 : is_deduct ∅ ((P.not_.imp_ ((Q.not_.imp_ P.not_).imp_ (P.imp_ Q))).imp_ ((P.not_.imp_ (Q.not_.imp_ P.not_)).imp_ (P.not_.imp_ (P.imp_ Q)))),
  apply is_deduct.axiom_,
  apply is_axiom.prop_2,

  have s5 : is_deduct ∅ ((P.not_.imp_ (Q.not_.imp_ P.not_)).imp_ (P.not_.imp_ (P.imp_ Q))),
  exact is_deduct.mp_ s4 s3,

  have s6 : is_deduct ∅ (P.not_.imp_ (Q.not_.imp_ P.not_)),
  apply is_deduct.axiom_,
  apply is_axiom.prop_1,

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
