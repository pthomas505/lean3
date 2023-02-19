import .binders


set_option pp.parens true


open formula


inductive is_prop_axiom : formula → Prop

-- ⊢ P → (Q → P)
| prop_1_
  (P Q : formula) :
  is_prop_axiom (P.imp_ (Q.imp_ P))

-- ⊢ (P → (Q → R)) → ((P → Q) → (P → R))
| prop_2_
  (P Q R : formula) :
  is_prop_axiom ((P.imp_ (Q.imp_ R)).imp_ ((P.imp_ Q).imp_ (P.imp_ R)))

-- ⊢ (¬ P → ¬ Q) → (Q → P)
| prop_3_
  (P Q : formula) :
  is_prop_axiom (((not_ P).imp_ (not_ Q)).imp_ (Q.imp_ P))


inductive is_prop_deduct (Δ : set formula) : formula → Prop

| axiom_
  (P : formula) :
  is_prop_axiom P →
  is_prop_deduct P

| assume_
  (P : formula) :
  P ∈ Δ →
  is_prop_deduct P

| mp_
  (P Q : formula) :
  is_prop_deduct (P.imp_ Q) →
  is_prop_deduct P →
  is_prop_deduct Q


def is_prop_proof (P : formula) : Prop := is_prop_deduct ∅ P


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
