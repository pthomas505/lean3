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

-- ⊢ P ⇒ ⊢ ∀ v P  provided v is not free in any of the assumptions
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
