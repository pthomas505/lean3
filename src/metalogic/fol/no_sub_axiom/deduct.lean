import metalogic.fol.common.binders


set_option pp.parens true


open formula


/--
  is_proof P := True if and only if there is a proof of P in classical first order logic.
-/
inductive is_proof : formula → Prop

-- ⊢ ⊤
| prop_true_ :
  is_proof true_

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
  (v : variable_) (P Q : formula) :
  is_proof ((forall_ v (P.imp_ Q)).imp_ ((forall_ v P).imp_ (forall_ v Q)))

-- ⊢ P → (∀ v P)  provided v is not free in P
| pred_2_
  (v : variable_) (P : formula) :
  ¬ is_free_in v P →
  is_proof (P.imp_ (forall_ v P))

| eq_1_
  (x t : variable_) :
  ¬ x = t →
  is_proof (exists_ x (eq_ x t))

| eq_2_
  (x : variable_) :
  is_proof (eq_ x x)

/-
⊢ (x_0 = y_0) → ... → (x_n = y_n) →
    pred_ name [x_0 ... x_n] → pred_ name [y_0 ... y_n]
-/
| eq_3_pred_
  (name : pred_name_) (n : ℕ) (xs ys : fin n → variable_) :
  is_proof
    (list.foldr formula.imp_ ((pred_ name (list.of_fn xs)).imp_ (pred_ name (list.of_fn ys))) (list.of_fn (fun (i : fin n), eq_ (xs i) (ys i))))

/-
⊢ (x_0 = y_0) → (x_1 = y_1) →
    (eq_ x_0 x_1) → (eq_ y_0 y_1)
-/
| eq_3_eq_
  (x_0 x_1 y_0 y_1 : variable_) :
  is_proof ((eq_ x_0 y_0).imp_ ((eq_ x_1 y_1).imp_
    ((eq_ x_0 x_1).imp_ (eq_ y_0 y_1))))

-- ⊢ P ⇒ ⊢ ∀ v P
| gen_
  (v : variable_) (P : formula) :
  is_proof P →
  is_proof (forall_ v P)

-- ⊢ P → Q ⇒ ⊢ P ⇒ ⊢ Q
| mp_
  (P Q : formula) :
  is_proof (P.imp_ Q) →
  is_proof P →
  is_proof Q


#lint
