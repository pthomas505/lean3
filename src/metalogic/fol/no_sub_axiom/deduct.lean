import metalogic.fol.base.admits


set_option pp.parens true


open formula


/--
  is_axiom_no_sub P := True if and only if P is a logical axiom of classical first order logic.
-/
inductive is_axiom_no_sub : formula → Prop

-- ⊢ ⊤
| prop_true_ :
  is_axiom_no_sub true_

-- ⊢ P → (Q → P)
| prop_1_
  (P Q : formula) :
  is_axiom_no_sub (P.imp_ (Q.imp_ P))

-- ⊢ (P → (Q → R)) → ((P → Q) → (P → R))
| prop_2_
  (P Q R : formula) :
  is_axiom_no_sub ((P.imp_ (Q.imp_ R)).imp_ ((P.imp_ Q).imp_ (P.imp_ R)))

-- ⊢ (¬ P → ¬ Q) → (Q → P)
| prop_3_
  (P Q : formula) :
  is_axiom_no_sub (((not_ P).imp_ (not_ Q)).imp_ (Q.imp_ P))

-- ⊢ (∀ v (P → Q)) → ((∀ v P) → (∀ v Q))
| pred_1_
  (v : variable_) (P Q : formula) :
  is_axiom_no_sub ((forall_ v (P.imp_ Q)).imp_ ((forall_ v P).imp_ (forall_ v Q)))

-- ⊢ P → (∀ v P)  provided v is not free in P
| pred_2_
  (v : variable_) (P : formula) :
  ¬ is_free_in v P →
  is_axiom_no_sub (P.imp_ (forall_ v P))

| eq_1_
  (x y : variable_) :
  is_axiom_no_sub (exists_ x (eq_ x y))

| eq_2_
  (x y z : variable_) :
  is_axiom_no_sub ((eq_ x y).imp_ ((eq_ x z).imp_ (eq_ y z)))

/-
⊢ ∀ x_0 ... ∀ x_n ∀ y_0 ... y_n ((x_0 = y_0) ∧ ... ∧ (x_n = y_n) ∧ ⊤) →
    ((pred_ name [x_0 ... x_n] ↔ pred_ name [y_0 ... y_n]))
-/
| eq_3_pred_
  (name : pred_name_) (n : ℕ) (xs ys : fin n → variable_) :
  is_axiom_no_sub (Forall_ (list.of_fn xs) (Forall_ (list.of_fn ys)
    ((And_ (list.of_fn (fun (i : fin n), eq_ (xs i) (ys i)))).imp_
      ((pred_ name (list.of_fn xs)).iff_ (pred_ name (list.of_fn ys))))))

/-
⊢ ∀ x_0 ∀ x_1 ∀ y_0 ∀ y_1 ((x_0 = y_0) ∧ (x_1 = y_1)) →
    ((eq_ x_0 x_1) ↔ (eq_ y_0 y_1))
-/
| eq_3_eq_
  (x_0 x_1 y_0 y_1 : variable_) :
  is_axiom_no_sub (forall_ x_0 (forall_ x_1 (forall_ y_0 (forall_ y_1 ((and_ (eq_ x_0 y_0) (eq_ x_1 y_1)).imp_
    ((eq_ x_0 x_1).iff_ (eq_ y_0 y_1)))))))

-- ⊢ P ⇒ ⊢ ∀ v P
| gen_
  (v : variable_) (P : formula) :
  is_axiom_no_sub P →
  is_axiom_no_sub (forall_ v P)


inductive is_deduct_no_sub (Δ : set formula) : formula → Prop

| axiom_
  (P : formula) :
  is_axiom_no_sub P →
  is_deduct_no_sub P

| assume_
  (P : formula) :
  P ∈ Δ →
  is_deduct_no_sub P

| mp_
  (P Q : formula) :
  is_deduct_no_sub (P.imp_ Q) →
  is_deduct_no_sub P →
  is_deduct_no_sub Q


/--
  is_proof_no_sub P := True if and only if there is a proof of P in classical first order logic.
-/
inductive is_proof_no_sub : formula → Prop

-- ⊢ ⊤
| prop_true_ :
  is_proof_no_sub true_

-- ⊢ P → (Q → P)
| prop_1_
  (P Q : formula) :
  is_proof_no_sub (P.imp_ (Q.imp_ P))

-- ⊢ (P → (Q → R)) → ((P → Q) → (P → R))
| prop_2_
  (P Q R : formula) :
  is_proof_no_sub ((P.imp_ (Q.imp_ R)).imp_ ((P.imp_ Q).imp_ (P.imp_ R)))

-- ⊢ (¬ P → ¬ Q) → (Q → P)
| prop_3_
  (P Q : formula) :
  is_proof_no_sub (((not_ P).imp_ (not_ Q)).imp_ (Q.imp_ P))

-- ⊢ (∀ v (P → Q)) → ((∀ v P) → (∀ v Q))
| pred_1_
  (v : variable_) (P Q : formula) :
  is_proof_no_sub ((forall_ v (P.imp_ Q)).imp_ ((forall_ v P).imp_ (forall_ v Q)))

-- ⊢ P → (∀ v P)  provided v is not free in P
| pred_2_
  (v : variable_) (P : formula) :
  ¬ is_free_in v P →
  is_proof_no_sub (P.imp_ (forall_ v P))

| eq_1_
  (x y : variable_) :
  is_proof_no_sub (exists_ x (eq_ x y))

| eq_2_
  (x y z : variable_) :
  is_proof_no_sub ((eq_ x y).imp_ ((eq_ x z).imp_ (eq_ y z)))

/-
⊢ ∀ x_0 ... ∀ x_n ∀ y_0 ... y_n ((x_0 = y_0) ∧ ... ∧ (x_n = y_n) ∧ ⊤) →
    ((pred_ name [x_0 ... x_n] ↔ pred_ name [y_0 ... y_n]))
-/
| eq_3_pred_
  (name : pred_name_) (n : ℕ) (xs ys : fin n → variable_) :
  is_proof_no_sub (Forall_ (list.of_fn xs) (Forall_ (list.of_fn ys)
    ((And_ (list.of_fn (fun (i : fin n), eq_ (xs i) (ys i)))).imp_
      ((pred_ name (list.of_fn xs)).iff_ (pred_ name (list.of_fn ys))))))

/-
⊢ ∀ x_0 ∀ x_1 ∀ y_0 ∀ y_1 ((x_0 = y_0) ∧ (x_1 = y_1)) →
    ((eq_ x_0 x_1) ↔ (eq_ y_0 y_1))
-/
| eq_3_eq_
  (x_0 x_1 y_0 y_1 : variable_) :
  is_proof_no_sub (forall_ x_0 (forall_ x_1 (forall_ y_0 (forall_ y_1 ((and_ (eq_ x_0 y_0) (eq_ x_1 y_1)).imp_
    ((eq_ x_0 x_1).iff_ (eq_ y_0 y_1)))))))

-- ⊢ P ⇒ ⊢ ∀ v P
| gen_
  (v : variable_) (P : formula) :
  is_proof_no_sub P →
  is_proof_no_sub (forall_ v P)

-- ⊢ P → Q ⇒ ⊢ P ⇒ ⊢ Q
| mp_
  (P Q : formula) :
  is_proof_no_sub (P.imp_ Q) →
  is_proof_no_sub P →
  is_proof_no_sub Q
