import metalogic.fol.common.sub.one.rec.sub_one_rec_admits


set_option pp.parens true


namespace fol

open formula


/--
  is_prop_axiom F := True if and only if F is a logical axiom of classical propositional logic.
-/
inductive is_prop_axiom : formula → Prop

-- ⊢ ⊤
| prop_true_ :
  is_prop_axiom true_

-- ⊢ phi → (psi → phi)
| prop_1_
  (phi psi : formula) :
  is_prop_axiom (phi.imp_ (psi.imp_ phi))

-- ⊢ (phi → (psi → chi)) → ((phi → psi) → (phi → chi))
| prop_2_
  (phi psi chi : formula) :
  is_prop_axiom ((phi.imp_ (psi.imp_ chi)).imp_ ((phi.imp_ psi).imp_ (phi.imp_ chi)))

-- ⊢ (¬ phi → ¬ psi) → (psi → phi)
| prop_3_
  (phi psi : formula) :
  is_prop_axiom (((not_ phi).imp_ (not_ psi)).imp_ (psi.imp_ phi))


/--
  is_prop_deduct Δ F := True if and only if there is a deduction of F from Δ in classical propositional logic.
-/
inductive is_prop_deduct (Δ : set formula) : formula → Prop

| axiom_
  (phi : formula) :
  is_prop_axiom phi →
  is_prop_deduct phi

| assume_
  (phi : formula) :
  phi ∈ Δ →
  is_prop_deduct phi

| mp_
  (phi psi : formula) :
  is_prop_deduct (phi.imp_ psi) →
  is_prop_deduct phi →
  is_prop_deduct psi


/--
  is_prop_proof F := True if and only if there is a proof of F in classical propositional logic.
-/
def is_prop_proof (phi : formula) : Prop := is_prop_deduct ∅ phi


/--
  is_axiom F := True if and only if F is a logical axiom of classical first order logic.
-/
inductive is_axiom : formula → Prop

-- ⊢ ⊤
| prop_true_ :
  is_axiom true_

-- ⊢ phi → (psi → phi)
| prop_1_
  (phi psi : formula) :
  is_axiom (phi.imp_ (psi.imp_ phi))

-- ⊢ (phi → (psi → chi)) → ((phi → psi) → (phi → chi))
| prop_2_
  (phi psi chi : formula) :
  is_axiom ((phi.imp_ (psi.imp_ chi)).imp_ ((phi.imp_ psi).imp_ (phi.imp_ chi)))

-- ⊢ (¬ phi → ¬ psi) → (psi → phi)
| prop_3_
  (phi psi : formula) :
  is_axiom (((not_ phi).imp_ (not_ psi)).imp_ (psi.imp_ phi))

-- ⊢ (∀ v (phi → psi)) → ((∀ v phi) → (∀ v psi))
| pred_1_
  (v : var_name) (phi psi : formula) :
  is_axiom ((forall_ v (phi.imp_ psi)).imp_ ((forall_ v phi).imp_ (forall_ v psi)))

-- ⊢ (∀ v phi) → phi(t/v)  provided phi admits t for v
| pred_2_
  (v t : var_name) (phi phi' : formula) :
  fast_admits v t phi →
  fast_replace_free v t phi = phi' →
  is_axiom ((forall_ v phi).imp_ phi')

-- ⊢ phi → (∀ v phi)  provided v is not free in phi
| pred_3_
  (v : var_name) (phi : formula) :
  ¬ is_free_in v phi →
  is_axiom (phi.imp_ (forall_ v phi))

-- ⊢ ∀ v (v = v)
| eq_1_
  (v : var_name) :
  is_axiom (forall_ v (eq_ v v))

/-
⊢ ∀ x_0 ... ∀ x_n ∀ y_0 ... y_n ((x_0 = y_0) ∧ ... ∧ (x_n = y_n) ∧ ⊤) →
    ((pred_ name [x_0 ... x_n] ↔ pred_ name [y_0 ... y_n]))
-/
| eq_2_pred_
  (name : pred_name) (n : ℕ) (xs ys : fin n → var_name) :
  is_axiom (Forall_ (list.of_fn xs) (Forall_ (list.of_fn ys)
    ((And_ (list.of_fn (fun (i : fin n), eq_ (xs i) (ys i)))).imp_
      ((pred_ name (list.of_fn xs)).iff_ (pred_ name (list.of_fn ys))))))

/-
⊢ ∀ x_0 ∀ x_1 ∀ y_0 ∀ y_1 ((x_0 = y_0) ∧ (x_1 = y_1)) →
    ((eq_ x_0 x_1) ↔ (eq_ y_0 y_1))
-/
| eq_2_eq_
  (x_0 x_1 y_0 y_1 : var_name) :
  is_axiom (forall_ x_0 (forall_ x_1 (forall_ y_0 (forall_ y_1 ((and_ (eq_ x_0 y_0) (eq_ x_1 y_1)).imp_
    ((eq_ x_0 x_1).iff_ (eq_ y_0 y_1)))))))

-- ⊢ phi ⇒ ⊢ ∀ v phi
| gen_
  (v : var_name) (phi : formula) :
  is_axiom phi →
  is_axiom (forall_ v phi)


/--
  is_deduct Δ F := True if and only if there is a deduction of F from Δ in classical first order logic.
-/
inductive is_deduct (Δ : set formula) : formula → Prop

| axiom_
  (phi : formula) :
  is_axiom phi →
  is_deduct phi

| assume_
  (phi : formula) :
  phi ∈ Δ →
  is_deduct phi

| mp_
  (phi psi : formula) :
  is_deduct (phi.imp_ psi) →
  is_deduct phi →
  is_deduct psi


/--
  is_proof F := True if and only if there is a proof of F in classical first order logic.
-/
def is_proof (F : formula) : Prop := is_deduct ∅ F


/--
  is_proof_alt F := True if and only if there is a proof of F in classical first order logic.

  This definition is equivalent to is_proof.
-/
inductive is_proof_alt : formula → Prop

-- ⊢ ⊤
| prop_true_ :
  is_proof_alt true_

-- ⊢ phi → (psi → phi)
| prop_1_
  (phi psi : formula) :
  is_proof_alt (phi.imp_ (psi.imp_ phi))

-- ⊢ (phi → (psi → chi)) → ((phi → psi) → (phi → chi))
| prop_2_
  (phi psi chi : formula) :
  is_proof_alt ((phi.imp_ (psi.imp_ chi)).imp_ ((phi.imp_ psi).imp_ (phi.imp_ chi)))

-- ⊢ (¬ phi → ¬ psi) → (psi → phi)
| prop_3_
  (phi psi : formula) :
  is_proof_alt (((not_ phi).imp_ (not_ psi)).imp_ (psi.imp_ phi))

-- ⊢ (∀ v (phi → psi)) → ((∀ v phi) → (∀ v psi))
| pred_1_
  (v : var_name) (phi psi : formula) :
  is_proof_alt ((forall_ v (phi.imp_ psi)).imp_ ((forall_ v phi).imp_ (forall_ v psi)))

-- ⊢ (∀ v phi) → phi(t/v)  provided phi admits t for v
| pred_2_
  (v t : var_name) (phi phi' : formula) :
  fast_admits v t phi →
  fast_replace_free v t phi = phi' →
  is_proof_alt ((forall_ v phi).imp_ phi')

-- ⊢ phi → (∀ v phi)  provided v is not free in phi
| pred_3_
  (v : var_name) (phi : formula) :
  ¬ is_free_in v phi →
  is_proof_alt (phi.imp_ (forall_ v phi))

-- ⊢ ∀ v (v = v)
| eq_1_
  (v : var_name) :
  is_proof_alt (forall_ v (eq_ v v))

/-
⊢ ∀ x_0 ... ∀ x_n ∀ y_0 ... y_n ((x_0 = y_0) ∧ ... ∧ (x_n = y_n) ∧ ⊤) →
    ((pred_ name [x_0 ... x_n] ↔ pred_ name [y_0 ... y_n]))
-/
| eq_2_pred_
  (name : pred_name) (n : ℕ) (xs ys : fin n → var_name) :
  is_proof_alt (Forall_ (list.of_fn xs) (Forall_ (list.of_fn ys)
    ((And_ (list.of_fn (fun (i : fin n), eq_ (xs i) (ys i)))).imp_
      ((pred_ name (list.of_fn xs)).iff_ (pred_ name (list.of_fn ys))))))

/-
⊢ ∀ x_0 ∀ x_1 ∀ y_0 ∀ y_1 ((x_0 = y_0) ∧ (x_1 = y_1)) →
    ((eq_ x_0 x_1) ↔ (eq_ y_0 y_1))
-/
| eq_2_eq_
  (x_0 x_1 y_0 y_1 : var_name) :
  is_proof_alt (forall_ x_0 (forall_ x_1 (forall_ y_0 (forall_ y_1 ((and_ (eq_ x_0 y_0) (eq_ x_1 y_1)).imp_
    ((eq_ x_0 x_1).iff_ (eq_ y_0 y_1)))))))

-- ⊢ phi ⇒ ⊢ ∀ v phi
| gen_
  (v : var_name) (phi : formula) :
  is_proof_alt phi →
  is_proof_alt (forall_ v phi)

-- ⊢ phi → psi ⇒ ⊢ phi ⇒ ⊢ psi
| mp_
  (phi psi : formula) :
  is_proof_alt (phi.imp_ psi) →
  is_proof_alt phi →
  is_proof_alt psi


#lint

end fol
