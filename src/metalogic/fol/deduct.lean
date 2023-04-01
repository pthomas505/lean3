import .admits


set_option pp.parens true


open formula


/--
  is_prop_axiom P := True if and only if P is a logical axiom of classical propositional logic.
-/
inductive is_prop_axiom : formula → Prop

-- ⊢ ⊤
| prop_true_ :
  is_prop_axiom true_

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


/--
  is_prop_deduct Δ P := True if and only if there is a deduction of P from Δ in classical propositional logic.
-/
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


/--
  is_prop_proof P := True if and only if there is a proof of P in classical propositional logic.
-/
def is_prop_proof (P : formula) : Prop := is_prop_deduct ∅ P


/--
  is_axiom P := True if and only if P is a logical axiom of classical first order logic.
-/
inductive is_axiom : formula → Prop

-- ⊢ ⊤
| prop_true_ :
  is_axiom true_

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
  (v : variable_) (P Q : formula) :
  is_axiom ((forall_ v (P.imp_ Q)).imp_ ((forall_ v P).imp_ (forall_ v Q)))

-- ⊢ (∀ v P) → P(t/v)  provided P admits t for v
| pred_2_
  (v t : variable_) (P P' : formula) :
  fast_admits v t P →
  fast_replace_free v t P = P' →
  is_axiom ((forall_ v P).imp_ P')

-- ⊢ P → (∀ v P)  provided v is not free in P
| pred_3_
  (v : variable_) (P : formula) :
  ¬ is_free_in v P →
  is_axiom (P.imp_ (forall_ v P))

-- ⊢ ∀ v (v = v)
| eq_1_
  (v : variable_) :
  is_axiom (forall_ v (eq_ v v))

/-
⊢ ∀ x_0 ... ∀ x_n ∀ y_0 ... y_n ((x_0 = y_0) ∧ ... ∧ (x_n = y_n) ∧ ⊤) →
    ((pred_ name [x_0 ... x_n] ↔ pred_ name [y_0 ... y_n]))
-/
| eq_2_pred_
  (name : pred_name_) (n : ℕ) (xs ys : fin n → variable_) :
  is_axiom (Forall_ (list.of_fn xs) (Forall_ (list.of_fn ys)
    ((And_ (list.of_fn (fun (i : fin n), eq_ (xs i) (ys i)))).imp_
      ((pred_ name (list.of_fn xs)).iff_ (pred_ name (list.of_fn ys))))))

/-
⊢ ∀ x_0 ∀ x_1 ∀ y_0 ∀ y_1 ((x_0 = y_0) ∧ (x_1 = y_1)) → ((eq_ x_0 x_1) ↔ (eq_ y_0 y_1))
-/
| eq_2_eq_
  (x_0 x_1 y_0 y_1 : variable_) :
  is_axiom (forall_ x_0 (forall_ x_1 (forall_ y_0 (forall_ y_1 ((and_ (eq_ x_0 y_0) (eq_ x_1 y_1)).imp_
    ((eq_ x_0 x_1).iff_ (eq_ y_0 y_1)))))))

-- ⊢ P ⇒ ⊢ ∀ v P
| gen_
  (v : variable_) (P : formula) :
  is_axiom P →
  is_axiom (forall_ v P)


/--
  is_deduct Δ P := True if and only if there is a deduction of P from Δ in classical first order logic.
-/
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


/--
  is_proof P := True if and only if there is a proof of P in classical first order logic.
-/
def is_proof (P : formula) : Prop := is_deduct ∅ P


/--
  is_proof_alt P := True if and only if there is a proof of P in classical first order logic.

  This definition is equivalent to is_proof.
-/
inductive is_proof_alt : formula → Prop

-- ⊢ ⊤
| prop_true_ :
  is_proof_alt true_

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
  (v : variable_) (P Q : formula) :
  is_proof_alt ((forall_ v (P.imp_ Q)).imp_ ((forall_ v P).imp_ (forall_ v Q)))

-- ⊢ (∀ v P) → P(t/v)  provided P admits t for v
| pred_2_
  (v t : variable_) (P P' : formula) :
  fast_admits v t P →
  fast_replace_free v t P = P' →
  is_proof_alt ((forall_ v P).imp_ P')

-- ⊢ P → (∀ v P)  provided v is not free in P
| pred_3_
  (v : variable_) (P : formula) :
  ¬ is_free_in v P →
  is_proof_alt (P.imp_ (forall_ v P))

-- ⊢ ∀ v (v = v)
| eq_1_
  (v : variable_) :
  is_proof_alt (forall_ v (eq_ v v))

/-
⊢ ∀ x_0 ... ∀ x_n ∀ y_0 ... y_n ((x_0 = y_0) ∧ ... ∧ (x_n = y_n) ∧ ⊤) →
    ((pred_ name [x_0 ... x_n] ↔ pred_ name [y_0 ... y_n]))
-/
| eq_2_pred_
  (name : pred_name_) (n : ℕ) (xs ys : fin n → variable_) :
  is_proof_alt (Forall_ (list.of_fn xs) (Forall_ (list.of_fn ys)
    ((And_ (list.of_fn (fun (i : fin n), eq_ (xs i) (ys i)))).imp_
      ((pred_ name (list.of_fn xs)).iff_ (pred_ name (list.of_fn ys))))))

/-
⊢ ∀ x_0 ∀ x_1 ∀ y_0 ∀ y_1 ((x_0 = y_0) ∧ (x_1 = y_1)) → ((eq_ x_0 x_1) ↔ (eq_ y_0 y_1))
-/
| eq_2_eq_
  (x_0 x_1 y_0 y_1 : variable_) :
  is_proof_alt (forall_ x_0 (forall_ x_1 (forall_ y_0 (forall_ y_1 ((and_ (eq_ x_0 y_0) (eq_ x_1 y_1)).imp_
    ((eq_ x_0 x_1).iff_ (eq_ y_0 y_1)))))))

-- ⊢ P ⇒ ⊢ ∀ v P
| gen_
  (v : variable_) (P : formula) :
  is_proof_alt P →
  is_proof_alt (forall_ v P)

-- ⊢ P → Q ⇒ ⊢ P ⇒ ⊢ Q
| mp_
  (P Q : formula) :
  is_proof_alt (P.imp_ Q) →
  is_proof_alt P →
  is_proof_alt Q


theorem T_14_10
  (Q : formula)
  (Δ : set formula)
  (h1 : is_deduct Δ Q) :
  ∀ (Γ : set formula), is_deduct (Δ ∪ Γ) Q :=
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
    simp only [set.mem_union_eq],
    left,
    exact h1_1,
  },
  case is_deduct.mp_ : h1_P h1_Q h1_1 h1_2 h1_ih_1 h1_ih_2
  {
    apply is_deduct.mp_ h1_P,
    {
      exact h1_ih_1,
    },
    {
      exact h1_ih_2,
    }
  },
end


theorem T_14_10_comm
  (Q : formula)
  (Δ : set formula)
  (h1 : is_deduct Δ Q) :
  ∀ (Γ : set formula), is_deduct (Γ ∪ Δ) Q :=
begin
  simp only [set.union_comm],
  exact T_14_10 Q Δ h1,
end


theorem C_14_11
  (P : formula)
  (h1 : is_proof P) :
  ∀ (Δ : set formula), is_deduct Δ P :=
begin
  intros Δ,
  obtain s1 := T_14_10 P ∅ h1 Δ,
  simp only [set.empty_union] at s1,
  exact s1,
end

alias C_14_11 <- proof_imp_deduct


theorem T_14_16
  (Q : formula)
  (Δ Γ : set formula)
  (h1 : is_deduct Γ Q)
  (h2 : ∀ (P : formula), P ∈ Γ → is_deduct Δ P) :
  is_deduct Δ Q :=
begin
  induction h1,
  case is_deduct.axiom_ : h1_P h1_1
  {
    apply is_deduct.axiom_,
    exact h1_1,
  },
  case is_deduct.assume_ : h1_P h1_1
  {
    exact h2 h1_P h1_1,
  },
  case is_deduct.mp_ : h1_P h1_Q h1_1 h1_2 h1_ih_1 h1_ih_2
  {
    exact is_deduct.mp_ h1_P h1_Q h1_ih_1 h1_ih_2,
  },
end


theorem C_14_17
  (Q : formula)
  (Γ : set formula)
  (h1 : is_deduct Γ Q)
  (h2 : ∀ (P : formula), P ∈ Γ → is_proof P) :
  is_proof Q :=
begin
  unfold is_proof at h2,

  unfold is_proof,
  exact T_14_16 Q ∅ Γ h1 h2,
end


#lint
