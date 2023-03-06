import .admits


set_option pp.parens true


open formula


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


/--
  eq_subst_pred name n [x_0 ... x_n] [y_0 ... y_n] := ((x_0 = y_0) ∧ ... ∧ (x_n = y_n) ∧ ⊤) → (pred_ name [x_0 ... x_n] = pred_ name [y_0 ... y_n])
-/
def eq_subst_pred (name : pred_name_) (n : ℕ) (xs ys : fin n → variable_) : formula :=
(And (list.of_fn (fun (i : fin n), eq_ (xs i) (ys i)))).imp_
((pred_ name (list.of_fn xs)).imp_ (pred_ name (list.of_fn ys)))


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

-- ⊢ P ⇒ ⊢ ∀ v P
| gen_
  (v : variable_) (P : formula) :
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


lemma proof_imp_deduct
  (P : formula)
  (h1 : is_proof P) :
  ∀ (Δ : set formula), is_deduct Δ P :=
begin
  unfold is_proof at h1,

  intros Δ,
  induction h1,
  case is_deduct.axiom_ : h1_P h1_1
  {
    apply is_deduct.axiom_,
    exact h1_1,
  },
  case is_deduct.assume_ : h1_P h1_1
  {
    simp only [set.mem_empty_eq] at h1_1,
    contradiction,
  },
  case is_deduct.mp_ : h1_P h1_Q h1_1 h1_2 h1_ih_1 h1_ih_2
  {
    exact is_deduct.mp_ h1_P h1_Q h1_ih_1 h1_ih_2,
  },
end


#lint
