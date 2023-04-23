import metalogic.fol.common.binders


set_option pp.parens true


open formula


/--
  is_proof P := True if and only if there is a proof of P in classical first order logic.
-/
inductive is_proof : formula → Prop

-- ⊢ ⊤
| tru_ :
  is_proof true_

-- ⊢ P → (Q → P)
| ax_1_
  (P Q : formula) :
  is_proof (P.imp_ (Q.imp_ P))

-- ⊢ (P → (Q → R)) → ((P → Q) → (P → R))
| ax_2_
  (P Q R : formula) :
  is_proof ((P.imp_ (Q.imp_ R)).imp_ ((P.imp_ Q).imp_ (P.imp_ R)))

-- ⊢ (¬ P → ¬ Q) → (Q → P)
| ax_3_
  (P Q : formula) :
  is_proof (((not_ P).imp_ (not_ Q)).imp_ (Q.imp_ P))

-- ⊢ P ⇒ ⊢ P → Q ⇒ ⊢ Q
| ax_mp_
  (P Q : formula) :
  is_proof P →
  is_proof (P.imp_ Q) →
  is_proof Q

-- ⊢ P ⇒ ⊢ ∀ x P
| ax_gen_
  (x : variable_) (P : formula) :
  is_proof P →
  is_proof (forall_ x P)

-- ⊢ (∀ x (P → Q)) → ((∀ x P) → (∀ x Q))
| ax_4_
  (x : variable_) (P Q : formula) :
  is_proof ((forall_ x (P.imp_ Q)).imp_ ((forall_ x P).imp_ (forall_ x Q)))

-- ⊢ P → (∀ x P)  provided x does not occur in P
| ax_5_
  (x : variable_) (P : formula) :
  ¬ occurs_in x P →
  is_proof (P.imp_ (forall_ x P))

-- ⊢ ∃ x (x = y)
| ax_6_
  (x y : variable_) :
  is_proof (exists_ x (eq_ x y))

-- ⊢ (x = y) → ((x = z) → (y = z))
| ax_7_
  (x y z : variable_) :
  is_proof ((eq_ x y).imp_ ((eq_ x z).imp_ (eq_ y z)))


/-
⊢ (x_0 = y_0) → ... → (x_n = y_n) →
    pred_ name [x_0 ... x_n] → pred_ name [y_0 ... y_n]
-/
| ax_8_
  (name : pred_name_)
  (xs ys : list variable_) :
  xs.length = ys.length → 
  is_proof (
    list.foldr
      formula.imp_
      ((pred_ name xs).imp_ (pred_ name ys))
      (list.map₂ eq_ xs ys))


-- ⊢ (¬ (∀ x P)) → ∀ x ¬ (∀ x P)
| ax_10_
  (x : variable_) (P : formula) :
  is_proof ((not_ (forall_ x P)).imp_ (forall_ x (not_ (forall_ x P))))

-- ⊢ (∀ x ∀ y P) → (∀ y ∀ x P)
| ax_11_
  (x y : variable_) (P : formula) :
  is_proof ((forall_ x (forall_ y P)).imp_ (forall_ y (forall_ x P)))

-- ⊢ ∀ y (P → ∀ x (x = y → P))
| ax_12_
  (x y : variable_) (P : formula) :
  is_proof (forall_ y (P.imp_ (forall_ x ((eq_ x y).imp_ P))))

#lint
