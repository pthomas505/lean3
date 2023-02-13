/-
Reference:
First Order Mathematical Logic (Dover Books on Mathematics)
by Angelo Margaris
-/


import metalogic.fol.margaris.binders

open formula


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

-- ⊢ P → Q ⇒ ⊢ P ⇒ ⊢ Q 
| mp_
  (P Q : formula) :
  -- major premise
  is_axiom (P.imp_ Q) →
  -- minor premise
  is_axiom P →
  is_axiom Q


inductive is_deduct (Δ : finset formula) : formula → Prop
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


def list.is_deduct (Δ : finset formula) (l : list formula) : Prop :=
  ∀ P ∈ l,
    is_axiom P ∨
    P ∈ Δ ∨
    ∃ (Q R : formula),
      Q ∈ l ∧ R ∈ l ∧
      l.index_of Q < l.index_of P ∧
      l.index_of R < l.index_of P ∧
      Q.imp_ P = R



inductive is_deduct' (Δ : finset formula) : formula → Prop
| base_
  (P : formula) :
  is_deduct' P

| mp_
  (P Q : formula) :
  is_deduct' (P.imp_ Q) →
  is_deduct' P →
  is_deduct' Q


def list.is_deduct' (Δ : finset formula) (l : list formula) : Prop :=
  ∀ P ∈ l,
    ∃ (Q R : formula),
      Q ∈ l ∧ R ∈ l ∧
      Q.imp_ P = R


example
  (Δ : finset formula)
  (H : formula)
  (h1 : is_deduct' Δ H) :
  ∃ (l : list formula), H ∈ l ∧ l.is_deduct' Δ :=
begin
  induction h1,
  case is_deduct'.base_ : h1
  { admit },
  case is_deduct'.mp_ : h1_P h1_Q h1_1 h1_2 h1_ih_1 h1_ih_2
  {
    apply exists.elim h1_ih_1,
    intros l1 a1,
    clear h1_ih_1,
    cases a1,

    unfold list.is_deduct' at a1_right,

    apply exists.elim h1_ih_2,
    intros l2 a2,
    clear h1_ih_2,
    cases a2,

    unfold list.is_deduct' at a2_right,

    apply exists.intro (l1 ++ l2 ++ [h1_Q]),
    split,
    {
      squeeze_simp,
    },
    {
      unfold list.is_deduct',
      intros S a3,
      squeeze_simp at a3,

      cases a3,
      {
        sorry,
      },
      {
        cases a3,
        {
          sorry,
        },
        {
          apply exists.intro h1_P,
          apply exists.intro (h1_P.imp_ h1_Q),
          squeeze_simp,
          split,
          {
            apply or.intro_right,
            apply or.intro_left,
            exact a2_left,
          },
          {
            split,
            {
              apply or.intro_left,
              exact a1_left,
            },
            {
              exact a3,
            }
          },
        }
      }
    }
  },
end


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
  case is_deduct.assume_ : h1_P h1_1
  {
    simp only [finset.not_mem_empty] at h1_1,
    contradiction,
  },
  case is_deduct.mp_ : h1_P h1_Q h1_1 h1_2 h1_ih_1 h1_ih_2
  {
    exact is_deduct.mp_ h1_P h1_Q h1_ih_1 h1_ih_2,
  },
end


lemma prop_id
  (P : formula) :
  is_proof (P.imp_ P) :=
begin
  unfold is_proof,

  apply is_deduct.mp_,
  {
    apply is_deduct.mp_,
    {
      apply is_deduct.axiom_,
      exact is_axiom.prop_2_ P (P.imp_ P) P,
    },
    {
      apply is_deduct.axiom_,
      exact is_axiom.prop_1_ P (P.imp_ P),
    }
  },
  {
    apply is_deduct.axiom_,
    exact is_axiom.prop_1_ P P,
  },
end


example
  (P Q : formula) :
  is_proof ((not_ P).imp_ (P.imp_ Q)) :=
begin
  unfold is_proof,

  apply is_deduct.mp_,
  {
    apply is_deduct.mp_,
    {
      apply is_deduct.axiom_,
      exact is_axiom.prop_2_ P.not_ (Q.not_.imp_ P.not_) (P.imp_ Q),
    },
    {
      apply is_deduct.mp_,
      {
        apply is_deduct.axiom_,
        exact is_axiom.prop_1_ ((Q.not_.imp_ P.not_).imp_ (P.imp_ Q)) P.not_,
      },
      {
        apply is_deduct.axiom_,
        exact is_axiom.prop_3_ Q P,
      }
    }
  },
  {
    apply is_deduct.axiom_,
    exact is_axiom.prop_1_ P.not_ Q.not_,
  },
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

    apply is_deduct.mp_,
    {
      apply is_deduct.axiom_,
      exact is_axiom.prop_1_ h1_P P,
    },
    {
      apply is_deduct.axiom_,
      exact h1_1,
    },
  },
  case is_deduct.assume_ : h1_P h1_1
  {
    simp only [finset.mem_union, finset.mem_singleton] at h1_1,
    cases h1_1,
    {
      -- Case 2

      apply is_deduct.mp_,
      {
        apply is_deduct.axiom_,
        exact is_axiom.prop_1_ h1_P P,
      },
      {
        apply is_deduct.assume_,
        exact h1_1,
      },
    },
    {
      -- Case 3

      rewrite h1_1,
      apply proof_imp_deduct,
      exact prop_id P,
    }
  },
  case is_deduct.mp_ : h1_P h1_Q h1_1 h1_2 h1_ih_1 h1_ih_2
  {
    -- Case 4

    apply is_deduct.mp_,
    {
      apply is_deduct.mp_,
      {
        apply is_deduct.axiom_,
        exact is_axiom.prop_2_ P h1_P h1_Q,
      },
      {
        exact h1_ih_1,
      }
    },
    {
      exact h1_ih_2,
    },
  },
end


example
  (P Q : formula) :
  is_proof ((not_ P).imp_ (P.imp_ Q)) :=
begin
  unfold is_proof,

  apply deduction_theorem,

  apply is_deduct.mp_,
  {
    apply is_deduct.axiom_,
    exact is_axiom.prop_3_ Q P,
  },
  {
    apply is_deduct.mp_,
    {
      apply is_deduct.axiom_,
      exact is_axiom.prop_1_ P.not_ Q.not_,
    },
    {
    apply is_deduct.assume_,
    simp only [finset.empty_union, finset.mem_singleton],
    },
  },
end
