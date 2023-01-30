/-
Reference:
First Order Mathematical Logic (Dover Books on Mathematics)
by Angelo Margaris
-/


import data.finset


@[derive decidable_eq]
inductive variable_ : Type
| variable_ : string → variable_

@[derive decidable_eq]
inductive pred_symbol_ : Type
| pred_symbol_ : string → pred_symbol_


@[derive decidable_eq]
inductive formula : Type
| pred_ : pred_symbol_ → list variable_ → formula
| not_ : formula → formula
| imp_ : formula → formula → formula
| forall_ : variable_ → formula → formula

open formula


-- P ∨ Q := ~ P → Q
def formula.or_ (P Q : formula) : formula := (not_ P).imp_ Q

-- P ∧ Q := ~ ( P → ~ Q )
def formula.and_ (P Q : formula) : formula := not_ (P.imp_ (not_ Q))

-- P ↔ Q := ( P → Q ) ∧ ( Q → P )
def formula.iff_ (P Q : formula) : formula := (P.imp_ Q).and_ (Q.imp_ P)

-- ∃ x P := ~ ∀ x ~ P
def formula.exists_ (x : variable_) (P : formula) : formula := not_ (forall_ x (not_ P))


/-
pg. 48

An occurrence of a variable $v$ in a formula $P$ is bound if and only if it occurs in a subformula of $P$ of the form $\forall v Q$. An occurrence of $v$ in $P$ is free if and only if it is not a bound occurrence. The variable $v$ is free or bound in $P$ according as it has a free or bound occurrence in $P$.
-/

def formula.free_var_set : formula → finset variable_
| (pred_ name args) := args.to_finset
| (not_ P) := P.free_var_set
| (imp_ P Q) := P.free_var_set ∪ Q.free_var_set
| (forall_ x P) := P.free_var_set \ {x}

def is_free_in (v : variable_) : formula → Prop
| (pred_ name args) := v ∈ args.to_finset
| (not_ P) := is_free_in P
| (imp_ P Q) := is_free_in P ∨ is_free_in Q
| (forall_ x P) := ¬ v = x ∧ is_free_in P


example
  (v : variable_)
  (P : formula) :
  is_free_in v P ↔ v ∈ P.free_var_set :=
begin
  induction P,
  case formula.pred_ : name args
  {
    refl,
  },
  case formula.not_ : P P_ih
  {
    unfold is_free_in,
    unfold formula.free_var_set,
    exact P_ih,
  },
  case formula.imp_ : P Q P_ih Q_ih
  {
    unfold is_free_in,
    unfold formula.free_var_set,
    simp only [finset.mem_union],
    exact iff.or P_ih Q_ih,
  },
  case formula.forall_ : x P P_ih
  {
    cases P_ih,

    unfold is_free_in,
    unfold formula.free_var_set,
    simp only [finset.mem_sdiff, finset.mem_singleton],
    split,
    {
      intros a1,
      cases a1,
      split,
      {
        exact P_ih_mp a1_right,
      },
      {
        exact a1_left,
      }
    },
    {
      intros a1,
      cases a1,
      split,
      {
        exact a1_right,
      },
      {
        exact P_ih_mpr a1_left,
      }
    }
  },
end


/-
pg. 48

If $P$ is a formula, $v$ is a variable, and $t$ is a term, then $P(t/v)$ is the result of replacing each free occurrence of $v$ in $P$ by an occurrence of $t$.
-/

-- v -> t
def replace
  {α : Type}
  [decidable_eq α]
  (v t x : α) : α :=
  if x = v then t else x

-- P (t/v)
-- v -> t in P
def replace_free (v t : variable_) : formula → formula
| (pred_ name args) := pred_ name (args.map (replace v t))
| (not_ P) := not_ (replace_free P)
| (imp_ P Q) := imp_ (replace_free P) (replace_free Q)
| (forall_ x P) :=
  if x = v
  then forall_ x P
  else forall_ x (replace_free P)


/-
pg. 48

If $v$ and $u$ are variables and $P$ is a formula, then $P$ admits $u$ for $v$ if and only if there is no free occurrence of $v$ in $P$ that becomes a bound occurrence of $u$ in $P(u/v)$. If $t$ is a term, then $P$ admits $t$ for $v$ if and only if $P$ admits for $v$ every variable in $t$.
-/

-- P admits u for v
-- v → u in P

def admits_aux (v u : variable_) : finset variable_ → formula → Prop
| binders (pred_ name args) :=
    v ∉ args ∨
    v ∈ binders ∨
    u ∉ binders
| binders (not_ P) := admits_aux binders P
| binders (imp_ P Q) := admits_aux binders P ∧ admits_aux binders Q
| binders (forall_ x P) := admits_aux (binders ∪ {x}) P

def admits (v u : variable_) (P : formula) : Prop :=
  admits_aux v u ∅ P


def admits' (v u : variable_) : formula → Prop
| (pred_ name args) := true
| (not_ P) := admits' P
| (imp_ P Q) := admits' P ∧ admits' Q
| (forall_ x P) := v ∈ (P.free_var_set \ {x}) → ¬ x = u


inductive is_prop_sub : formula → variable_ → variable_ → formula → Prop
| pred_ (name : pred_symbol_) (args : list variable_)
  (v t : variable_) :
  is_prop_sub (pred_ name args) v t (pred_ name (args.map (replace v t)))

| not_ (P : formula)
  (v t : variable_)
  (P' : formula) :
  is_prop_sub P v t P' →
  is_prop_sub P.not_ v t P'.not_

| imp_ (P Q : formula)
  (v t : variable_)
  (P' Q' : formula) :
  is_prop_sub P v t P' →
  is_prop_sub Q v t Q' →
  is_prop_sub (P.imp_ Q) v t (P'.imp_ Q')

| not_free (x : variable_) (P : formula)
  (v t : variable_)
  (P' : formula) :
  v ∉ P.free_var_set →
  is_prop_sub P v t P

| forall_free (x : variable_) (P : formula)
  (v t : variable_)
  (P' : formula) :
  ¬ x = v → ¬ x = t →
  is_prop_sub P v t P' →
  is_prop_sub (forall_ x P) v t (forall_ x P')


example
  (P : formula)
  (v u : variable_) :
  admits v u P ↔ admits' v u P :=
begin
  induction P,
  case formula.pred_ : name args
  {
    unfold admits,
    unfold admits_aux,
    simp only [finset.not_mem_empty, not_false_iff, or_true, true_iff],
  },
  case formula.not_ : P_ᾰ P_ih
  { admit },
  case formula.imp_ : P_ᾰ P_ᾰ_1 P_ih_ᾰ P_ih_ᾰ_1
  { admit },
  case formula.forall_ : x P P_ih
  {
    unfold admits at P_ih,
    cases P_ih,
    unfold admits,
    unfold admits_aux,
    simp only [finset.empty_union],
    unfold admits',
    split,
    {
      intros a1,
      sorry,
    },
    {
      intros a1,
      cases a1,
    }
  },
end


example
  (P : formula)
  (v t : variable_)
  (P' : formula)
  (h1 : admits v t P)
  (h2 : P' = replace_free v t P) :
  is_prop_sub P v t P' :=
begin
  subst h2,
  induction P,
end


example
  (P : formula)
  (v t : variable_)
  (P' : formula)
  (h1 : is_prop_sub P v t P') :
  admits v t P ∧ P' = replace_free v t P :=
begin
  induction h1,
end


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
