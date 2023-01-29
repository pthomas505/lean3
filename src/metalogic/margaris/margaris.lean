import data.finset


@[derive decidable_eq]
inductive variable_ : Type
| variable_ : string → variable_

@[derive decidable_eq]
inductive pred_symbol_ : Type
| pred_symbol_ : string → pred_symbol_


@[derive decidable_eq]
inductive formula_ : Type
| pred_ : pred_symbol_ → list variable_ → formula_
| not_ : formula_ → formula_
| imp_ : formula_ → formula_ → formula_
| forall_ : variable_ → formula_ → formula_

open formula_


-- P ∨ Q := ~ P → Q
def or_ (P Q : formula_) : formula_ := imp_ (not_ P) Q

-- P ∧ Q := ~ ( P → ~ Q )
def and_ (P Q : formula_) : formula_ := not_ (imp_ P (not_ Q))

-- P ↔ Q := ( P → Q ) ∧ ( Q → P )
def iff_ (P Q : formula_) : formula_ := and_ (imp_ P Q) (imp_ Q P)

-- ∃ x P := ~ ∀ x ~ P
def exists_ (x : variable_) (P : formula_) : formula_ := not_ (forall_ x (not_ P))


/-
  pg. 20

  An occurrence of a variable v in a formula P is bound if and only if it is the explicit occurrence in a quantifier ∀ v or ∃ v, or if it is in the scope of a quantifier ∀ v or ∃ v. An occurrence of a variable is free if and only if it is not bound. A variable is bound or free in P according as it has a bound or free occurrence in P.
-/

/-
  pg. 38
  Let P be a formula, v a variable, and t a term. Then P(t/v) is the formula that results when each free occurrence of v in P is replaced by an occurrence of t. We say that P(t/v) is the result of substituting t for v in P.

  Let u and v be variables and P a formula. P admits u for v if and only if every free occurrence of v in P becomes a free occurrence of u in P(u/v).

  Let t be a term, v a variable, and P a formula. Then P admits t for v if and only if P admits u for v for every variable u that occurrs in t.
-/


/-
pg. 48

An occurrence of a variable $v$ in a formula $P$ is bound if and only if it occurs in a subformula of $P$ of the form $\forall v Q$. An occurrence of $v$ in $P$ is free if and only if it is not a bound occurrence. The variable $v$ is free or bound in $P$ according as it has a free or bound occurrence in $P$.

If $P$ is a formula, $v$ is a variable, and $t$ is a term, then $P(t/v)$ is the result of replacing each free occurrence of $v$ in $P$ by an occurrence of $t$.

If $v$ and $u$ are variables and $P$ is a formula, then $P$ admits $u$ for $v$ if and only if there is no free occurrence of $v$ in $P$ that becomes a bound occurrence of $u$ in $P(u/v)$. If $t$ is a term, then $P$ admits $t$ for $v$ if and only if $P$ admits for $v$ every variable in $t$.
-/

def formula_.free_var_set : formula_ → finset variable_
| (pred_ name args) := args.to_finset
| (not_ P) := P.free_var_set
| (imp_ P Q) := P.free_var_set ∪ Q.free_var_set
| (forall_ x P) := P.free_var_set \ {x}

def is_free_in (v : variable_) : formula_ → Prop
| (pred_ name args) := v ∈ args.to_finset
| (not_ P) := is_free_in P
| (imp_ P Q) := is_free_in P ∨ is_free_in Q
| (forall_ x P) := ¬ v = x ∧ is_free_in P


example
  (v : variable_)
  (P : formula_) :
  is_free_in v P ↔ v ∈ P.free_var_set :=
begin
  induction P,
  case formula_.pred_ : name args
  {
    refl,
  },
  case formula_.not_ : P P_ih
  {
    unfold is_free_in,
    unfold formula_.free_var_set,
    exact P_ih,
  },
  case formula_.imp_ : P Q P_ih Q_ih
  {
    unfold is_free_in,
    unfold formula_.free_var_set,
    simp only [finset.mem_union],
    exact iff.or P_ih Q_ih,
  },
  case formula_.forall_ : x P P_ih
  {
    cases P_ih,

    unfold is_free_in,
    unfold formula_.free_var_set,
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


-- v -> u
def replace
  {α : Type}
  [decidable_eq α]
  (v u x : α) : α :=
  if x = v then u else x

def replace_free (v u : variable_) : formula_ → formula_
| (pred_ name args) := pred_ name (args.map (replace v u))
| (not_ P) := not_ (replace_free P)
| (imp_ P Q) := imp_ (replace_free P) (replace_free Q)
| (forall_ x φ) :=
  if x = v
  then forall_ x φ
  else forall_ x (replace_free φ)




inductive is_axiom : formula_ → Prop

| prop_1 (P Q : formula_) :
  is_axiom (P.imp_ (Q.imp_ P))

| prop_2 (P Q S : formula_) :
  is_axiom ((S.imp_ (P.imp_ Q)).imp_ ((S.imp_ P).imp_ (S.imp_ Q)))

| prop_3 (P Q : formula_) :
  is_axiom (((not_ Q).imp_ (not_ P)).imp_ (P.imp_ Q))

| pred_1 (P Q : formula_) (v : variable_) :
  is_axiom ((forall_ v (P.imp_ Q)).imp_ ((forall_ v P).imp_ (forall_ v Q)))

| pred_2 (v : variable_) (P : formula_)
  (t : variable_) :
  P.admits t v → 
  is_axiom ((forall_ v P).imp_ P(t/v))

| pred_3 (P : formula_) (v : variable_) :
  v ∉ P.free_var_set →
  is_axiom (P.imp_ (forall_ v P))

| gen (P : formula_) (v : variable_) :
  is_axiom P →
  v ∈ P.free_var_set →
  is_axiom (forall_ v P)

| mp (P Q : formula_) :
  -- major premise
  is_axiom (P.imp_ Q) →
  -- minor premise
  is_axiom P →
  is_axiom Q

