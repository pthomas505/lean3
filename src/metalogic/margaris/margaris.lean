import data.finset


abbreviation var_name := string
abbreviation pred_name := string


@[derive decidable_eq]
inductive formula : Type
| pred_ : pred_name → list var_name → formula
| not_ : formula → formula
| imp_ : formula → formula → formula
| forall_ : var_name → formula → formula

open formula


-- P ∨ Q := ~ P → Q
def or_ (P Q : formula) : formula := imp_ (not_ P) Q

-- P ∧ Q := ~ ( P → ~ Q )
def and_ (P Q : formula) : formula := not_ (imp_ P (not_ Q))

-- P ↔ Q := ( P → Q ) ∧ ( Q → P )
def iff_ (P Q : formula) : formula := and_ (imp_ P Q) (imp_ Q P)

-- ∃ x P := ~ ∀ x ~ P
def exists_ (x : var_name) (P : formula) : formula := not_ (forall_ x (not_ P))


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

def formula.free_var_set : formula → finset var_name
| (pred_ name args) := args.to_finset
| (not_ φ) := φ.free_var_set
| (imp_ φ ψ) := φ.free_var_set ∪ ψ.free_var_set
| (forall_ x φ) := φ.free_var_set \ {x}

def is_free_in (v : var_name) : formula → Prop
| (pred_ name args) := v ∈ args.to_finset
| (not_ P) := is_free_in P
| (imp_ P Q) := is_free_in P ∨ is_free_in Q
| (forall_ x P) := ¬ v = x ∧ is_free_in P

example
  (v : var_name)
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


inductive is_axiom : formula → Prop

| prop_1 (P Q : formula) :
  is_axiom (P.imp_ (Q.imp_ P))

| prop_2 (P Q S : formula) :
  is_axiom ((S.imp_ (P.imp_ Q)).imp_ ((S.imp_ P).imp_ (S.imp_ Q)))

| prop_3 (P Q : formula) :
  is_axiom (((not_ Q).imp_ (not_ P)).imp_ (P.imp_ Q))

| pred_1 (P Q : formula) (v : var_name) :
  is_axiom ((forall_ v (P.imp_ Q)).imp_ ((forall_ v P).imp_ (forall_ v Q)))

| pred_2 (v : var_name) (P : formula)
  (t : var_name) :
  P.admits t v → 
  is_axiom ((forall_ v P).imp_ P(t/v))

| pred_3 (P : formula) (v : var_name) :
  v ∉ P.free_var_set →
  is_axiom (P.imp_ (forall_ v P))

| gen (P : formula) (v : var_name) :
  is_axiom P →
  v ∈ P.free_var_set →
  is_axiom (forall_ v P)

| mp (P Q : formula) :
  -- major premise
  is_axiom (P.imp_ Q) →
  -- minor premise
  is_axiom P →
  is_axiom Q

