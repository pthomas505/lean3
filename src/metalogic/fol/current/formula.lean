import tactic

set_option pp.parens true


@[derive [inhabited, decidable_eq]]
inductive variable_ : Type
| variable_ : string → variable_


@[derive [inhabited, decidable_eq]]
inductive pred_name_ : Type
| pred_name_ : string → pred_name_


@[derive [inhabited, decidable_eq]]
inductive formula : Type
| pred_ : pred_name_ → list variable_ → formula
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


def formula.is_prime : formula → Prop
| (pred_ name args) := true
| (not_ P) := false
| (imp_ P Q) := false
| (forall_ x P) := true

def formula.prime_constituent_set : formula → finset formula
| (pred_ name args) := {pred_ name args}
| (not_ P) := P.prime_constituent_set
| (imp_ P Q) := P.prime_constituent_set ∪ Q.prime_constituent_set
| (forall_ x P) := {forall_ x P}


def bool.bimp : bool → bool → bool
| bool.tt bool.tt := bool.tt
| bool.tt bool.ff := bool.ff
| bool.ff bool.tt := bool.tt
| bool.ff bool.ff := bool.tt

def formula.truth_value (valuation : formula → bool) : formula → bool
| (pred_ name args) := valuation (pred_ name args)
| (not_ P) := bnot P.truth_value
| (imp_ P Q) := bool.bimp P.truth_value Q.truth_value
| (forall_ x P) := valuation (forall_ x P)

def formula.is_tautology (P : formula) : Prop :=
  ∀ (valuation : formula → bool), P.truth_value valuation = bool.tt


lemma L_15_3_a
  (P Q : formula) :
  formula.is_tautology (P.imp_ (Q.imp_ P)) :=
begin
  sorry,
end
