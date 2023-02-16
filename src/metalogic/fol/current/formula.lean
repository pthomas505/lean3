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
