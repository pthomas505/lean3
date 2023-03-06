import tactic


set_option pp.parens true


/--
  The type of FOL variables.
-/
@[derive [inhabited, decidable_eq]]
inductive variable_ : Type
| variable_ : string → variable_


/--
  The string representation of FOL variables.
-/
def variable_.repr : variable_ → string
| (variable_.variable_ name) := name

instance variable_.has_repr : has_repr variable_ := has_repr.mk variable_.repr


/--
  The type of FOL predicate names.
-/
@[derive [inhabited, decidable_eq]]
inductive pred_name_ : Type
| pred_name_ : string → pred_name_


/--
  The string representation of FOL predicate names.
-/
def pred_name_.repr : pred_name_ → string
| (pred_name_.pred_name_ name) := name

instance pred_name_.has_repr : has_repr pred_name_ := has_repr.mk pred_name_.repr


/--
  The type of FOL formulas.
-/
@[derive [inhabited, decidable_eq]]
inductive formula : Type
| true_ : formula
| pred_ : pred_name_ → list variable_ → formula
| eq_ : variable_ → variable_ → formula
| not_ : formula → formula
| imp_ : formula → formula → formula
| forall_ : variable_ → formula → formula

open formula


/--
  ⊥ := ¬ ⊤
-/
def formula.false_ : formula := not_ true_

/--
  P ∨ Q := ~ P → Q
-/
def formula.or_ (P Q : formula) : formula := (not_ P).imp_ Q

/--
P ∧ Q := ~ ( P → ~ Q )
-/
def formula.and_ (P Q : formula) : formula := not_ (P.imp_ (not_ Q))

/--
  P ↔ Q := ( P → Q ) ∧ ( Q → P )
-/
def formula.iff_ (P Q : formula) : formula := (P.imp_ Q).and_ (Q.imp_ P)

/--
  ∃ x P := ~ ∀ x ~ P
-/
def formula.exists_ (x : variable_) (P : formula) : formula := not_ (forall_ x (not_ P))


/--
  And [] = ⊤

  And [P] = P ∧ ⊤

  And [P_1 ... P_n] := P_1 ∧ ... ∧ P_n ∧ ⊤ 
-/
def formula.And (l : list formula) : formula := list.foldr formula.and_ true_ l


/--
  Forall [x0 ... xn] P := ∀ x0 ... ∀ xn P
-/
def formula.Forall_ : list variable_ → formula → formula
| [] P := P
| (x :: xs) P := forall_ x (formula.Forall_ xs P)


def formula.repr : formula → string
| true_ := "⊤"
| (pred_ name args) := sformat!"({name.repr} {args.repr})"
| (eq_ x y) := sformat!"({x.repr} = {y.repr})"
| (not_ P) := sformat!"(¬ {P.repr})"
| (imp_ P Q) := sformat!"({P.repr} → {Q.repr})"
| (forall_ x P) := sformat!"(∀ {x.repr}. {P.repr})"

instance formula.has_repr : has_repr formula := has_repr.mk formula.repr


#lint
