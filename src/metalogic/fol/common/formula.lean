import tactic


set_option pp.parens true


namespace fol


/--
  The type of variables.
-/
@[derive [inhabited, decidable_eq]]
inductive var_name : Type
| mk : string → var_name


/--
  The string representation of variables.
-/
def var_name.repr : var_name → string
| (var_name.mk name) := name

instance var_name.has_repr : has_repr var_name := has_repr.mk var_name.repr


/--
  The type of predicate names.
-/
@[derive [inhabited, decidable_eq]]
inductive pred_name : Type
| mk : string → pred_name


/--
  The string representation of predicate names.
-/
def pred_name.repr : pred_name → string
| (pred_name.mk name) := name

instance pred_name.has_repr : has_repr pred_name := has_repr.mk pred_name.repr


/--
  The type of formulas.
-/
@[derive [inhabited, decidable_eq]]
inductive formula : Type
| true_ : formula
| pred_ : pred_name → list var_name → formula
| not_ : formula → formula
| imp_ : formula → formula → formula
| forall_ : var_name → formula → formula

open formula


/--
  ⊥ := ¬ ⊤
-/
def formula.false_ : formula :=
  not_ true_

/--
  P ∨ Q := ~ P → Q
-/
def formula.or_ (P Q : formula) : formula :=
  (not_ P).imp_ Q

/--
P ∧ Q := ~ ( P → ~ Q )
-/
def formula.and_ (P Q : formula) : formula :=
  not_ (P.imp_ (not_ Q))

/--
  P ↔ Q := ( P → Q ) ∧ ( Q → P )
-/
def formula.iff_ (P Q : formula) : formula :=
  (P.imp_ Q).and_ (Q.imp_ P)

/--
  ∃ x P := ~ ∀ x ~ P
-/
def formula.exists_ (x : var_name) (P : formula) : formula :=
  not_ (forall_ x (not_ P))


/--
  eq_ x y := x = y
-/
def formula.eq_ (x y : var_name) : formula :=
  pred_ (pred_name.mk "=") [x, y]


/--
  mem_ x y := x ∈ y
-/
def formula.mem_ (x y : var_name) : formula :=
  pred_ (pred_name.mk "∈") [x, y]


/--
  Imp_ [] := ⊤

  Imp_ [P] := P → ⊤

  Imp_ [P_0 ... P_n] := P_0 → ... → P_n → ⊤
-/
def formula.Imp_ (l : list formula) : formula :=
  list.foldr formula.imp_ true_ l


/--
  And_ [] := ⊤

  And_ [P] := P ∧ ⊤

  And_ [P_0 ... P_n] := P_0 ∧ ... ∧ P_n ∧ ⊤
-/
def formula.And_ (l : list formula) : formula :=
  list.foldr formula.and_ true_ l


/--
  Or_ [] := ⊥

  Or_ [P] := P ∨ ⊥

  Or_ [P_0 ... P_n] := P_0 ∧ ... ∧ P_n ∧ ⊥
-/
def formula.Or_ (l : list formula) : formula :=
  list.foldr formula.or_ formula.false_ l


/--
  Forall_ [x_0 ... x_n] P := ∀ x_0 ... ∀ x_n P
-/
def formula.Forall_ (xs : list var_name) (P : formula) : formula :=
  list.foldr formula.forall_ P xs


/--
  Exists_ [x_0 ... x_n] P := ∃ x_0 ... ∃ x_n P
-/
def formula.Exists_ (xs : list var_name) (P : formula) : formula :=
  list.foldr formula.exists_ P xs


/--
  The string representation of formulas.
-/
def formula.repr : formula → string
| true_ := "⊤"
| (pred_ X xs) := sformat!"({X.repr} {xs.repr})"
| (not_ phi) := sformat!"(¬ {phi.repr})"
| (imp_ phi psi) := sformat!"({phi.repr} → {psi.repr})"
| (forall_ x phi) := sformat!"(∀ {x.repr}. {phi.repr})"

instance formula.has_repr : has_repr formula :=
  has_repr.mk formula.repr


#eval formula.And_ [pred_ (pred_name.mk "P") [], pred_ (pred_name.mk "Q") []]

#eval formula.Forall_ [(var_name.mk "x"), (var_name.mk "y")] (formula.pred_ (pred_name.mk "P") [])


#lint

end fol
