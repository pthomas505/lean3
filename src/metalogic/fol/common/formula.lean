import tactic


set_option pp.parens true


namespace fol


/--
  The type of variable names.
-/
@[derive [inhabited, decidable_eq]]
inductive var_name : Type
| mk : string → var_name


/--
  The string representation of variable names.
-/
def var_name.repr : var_name → string
| (var_name.mk name) := name

instance var_name.has_repr : has_repr var_name := has_repr.mk var_name.repr


/--
  The type of predicate names.
-/
@[derive [inhabited, decidable_eq]]
inductive pred_name : Type
| const : string → pred_name
| var : string → pred_name

/--
  The string representation of predicate names.
-/
def pred_name.repr : pred_name → string
| (pred_name.const name) := name
| (pred_name.var name) := name

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


/--
  ⊥ := ¬ ⊤
-/
def formula.false_ : formula :=
  not_ true_

/--
  phi ∨ psi := ¬ phi → psi
-/
def formula.or_ (phi psi : formula) : formula :=
  (not_ phi).imp_ psi

/--
phi ∧ psi := ¬ ( phi → ¬ psi )
-/
def formula.and_ (phi psi : formula) : formula :=
  not_ (phi.imp_ (not_ psi))

/--
  phi ↔ psi := ( phi → psi ) ∧ ( psi → phi )
-/
def formula.iff_ (phi psi : formula) : formula :=
  (phi.imp_ psi).and_ (psi.imp_ phi)

/--
  ∃ x phi := ¬ ∀ x ¬ phi
-/
def formula.exists_ (x : var_name) (phi : formula) : formula :=
  not_ (forall_ x (not_ phi))


/--
  eq_ x y := x = y
-/
def formula.eq_ (x y : var_name) : formula :=
  pred_ (pred_name.const "=") [x, y]


/--
  mem_ x y := x ∈ y
-/
def formula.mem_ (x y : var_name) : formula :=
  pred_ (pred_name.const "∈") [x, y]


/--
  Imp_ [] := ⊤

  Imp_ [phi] := phi → ⊤

  Imp_ [phi_0 ... phi_n] := phi_0 → ... → phi_n → ⊤
-/
def formula.Imp_ (l : list formula) : formula :=
  list.foldr formula.imp_ true_ l


/--
  And_ [] := ⊤

  And_ [phi] := phi ∧ ⊤

  And_ [phi_0 ... phi_n] := phi_0 ∧ ... ∧ phi_n ∧ ⊤
-/
def formula.And_ (l : list formula) : formula :=
  list.foldr formula.and_ true_ l


/--
  Or_ [] := ⊥

  Or_ [phi] := phi ∨ ⊥

  Or_ [phi_0 ... phi_n] := phi_0 ∧ ... ∧ phi_n ∧ ⊥
-/
def formula.Or_ (l : list formula) : formula :=
  list.foldr formula.or_ formula.false_ l


/--
  Forall_ [x_0 ... x_n] phi := ∀ x_0 ... ∀ x_n phi
-/
def formula.Forall_ (xs : list var_name) (phi : formula) : formula :=
  list.foldr formula.forall_ phi xs


/--
  Exists_ [x_0 ... x_n] phi := ∃ x_0 ... ∃ x_n phi
-/
def formula.Exists_ (xs : list var_name) (phi : formula) : formula :=
  list.foldr formula.exists_ phi xs


#eval formula.And_ [pred_ (pred_name.var "X") [], pred_ (pred_name.var "Y") []]

#eval formula.Forall_ [(var_name.mk "x"), (var_name.mk "y")] (formula.pred_ (pred_name.var "phi") [])


#lint

end fol
