import tactic


set_option pp.parens true


/--
  The type of propositional variables.
-/
@[derive [inhabited, decidable_eq]]
inductive prop_var_ : Type
| mk : string → prop_var_


/--
  The string representation of propositional variables.
-/
def prop_var_.repr : prop_var_ → string
| (prop_var_.mk name) := name

instance prop_var_.has_repr : has_repr prop_var_ := has_repr.mk prop_var_.repr


/--
  The type of propositional formulas.
-/
@[derive [inhabited, decidable_eq]]
inductive formula : Type
| prop_ : prop_var_ → formula
| not_ : formula → formula
| imp_ : formula → formula → formula

open formula


@[derive inhabited]
def assignment : Type := prop_var_ → bool

def formula.eval (a : assignment) : formula → bool
| (prop_ P) := a P
| (not_ P) := ! P.eval
| (imp_ P Q) := (! P.eval) || Q.eval

def formula.holds (P : formula) (a : assignment) : Prop :=
  P.eval a = bool.tt

def formula.is_satisfiable (P : formula) : Prop :=
  ∃ (a : assignment), P.eval a = bool.tt

def set_is_satisfiable (S : set formula) : Prop :=
  ∃ (a : assignment), ∀ (P : formula), P ∈ S → P.holds a

def formula.is_valid (P : formula) : Prop :=
  ∀ (a : assignment), P.holds a


theorem compactness_right
  (S : set formula)
  (h1 : set_is_satisfiable S) :
  ∀ (T : set formula), T.finite → T ⊆ S → set_is_satisfiable T :=
begin
  unfold set_is_satisfiable at h1,
  apply exists.elim h1,
  intros a h1_1,
  intros T a1 a2,
  unfold set_is_satisfiable,
  apply exists.intro a,
  intros P a3,
  apply h1_1 P,
  tauto,
end


theorem compactness_left
  (S : set formula)
  (h1 : ∀ (T : set formula), T.finite → T ⊆ S → set_is_satisfiable T) :
  set_is_satisfiable S :=
begin
  sorry,
end
