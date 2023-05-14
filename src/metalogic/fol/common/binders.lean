import .formula

import data.finset


set_option pp.parens true


namespace fol

open formula


/-
[margaris]
pg. 48

An occurrence of a variable $v$ in a formula $P$ is bound if and only if it occurs in a subformula of $P$ of the form $\forall v Q$. An occurrence of $v$ in $P$ is free if and only if it is not a bound occurrence. The variable $v$ is free or bound in $P$ according as it has a free or bound occurrence in $P$.
-/


/--
  formula.var_set F := The set of all of the variables that have an occurrence in the formula F.
-/
def formula.var_set : formula → finset var_name
| true_ := ∅
| (pred_ _ xs) := xs.to_finset
| (not_ phi) := phi.var_set
| (imp_ phi psi) := phi.var_set ∪ psi.var_set
| (forall_ x phi) := phi.var_set ∪ {x}

/--
  occurs_in v F := True if and only if there is an occurrence of the variable v in the formula F.
-/
@[derive decidable]
def occurs_in (v : var_name) : formula → bool
| true_ := false
| (pred_ _ xs) := v ∈ xs.to_finset
| (not_ phi) := occurs_in phi
| (imp_ phi psi) := occurs_in phi ∨ occurs_in psi
| (forall_ x phi) := v = x ∨ occurs_in phi


/--
  formula.bound_var_set F := The set of all of the variables that have a bound occurrence in the formula F.
-/
def formula.bound_var_set : formula → finset var_name
| true_ := ∅
| (pred_ _ _) := ∅
| (not_ phi) := phi.bound_var_set
| (imp_ phi psi) := phi.bound_var_set ∪ psi.bound_var_set
| (forall_ x phi) := phi.bound_var_set ∪ {x}

/--
  is_bound_in v F := True if and only if there is a bound occurrence of the variable v in the formula F.
-/
@[derive decidable]
def is_bound_in (v : var_name) : formula → bool
| true_ := false
| (pred_ _ _) := false
| (not_ phi) := is_bound_in phi
| (imp_ phi psi) := is_bound_in phi ∨ is_bound_in psi
| (forall_ x phi) := v = x ∨ is_bound_in phi


/--
  formula.free_var_set F := The set of all of the variables that have a free occurrence in the formula F.
-/
def formula.free_var_set : formula → finset var_name
| true_ := ∅
| (pred_ _ xs) := xs.to_finset
| (not_ phi) := phi.free_var_set
| (imp_ phi psi) := phi.free_var_set ∪ psi.free_var_set
| (forall_ x phi) := phi.free_var_set \ {x}

/--
  is_free_in v F := True if and only if there is a free occurrence of the variable v in the formula F.
-/
@[derive decidable]
def is_free_in (v : var_name) : formula → bool
| true_ := false
| (pred_ _ xs) := v ∈ xs.to_finset
| (not_ phi) := is_free_in phi
| (imp_ phi psi) := is_free_in phi ∨ is_free_in psi
| (forall_ x phi) := ¬ v = x ∧ is_free_in phi

/--
  pred.occurs_in P n F := True if and only if there is an occurrence of the predicate named P of arity n in the formula F.
-/
@[derive decidable]
def pred.occurs_in (P : pred_name) (n : ℕ) : formula → bool
| true_ := ff
| (pred_ X xs) := X = P ∧ xs.length = n
| (not_ phi) := pred.occurs_in phi
| (imp_ phi psi) := pred.occurs_in phi ∨ pred.occurs_in psi
| (forall_ _ phi) := pred.occurs_in phi


lemma occurs_in_iff_mem_var_set
  (v : var_name)
  (F : formula) :
  occurs_in v F ↔ v ∈ F.var_set :=
begin
  induction F,
  case fol.formula.true_
  {
    unfold occurs_in,
    unfold formula.var_set,
    simp only [to_bool_false_eq_ff, coe_sort_ff, finset.not_mem_empty],
  },
  case fol.formula.pred_ : X xs
  {
    unfold occurs_in,
    unfold formula.var_set,
    simp only [bool.of_to_bool_iff],
  },
  case formula.not_ : phi phi_ih
  {
    assumption,
  },
  case formula.imp_ : phi psi phi_ih psi_ih
  {
    unfold occurs_in,
    unfold formula.var_set,
    simp only [finset.mem_union],
    simp only [bool.of_to_bool_iff],
    tauto,
  },
  case formula.forall_ : x phi phi_ih
  {
    unfold occurs_in,
    unfold formula.var_set,
    simp only [bool.of_to_bool_iff, finset.mem_union, finset.mem_singleton],
    tauto,
  },
end


lemma is_bound_in_iff_mem_bound_var_set
  (v : var_name)
  (F : formula) :
  is_bound_in v F ↔ v ∈ F.bound_var_set :=
begin
  induction F,
  case fol.formula.true_
  {
    unfold is_bound_in,
    unfold formula.bound_var_set,
    simp only [to_bool_false_eq_ff, coe_sort_ff, finset.not_mem_empty],
  },
  case fol.formula.pred_ : X xs
  {
    unfold is_bound_in,
    unfold formula.bound_var_set,
    simp only [to_bool_false_eq_ff, coe_sort_ff, finset.not_mem_empty],
  },
  case formula.not_ : phi phi_ih
  {
    assumption,
  },
  case formula.imp_ : phi psi phi_ih psi_ih
  {
    unfold is_bound_in,
    unfold formula.bound_var_set,
    simp only [bool.of_to_bool_iff, finset.mem_union],
    tauto,
  },
  case formula.forall_ : x phi phi_ih
  {
    unfold is_bound_in,
    unfold formula.bound_var_set,
    simp only [bool.of_to_bool_iff, finset.mem_union, finset.mem_singleton],
    tauto,
  },
end


lemma is_free_in_iff_mem_free_var_set
  (v : var_name)
  (F : formula) :
  is_free_in v F ↔ v ∈ F.free_var_set :=
begin
  induction F,
  case fol.formula.true_
  {
    unfold is_free_in,
    unfold formula.free_var_set,
    simp only [to_bool_false_eq_ff, coe_sort_ff, finset.not_mem_empty],
  },
  case fol.formula.pred_ : X xs
  {
    unfold is_free_in,
    unfold formula.free_var_set,
    simp only [bool.of_to_bool_iff],
  },
  case formula.not_ : phi phi_ih
  {
    assumption,
  },
  case formula.imp_ : phi psi phi_ih psi_ih
  {
    unfold is_free_in,
    unfold formula.free_var_set,
    simp only [bool.of_to_bool_iff, finset.mem_union],
    tauto,
  },
  case formula.forall_ : x phi phi_ih
  {
    unfold is_free_in,
    unfold formula.free_var_set,
    simp only [bool.of_to_bool_iff, finset.mem_sdiff, finset.mem_singleton],
    tauto,
  },
end


theorem is_bound_in_imp_occurs_in
  (v : var_name)
  (F : formula)
  (h1 : is_bound_in v F) :
  occurs_in v F :=
begin
  induction F,
  case fol.formula.true_
  {
    unfold is_bound_in at h1,
    simp only [to_bool_false_eq_ff, coe_sort_ff] at h1,

    contradiction,
  },
  case fol.formula.pred_ : X xs
  {
    unfold is_bound_in at h1,
    simp only [to_bool_false_eq_ff, coe_sort_ff] at h1,

    contradiction,
  },
  case fol.formula.not_ : phi phi_ih
  {
    unfold is_bound_in at h1,

    unfold occurs_in,
    exact phi_ih h1,
  },
  case fol.formula.imp_ : phi psi phi_ih psi_ih
  {
    unfold is_bound_in at h1,
    simp only [bool.of_to_bool_iff] at h1,

    unfold occurs_in,
    simp only [bool.of_to_bool_iff],
    cases h1,
    {
      left,
      exact phi_ih h1,
    },
    {
      right,
      exact psi_ih h1,
    }
  },
  case fol.formula.forall_ : x phi phi_ih
  {
    unfold is_bound_in at h1,
    simp only [bool.of_to_bool_iff] at h1,

    unfold occurs_in,
    simp only [bool.of_to_bool_iff],
    cases h1,
    {
      left,
      exact h1,
    },
    {
      right,
      exact phi_ih h1,
    }
  },
end


theorem is_free_in_imp_occurs_in
  (v : var_name)
  (F : formula)
  (h1 : is_free_in v F) :
  occurs_in v F :=
begin
  induction F,
  case fol.formula.true_
  {
    unfold is_free_in at h1,
    simp only [to_bool_false_eq_ff, coe_sort_ff] at h1,

    contradiction,
  },
  case fol.formula.pred_ : X xs
  {
    unfold is_free_in at h1,
    simp only [list.mem_to_finset, bool.of_to_bool_iff] at h1,

    unfold occurs_in,
    simp only [list.mem_to_finset, bool.of_to_bool_iff],
    exact h1,
  },
  case fol.formula.not_ : phi phi_ih
  {
    unfold is_free_in at h1,

    unfold occurs_in,
    exact phi_ih h1,
  },
  case fol.formula.imp_ : phi psi phi_ih psi_ih
  {
    unfold is_free_in at h1,
    simp only [bool.of_to_bool_iff] at h1,

    unfold occurs_in,
    simp only [bool.of_to_bool_iff],
    cases h1,
    {
      left,
      exact phi_ih h1,
    },
    {
      right,
      exact psi_ih h1,
    }
  },
  case fol.formula.forall_ : x phi phi_ih
  {
    unfold is_free_in at h1,
    simp only [bool.of_to_bool_iff] at h1,
    cases h1,

    unfold occurs_in,
    simp only [bool.of_to_bool_iff],
    right,
    exact phi_ih h1_right,
  },
end


#lint

end fol
