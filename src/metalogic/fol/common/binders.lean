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
  formula.var_set P := The set of all of the variables that have an occurrence in the formula P.
-/
def formula.var_set : formula → finset var_name
| true_ := ∅
| (pred_ _ xs) := xs.to_finset
| (not_ P) := P.var_set
| (imp_ P Q) := P.var_set ∪ Q.var_set
| (forall_ x P) := P.var_set ∪ {x}

/--
  occurs_in v P := True if and only if there is an occurrence of the variable v in the formula P.
-/
@[derive decidable]
def occurs_in (v : var_name) : formula → bool
| true_ := false
| (pred_ _ xs) := v ∈ xs.to_finset
| (not_ P) := occurs_in P
| (imp_ P Q) := occurs_in P ∨ occurs_in Q
| (forall_ x P) := v = x ∨ occurs_in P


/--
  formula.bound_var_set P := The set of all of the variables that have a bound occurrence in the formula P.
-/
def formula.bound_var_set : formula → finset var_name
| true_ := ∅
| (pred_ _ _) := ∅
| (not_ P) := P.bound_var_set
| (imp_ P Q) := P.bound_var_set ∪ Q.bound_var_set
| (forall_ x P) := P.bound_var_set ∪ {x}

/--
  is_bound_in v P := True if and only if there is a bound occurrence of the variable v in the formula P.
-/
@[derive decidable]
def is_bound_in (v : var_name) : formula → bool
| true_ := false
| (pred_ _ _) := false
| (not_ P) := is_bound_in P
| (imp_ P Q) := is_bound_in P ∨ is_bound_in Q
| (forall_ x P) := v = x ∨ is_bound_in P


/--
  formula.free_var_set P := The set of all of the variables that have a free occurrence in the formula P.
-/
def formula.free_var_set : formula → finset var_name
| true_ := ∅
| (pred_ _ xs) := xs.to_finset
| (not_ P) := P.free_var_set
| (imp_ P Q) := P.free_var_set ∪ Q.free_var_set
| (forall_ x P) := P.free_var_set \ {x}

/--
  is_free_in v P := True if and only if there is a free occurrence of the variable v in the formula P.
-/
@[derive decidable]
def is_free_in (v : var_name) : formula → bool
| true_ := false
| (pred_ _ xs) := v ∈ xs.to_finset
| (not_ P) := is_free_in P
| (imp_ P Q) := is_free_in P ∨ is_free_in Q
| (forall_ x P) := ¬ v = x ∧ is_free_in P


@[derive decidable]
def pred.occurs_in (P : pred_name) (n : ℕ) : formula → bool
| true_ := ff
| (pred_ X xs) := X = P ∧ xs.length = n
| (not_ phi) := pred.occurs_in phi
| (imp_ phi psi) := pred.occurs_in phi ∨ pred.occurs_in psi
| (forall_ _ phi) := pred.occurs_in phi


lemma occurs_in_iff_mem_var_set
  (v : var_name)
  (P : formula) :
  occurs_in v P ↔ v ∈ P.var_set :=
begin
  induction P,
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
  case formula.not_ : P P_ih
  {
    assumption,
  },
  case formula.imp_ : P Q P_ih Q_ih
  {
    unfold occurs_in,
    unfold formula.var_set,
    simp only [finset.mem_union],
    simp only [bool.of_to_bool_iff],
    tauto,
  },
  case formula.forall_ : x P P_ih
  {
    unfold occurs_in,
    unfold formula.var_set,
    simp only [bool.of_to_bool_iff, finset.mem_union, finset.mem_singleton],
    tauto,
  },
end


lemma is_bound_in_iff_mem_bound_var_set
  (v : var_name)
  (P : formula) :
  is_bound_in v P ↔ v ∈ P.bound_var_set :=
begin
  induction P,
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
  case formula.not_ : P P_ih
  {
    assumption,
  },
  case formula.imp_ : P Q P_ih Q_ih
  {
    unfold is_bound_in,
    unfold formula.bound_var_set,
    simp only [bool.of_to_bool_iff, finset.mem_union],
    tauto,
  },
  case formula.forall_ : x P P_ih
  {
    unfold is_bound_in,
    unfold formula.bound_var_set,
    simp only [bool.of_to_bool_iff, finset.mem_union, finset.mem_singleton],
    tauto,
  },
end


lemma is_free_in_iff_mem_free_var_set
  (v : var_name)
  (P : formula) :
  is_free_in v P ↔ v ∈ P.free_var_set :=
begin
  induction P,
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
  case formula.not_ : P P_ih
  {
    assumption,
  },
  case formula.imp_ : P Q P_ih Q_ih
  {
    unfold is_free_in,
    unfold formula.free_var_set,
    simp only [bool.of_to_bool_iff, finset.mem_union],
    tauto,
  },
  case formula.forall_ : x P P_ih
  {
    unfold is_free_in,
    unfold formula.free_var_set,
    simp only [bool.of_to_bool_iff, finset.mem_sdiff, finset.mem_singleton],
    tauto,
  },
end


theorem is_bound_in_imp_occurs_in
  (P : formula)
  (v : var_name)
  (h1 : is_bound_in v P) :
  occurs_in v P :=
begin
  induction P,
  case fol.formula.true_
  {
    unfold is_bound_in at h1,
    squeeze_simp at h1,

    contradiction,
  },
  case fol.formula.pred_ : X xs
  {
    unfold is_bound_in at h1,
    squeeze_simp at h1,

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
    squeeze_simp at h1,

    unfold occurs_in,
    squeeze_simp,
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
    squeeze_simp at h1,

    unfold occurs_in,
    squeeze_simp,
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
  (P : formula)
  (v : var_name)
  (h1 : is_free_in v P) :
  occurs_in v P :=
begin
  induction P,
  case fol.formula.true_
  {
    unfold is_free_in at h1,
    squeeze_simp at h1,

    contradiction,
  },
  case fol.formula.pred_ : X xs
  {
    unfold is_free_in at h1,
    squeeze_simp at h1,

    unfold occurs_in,
    squeeze_simp,
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
    squeeze_simp at h1,

    unfold occurs_in,
    squeeze_simp,
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
    squeeze_simp at h1,
    cases h1,

    unfold occurs_in,
    squeeze_simp,
    right,
    exact phi_ih h1_right,
  },
end


#lint

end fol
