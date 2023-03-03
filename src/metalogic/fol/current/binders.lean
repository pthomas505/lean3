import .formula

import data.finset


set_option pp.parens true


open formula


/-
[margaris]
pg. 48

An occurrence of a variable $v$ in a formula $P$ is bound if and only if it occurs in a subformula of $P$ of the form $\forall v Q$. An occurrence of $v$ in $P$ is free if and only if it is not a bound occurrence. The variable $v$ is free or bound in $P$ according as it has a free or bound occurrence in $P$.
-/


/--
  formula.var_set P := The set of all of the variables that have an occurrence in the formula P.
-/
def formula.var_set : formula → finset variable_
| (true_) := ∅
| (pred_ name args) := args.to_finset
| (eq_ x y) := {x, y}
| (not_ P) := P.var_set
| (imp_ P Q) := P.var_set ∪ Q.var_set
| (forall_ x P) := P.var_set ∪ {x}

/--
  occurs_in v P := True if and only if there is an occurrence of the variable v in the formula P.
-/
def occurs_in (v : variable_) : formula → Prop
| (true_) := false
| (pred_ name args) := v ∈ args.to_finset
| (eq_ x y) := v = x ∨ v = y
| (not_ P) := occurs_in P
| (imp_ P Q) := occurs_in P ∨ occurs_in Q
| (forall_ x P) := v = x ∨ occurs_in P


/--
  formula.bound_var_set P := The set of all of the variables that have a bound occurrence in the formula P.
-/
def formula.bound_var_set : formula → finset variable_
| (true_) := ∅
| (pred_ name args) := ∅
| (eq_ x y) := ∅
| (not_ P) := P.bound_var_set
| (imp_ P Q) := P.bound_var_set ∪ Q.bound_var_set
| (forall_ x P) := P.bound_var_set ∪ {x}

/--
  is_bound_in v P := True if and only if there is a bound occurrence of the variable v in the formula P.
-/
def is_bound_in (v : variable_) : formula → Prop
| (true_) := false
| (pred_ name args) := false
| (eq_ x y) := false
| (not_ P) := is_bound_in P
| (imp_ P Q) := is_bound_in P ∨ is_bound_in Q
| (forall_ x P) := v = x ∨ is_bound_in P


/--
  formula.free_var_set P := The set of all of the variables that have a free occurrence in the formula P.
-/
def formula.free_var_set : formula → finset variable_
| (true_) := ∅
| (pred_ name args) := args.to_finset
| (eq_ x y) := {x, y}
| (not_ P) := P.free_var_set
| (imp_ P Q) := P.free_var_set ∪ Q.free_var_set
| (forall_ x P) := P.free_var_set \ {x}

/--
  is_free_in v P := True if and only if there is a free occurrence of the variable v in the formula P.
-/
def is_free_in (v : variable_) : formula → Prop
| (true_) := false
| (pred_ name args) := v ∈ args.to_finset
| (eq_ x y) := v = x ∨ v = y
| (not_ P) := is_free_in P
| (imp_ P Q) := is_free_in P ∨ is_free_in Q
| (forall_ x P) := ¬ v = x ∧ is_free_in P


example
  (v : variable_)
  (P : formula) :
  occurs_in v P ↔ v ∈ P.var_set :=
begin
  induction P,
  case [formula.true_, formula.pred_ : name args]
  {
    all_goals {refl},
  },
  case formula.eq_ : x y
  {
    unfold occurs_in,
    unfold formula.var_set,
    simp only [finset.mem_insert, finset.mem_singleton],
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
    tauto,
  },
  case formula.forall_ : x P P_ih
  {
    unfold occurs_in,
    unfold formula.var_set,
    simp only [finset.mem_union, finset.mem_singleton],
    tauto,
  },
end


example
  (v : variable_)
  (P : formula) :
  is_bound_in v P ↔ v ∈ P.bound_var_set :=
begin
  induction P,
  case [formula.true_, formula.pred_ : name args, formula.eq_ : x y]
  {
    all_goals {refl},
  },
  case formula.not_ : P P_ih
  {
    assumption,
  },
  case formula.imp_ : P Q P_ih Q_ih
  {
    unfold is_bound_in,
    unfold formula.bound_var_set,
    simp only [finset.mem_union],
    tauto,
  },
  case formula.forall_ : x P P_ih
  {
    unfold is_bound_in,
    unfold formula.bound_var_set,
    simp only [finset.mem_union, finset.mem_singleton],
    tauto,
  },
end


example
  (v : variable_)
  (P : formula) :
  is_free_in v P ↔ v ∈ P.free_var_set :=
begin
  induction P,
  case [formula.true_, formula.pred_ : name args]
  {
    all_goals {refl},
  },
  case formula.eq_ : x y
  {
    unfold is_free_in,
    unfold formula.free_var_set,
    simp only [finset.mem_insert, finset.mem_singleton],
  },
  case formula.not_ : P P_ih
  {
    assumption,
  },
  case formula.imp_ : P Q P_ih Q_ih
  {
    unfold is_free_in,
    unfold formula.free_var_set,
    simp only [finset.mem_union],
    tauto,
  },
  case formula.forall_ : x P P_ih
  {
    unfold is_free_in,
    unfold formula.free_var_set,
    simp only [finset.mem_sdiff, finset.mem_singleton],
    tauto,
  },
end


theorem is_bound_in_imp_occurs_in
  (P : formula)
  (v : variable_)
  (h1 : is_bound_in v P) :
  occurs_in v P :=
begin
  induction P;
  unfold is_bound_in at h1;
  unfold occurs_in;
  tauto,
end


theorem is_free_in_imp_occurs_in
  (P : formula)
  (v : variable_)
  (h1 : is_free_in v P) :
  occurs_in v P :=
begin
  induction P;
  unfold is_free_in at h1;
  unfold occurs_in;
  tauto,
end


#lint
