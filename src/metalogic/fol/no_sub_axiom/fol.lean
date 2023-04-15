import .prop


set_option pp.parens true


open formula


def proof_equiv (P Q : formula) : Prop := is_proof (P.iff_ Q)


/--
is_repl_of_var_in_list u v l_u l_v := True if and only if l_v is the result of replacing one or more specified occurrences (but not necessarily all occurrences) of u in l_u by occurrences of v.
-/
def is_repl_of_var_in_list_fun (u v : variable_) : list variable_ → list variable_ → Prop
| [] [] := true
| (hd_u :: tl_u) (hd_v :: tl_v) := (hd_u = hd_v ∨ (hd_u = u ∧ hd_v = v)) ∧ is_repl_of_var_in_list_fun tl_u tl_v
| _ _ := false


/--
is_repl_of_var_in_formula_fun u v P_u P_v := True if and only if P_v is the result of replacing one or more specified occurrences (but not necessarily all occurrences) of u in P_u by occurrences of v.
-/
def is_repl_of_var_in_formula_fun (u v : variable_) : formula → formula → Prop
| true_ true_ := true
| (pred_ name_u args_u) (pred_ name_v args_v) := name_u = name_v ∧ is_repl_of_var_in_list_fun u v args_u args_v
| (eq_ x_u y_u) (eq_ x_v y_v) := (x_u = x_v ∨ (x_u = u ∧ x_v = v)) ∧ (y_u = y_v ∨ (y_u = u ∧ y_v = v))
| (not_ P_u) (not_ P_v) := is_repl_of_var_in_formula_fun P_u P_v
| (imp_ P_u Q_u) (imp_ P_v Q_v) := is_repl_of_var_in_formula_fun P_u P_v ∧ is_repl_of_var_in_formula_fun Q_u Q_v
| (forall_ x P_u) (forall_ x' P_v) := x = x' ∧ is_repl_of_var_in_formula_fun P_u P_v
| _ _ := false


/--
is_repl_of_var_in_formula u v P_u P_v := True if and only if P_v is the result of replacing one or more specified occurrences (but not necessarily all occurrences) of u in P_u by occurrences of v.
-/
inductive is_repl_of_var_in_formula (u v : variable_) : formula → formula → Prop
| true_ :
  is_repl_of_var_in_formula true_ true_

| pred_
  (name : pred_name_)
  (n : ℕ)
  (args_u args_v : fin n → variable_) :
  (∀ (i : fin n), (args_u i = args_v i) ∨ (args_u i = u ∧ args_v i = v)) →
  is_repl_of_var_in_formula (pred_ name (list.of_fn args_u)) (pred_ name (list.of_fn args_v))

| eq_
  (x_u y_u : variable_)
  (x_v y_v : variable_) :
  (x_u = x_v) ∨ (x_u = u ∧ x_v = v) →
  (y_u = y_v) ∨ (y_u = u ∧ y_v = v) →
  is_repl_of_var_in_formula (eq_ x_u y_u) (eq_ x_v y_v)

| not_
  (P_u P_v : formula) :
  is_repl_of_var_in_formula P_u P_v →
  is_repl_of_var_in_formula P_u.not_ P_v.not_

| imp_
  (P_u Q_u : formula)
  (P_v Q_v : formula) :
  is_repl_of_var_in_formula P_u P_v →
  is_repl_of_var_in_formula Q_u Q_v →
  is_repl_of_var_in_formula (P_u.imp_ Q_u) (P_v.imp_ Q_v)

| forall_
  (x : variable_)
  (P_u P_v : formula) :
  is_repl_of_var_in_formula P_u P_v →
  is_repl_of_var_in_formula (forall_ x P_u) (forall_ x P_v)


/--
is_repl_of_formula_in_formula_fun U V P_u P_v := True if and only if P_v is the result of replacing one or more specified occurrences (but not necessarily all occurrences) of U in P_u by occurrences of V.
-/
def is_repl_of_formula_in_formula_fun (U V : formula) : formula → formula → Prop
| (not_ P_u) (not_ P_v) := is_repl_of_formula_in_formula_fun P_u P_v
| (imp_ P_u Q_u) (imp_ P_v Q_v) := is_repl_of_formula_in_formula_fun P_u P_v ∧ is_repl_of_formula_in_formula_fun Q_u Q_v
| (forall_ x P_u) (forall_ x' P_v) := x = x' ∧ is_repl_of_formula_in_formula_fun P_u P_v
| P_u P_v := P_u = P_v ∨ (P_u = U ∧ P_v = V)


/--
is_repl_of_formula_in_formula U V P_u P_v := True if and only if P_v is the result of replacing one or more specified occurrences (but not necessarily all occurrences) of U in P_u by occurrences of V.
-/
inductive is_repl_of_formula_in_formula (U V : formula) : formula → formula → Prop
-- not replacing an occurrence
| same_
  (P_u P_v : formula) :
  P_u = P_v →
  is_repl_of_formula_in_formula P_u P_v

-- replacing an occurrence
| diff_
  (P_u P_v : formula) :
  P_u = U →
  P_v = V →
  is_repl_of_formula_in_formula P_u P_v

| not_
  (P_u P_v : formula) :
  is_repl_of_formula_in_formula P_u P_v →
  is_repl_of_formula_in_formula P_u.not_ P_v.not_

| imp_
  (P_u Q_u : formula)
  (P_v Q_v : formula) :
  is_repl_of_formula_in_formula P_u P_v →
  is_repl_of_formula_in_formula Q_u Q_v →
  is_repl_of_formula_in_formula (P_u.imp_ Q_u) (P_v.imp_ Q_v)

| forall_
  (x : variable_)
  (P_u P_v : formula) :
  is_repl_of_formula_in_formula P_u P_v →
  is_repl_of_formula_in_formula (forall_ x P_u) (forall_ x P_v)


def similar (P_u P_v : formula) (u v : variable_) : Prop :=
  ¬ is_free_in v P_u ∧
  ¬ is_free_in u P_v ∧
  fast_admits u v P_u ∧
  fast_admits v u P_v ∧
  P_v = fast_replace_free u v P_u ∧
  P_u = fast_replace_free v u P_v


theorem T_17_7
  (Q : formula)
  (v : variable_)
  (Δ : set formula)
  (h1 : is_deduct Δ Q)
  (h2 : ∀ (H : formula), H ∈ Δ → ¬ is_free_in v H) :
  is_deduct Δ (forall_ v Q) :=
begin
  induction h1,
  case is_deduct.axiom_ : h1_P h1_1
  {
    apply is_deduct.axiom_,
    apply is_axiom.gen_,
    exact h1_1,
  },
  case is_deduct.assume_ : h1_P h1_1
  {
    apply is_deduct.mp_ h1_P,
    {
      apply is_deduct.axiom_,
      apply is_axiom.pred_2_,
      exact h2 h1_P h1_1,
    },
    {
      apply is_deduct.assume_,
      exact h1_1,
    },
  },
  case is_deduct.mp_ : h1_P h1_Q h1_1 h1_2 h1_ih_1 h1_ih_2
  {
    apply is_deduct.mp_ (forall_ v h1_P),
    {
      apply is_deduct.mp_ (forall_ v (h1_P.imp_ h1_Q)),
      {
        apply is_deduct.axiom_,
        apply is_axiom.pred_1_,
      },
      {
        exact h1_ih_1,
      }
    },
    {
      exact h1_ih_2,
    }
  },
end

alias T_17_7 <- generalization


example
  (v t : variable_)
  (P : formula)
  (h1 : fast_admits v t P) :
  is_proof ((forall_ v P).imp_ (fast_replace_free v t P)) :=
begin
  sorry,
end


#lint
