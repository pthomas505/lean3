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


theorem T_21_1
  (x y : variable_) :
  is_proof ((eq_ x y).imp_ (eq_ y x)) :=
begin
  apply is_deduct.mp_ (eq_ y y),
  {
    apply is_deduct.mp_ (((eq_ y y).and_ (eq_ x y)).imp_ ((eq_ y x).iff_ (eq_ y y))),
    {
      unfold formula.iff_,
      unfold formula.and_,
      SC,
    },
    {
      apply is_deduct.axiom_,
      exact is_axiom.eq_2_eq_ y x y y,
    }
  },
  {
    apply is_deduct.axiom_,
    exact is_axiom.eq_1_ y,
  },
end


theorem T_21_2
  (x y z : variable_) :
  is_proof (((eq_ x y).and_ (eq_ y z)).imp_ (eq_ x z)) :=
begin
  apply is_deduct.mp_ (eq_ z z),
  {
    apply is_deduct.mp_ (((eq_ x y).and_ (eq_ z z)).imp_ ((eq_ x z).iff_ (eq_ y z))),
    {
      unfold formula.iff_,
      unfold formula.and_,
      SC,
    },
    {
      apply is_deduct.axiom_,
      exact is_axiom.eq_2_eq_ x z y z,
    },
  },
  {
    apply is_deduct.axiom_,
    exact is_axiom.eq_1_ z,
  },
end


theorem T_21_8
  (P_r P_s : formula)
  (r s : variable_)
  (h1 : is_repl_of_var_in_formula r s P_r P_s)
  (h2 : ¬ is_bound_in r P_r)
  (h3 : ¬ is_bound_in s P_r) :
  is_proof ((eq_ r s).imp_ (P_r.iff_ P_s)) :=
begin
  induction h1,
  case is_repl_of_var_in_formula.true_
  {
    unfold formula.iff_,
    unfold formula.and_,
    SC,
  },
  case is_repl_of_var_in_formula.pred_ : name n args_u args_v h1_1
  {
    apply is_deduct.mp_ ((eq_ r s).imp_ ((pred_ name (list.of_fn args_u)).iff_ (pred_ name (list.of_fn args_v)))),
    {
      SC,
    },
    {
      apply is_deduct.mp_ ((eq_ r s).imp_ (And_ (list.of_fn (λ (i : fin n), eq_ (args_u i) (args_v i))))),
      {
        apply is_deduct.mp_ (((And_ (list.of_fn (λ (i : fin n), eq_ (args_u i) (args_v i))))).imp_ (((pred_ name (list.of_fn args_u)).iff_ (pred_ name (list.of_fn args_v))))),
        {
          unfold formula.iff_,
          unfold formula.and_,
          SC,
        },
        {
          apply is_deduct.axiom_,
          exact is_axiom.eq_2_pred_ name n args_u args_v,
        },
      },
      {
        clear h2,
        clear h3,
        unfold And_,
        induction n,
        case nat.zero
        {
          simp only [list.of_fn_zero, list.foldr_nil],
          SC,
        },
        case nat.succ : n ih
        {
          simp only [list.of_fn_succ, list.foldr_cons],
          apply is_deduct.mp_ ((eq_ r s).imp_ (list.foldr and_ true_ (list.of_fn (λ (i : fin n), eq_ (args_u i.succ) (args_v i.succ))))),
          {
            apply is_deduct.mp_ ((eq_ r s).imp_ (eq_ (args_u 0) (args_v 0))),
            {
              unfold formula.and_,
              SC,
            },
            {
              specialize h1_1 0,
              cases h1_1,
              {
                apply is_deduct.mp_ (eq_ (args_u 0) (args_v 0)),
                {
                  SC,
                },
                {
                  simp only [h1_1],
                  apply is_deduct.axiom_,
                  apply is_axiom.eq_1_,
                },
              },
              {
                cases h1_1,
                subst h1_1_left,
                subst h1_1_right,

                SC,
              }
            }
          },
          {
            apply ih,
            intros i,
            apply h1_1,
          },
        },
      },
    },
  },
  case is_repl_of_var_in_formula.eq_ : x_u y_u x_v y_v h1_1 h1_2
  {
    apply is_deduct.mp_ (((eq_ x_u x_v).and_ (eq_ y_u y_v)).imp_ ((eq_ x_u y_u).iff_ (eq_ x_v y_v))),
    {
      apply is_deduct.mp_ ((eq_ r s).imp_ ((eq_ x_u x_v).and_ (eq_ y_u y_v))),
      {
        unfold formula.iff_,
        unfold formula.and_,
        SC,
      },
      {
        cases h1_1,
        {
          subst h1_1,
          cases h1_2,
          {
            subst h1_2,
            apply is_deduct.mp_ (eq_ x_u x_u),
            {
              apply is_deduct.mp_ (eq_ y_u y_u),
              {
                unfold formula.and_,
                SC,
              },
              {
                apply is_deduct.axiom_,
                exact is_axiom.eq_1_ y_u,
              }
            },
            {
              apply is_deduct.axiom_,
              exact is_axiom.eq_1_ x_u,
            }
          },
          {
            cases h1_2,
            subst h1_2_left,
            subst h1_2_right,
            apply is_deduct.mp_ (eq_ x_u x_u),
            {
              unfold formula.and_,
              SC,
            },
            {
              apply is_deduct.axiom_,
              exact is_axiom.eq_1_ x_u,
            }
          }
        },
        {
          cases h1_1,
          subst h1_1_left,
          subst h1_1_right,
          cases h1_2,
          {
            subst h1_2,
            apply is_deduct.mp_ (eq_ y_u y_u),
            {
              unfold formula.and_,
              SC,
            },
            {
              apply is_deduct.axiom_,
              exact is_axiom.eq_1_ y_u,
            }
          },
          {
            cases h1_2,
            subst h1_2_left,
            subst h1_2_right,

            unfold formula.and_,
            SC,
          }
        },
      }
    },
    {
      apply is_deduct.axiom_,
      exact is_axiom.eq_2_eq_ x_u y_u x_v y_v,
    }
  },
  case is_repl_of_var_in_formula.not_ : P_u P_v h1_1 h1_ih
  {
    unfold is_bound_in at h2,

    unfold is_bound_in at h3,

    specialize h1_ih h2 h3,
    apply is_deduct.mp_ ((eq_ r s).imp_ (P_u.iff_ P_v)),
    {
      unfold formula.iff_,
      unfold formula.and_,
      SC,
    },
    {
      exact h1_ih,
    }
  },
  case is_repl_of_var_in_formula.imp_ : P_u Q_u P_v Q_v h1_1 h1_2 h1_ih_1 h1_ih_2
  {
    unfold is_bound_in at h2,
    push_neg at h2,
    cases h2,

    unfold is_bound_in at h3,
    push_neg at h3,
    cases h3,

    specialize h1_ih_1 h2_left h3_left,
    specialize h1_ih_2 h2_right h3_right,
    apply is_deduct.mp_ ((eq_ r s).imp_ (Q_u.iff_ Q_v)),
    {
      apply is_deduct.mp_ ((eq_ r s).imp_ (P_u.iff_ P_v)),
      {
        unfold formula.iff_,
        unfold formula.and_,
        SC,
      },
      {
        exact h1_ih_1,
      }
    },
    {
      exact h1_ih_2,
    }
  },
  case is_repl_of_var_in_formula.forall_ : x P_u P_v h1_1 h1_ih
  {
    unfold is_bound_in at h2,
    push_neg at h2,
    cases h2,

    unfold is_bound_in at h3,
    push_neg at h3,
    cases h3,

    specialize h1_ih h2_right h3_right,
    apply deduction_theorem,
    sorry,
  },
end


theorem gen_right
  (P Q : formula)
  (x : variable_)
  (h1 : ¬ is_free_in x P) :
  is_proof ((forall_ x (P.imp_ Q)).imp_ (P.imp_ (forall_ x Q))) :=
begin
  obtain s1 := is_axiom.pred_1_ x P Q,
  apply is_deduct.mp_ (P.imp_ (forall_ x P)),
  apply is_deduct.mp_ ((forall_ x (P.imp_ Q)).imp_ ((forall_ x P).imp_ (forall_ x Q))),
  SC,
  apply is_deduct.axiom_,
  exact s1,
  apply is_deduct.axiom_,
  apply is_axiom.pred_2_,
  exact h1,
end


theorem gen_imp
  (P Q : formula)
  (x : variable_)
  (h1 : ¬ is_free_in x (P.imp_ Q)) :
  is_proof ((P.imp_ Q).imp_ ((forall_ x P).imp_ (forall_ x Q))) :=
begin
  apply is_deduct.mp_ ((forall_ x (P.imp_ Q)).imp_ ((forall_ x P).imp_ (forall_ x Q))),
  apply is_deduct.mp_ ((P.imp_ Q).imp_ (forall_ x (P.imp_ Q))),
  SC,
  apply is_deduct.axiom_,
  apply is_axiom.pred_2_,
  exact h1,
  apply is_deduct.axiom_,
  apply is_axiom.pred_1_,
end


example
  (v t : variable_)
  (P : formula)
  (h1 : fast_admits v t P) :
  is_proof ((forall_ v P).imp_ (fast_replace_free v t P)) :=
begin
  sorry,
end


#lint
