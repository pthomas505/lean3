import .prop


set_option pp.parens true


open formula


theorem eq_symm
  (x y : variable_) :
  is_proof ((eq_ x y).imp_ (eq_ y x)) :=
begin
  apply is_proof.mp_ (eq_ x x),
  {
    apply imp_swap,
    apply is_proof.mp_ (eq_ x x),
    {
      apply imp_swap,
      apply is_proof.eq_3_eq_ x x y x,
    },
    {
      apply is_proof.eq_2_,
    },
  },
  {
    apply is_proof.eq_2_,
  },
end


theorem eq_trans
  (x y z : variable_) :
  is_proof ((eq_ x y).imp_ ((eq_ y z).imp_ (eq_ x z))) :=
begin
  apply imp_trans (eq_ x y) (eq_ y x) ((eq_ y z).imp_ (eq_ x z)),
  {
    apply eq_symm x y,
  },
  {
    apply is_proof.mp_ (eq_ z z),
    {
      apply imp_swap,
      apply is_proof.eq_3_eq_,
    },
    {
      apply is_proof.eq_2_,
    }
  }
end


theorem gen_right_th
  (P Q : formula)
  (x : variable_)
  (h1 : ¬ is_free_in x P) :
  is_proof ((forall_ x (P.imp_ Q)).imp_ (P.imp_ (forall_ x Q))) :=
begin
  have s1 : is_proof (P.imp_ (forall_ x P)),
  apply is_proof.pred_2_,
  exact h1,

  have s2 : is_proof ((forall_ x (P.imp_ Q)).imp_ ((forall_ x P).imp_ (forall_ x Q))),
  exact is_proof.pred_1_ x P Q,

  apply imp_swap,
  apply imp_trans,
  exact s1,
  apply imp_swap,
  exact s2,
end


theorem genimp
  (P Q : formula)
  (x : variable_)
  (h1 : is_proof (P.imp_ Q)) :
  is_proof ((forall_ x P).imp_ (forall_ x Q)) :=
begin
  apply is_proof.mp_ (forall_ x (P.imp_ Q)),
  {
    apply is_proof.pred_1_,
  },
  {
    apply is_proof.gen_,
    exact h1,
  }
end


theorem gen_right
  (P Q : formula)
  (x : variable_)
  (h1 : ¬ is_free_in x P)
  (h2 : is_proof (P.imp_ Q)) :
  is_proof (P.imp_ (forall_ x Q)) :=
begin
  apply is_proof.mp_,
  apply gen_right_th,
  exact h1,
  apply is_proof.gen_,
  exact h2,
end


theorem exists_left_th
  (P Q : formula)
  (x : variable_)
  (h1 : ¬ is_free_in x Q) :
  is_proof ((forall_ x (P.imp_ Q)).imp_ ((exists_ x P).imp_ Q)) :=
begin
  apply imp_swap,
  apply imp_trans,
  {
    apply imp_trans,
    {
      apply iff_imp1,
      apply axiom_not,
    },
    {
      apply imp_add_concl,
      {
        apply genimp,
        {
          apply iff_imp2,
          apply axiom_not,
        },
      },
    }
  },
  {
    apply imp_swap,
    apply imp_trans2,
    {
      apply imp_trans,
      {
        apply imp_trans,
        {
          apply genimp,
          apply imp_swap,
          exact imp_trans_th P Q false_,
        },
        {
          apply gen_right_th,
          unfold formula.false_,
          unfold is_free_in,
          push_neg,
          simp only [not_false_iff, and_true],
          exact h1,
        },
      },
      {
        apply imp_swap,
        exact imp_trans_th (imp_ Q false_) (forall_ x (imp_ P false_)) false_,
      },
    },
    {
      exact axiom_doubleneg Q,
    },
  },
end


theorem exists_left
  (P Q : formula)
  (x : variable_)
  (h1 : ¬ is_free_in x Q)
  (h2 : is_proof (P.imp_ Q)) :
  is_proof ((exists_ x P).imp_ Q) :=
begin
  apply is_proof.mp_,
  {
    exact exists_left_th P Q x h1,
  },
  {
    apply is_proof.gen_,
    exact h2,
  },
end


theorem subspec
  (P Q : formula)
  (x t : variable_)
  (h1 : ¬ x = t)
  (h2 : ¬ is_free_in x Q)
  (h3 : is_proof ((eq_ x t).imp_ (P.imp_ Q))) :
  is_proof ((forall_ x P).imp_ Q) :=
begin
  apply is_proof.mp_,
  {
    apply imp_swap,
    apply imp_trans,
    {
      apply genimp,
      apply imp_swap,
      exact h3,
    },
    {
      apply exists_left_th,
      exact h2,
    }
  },
  {
    exact is_proof.eq_1_ x t h1,
  },
end


theorem subalpha
  (P Q : formula)
  (x y : variable_)
  (h1 : ¬ is_free_in x Q)
  (h2 : ¬ is_free_in y P)
  (h3 : is_proof ((eq_ x y).imp_ (P.imp_ Q))) :
  is_proof ((forall_ x P).imp_ (forall_ y Q)) :=
begin
  by_cases c1 : x = y,
  {
    subst c1,
    apply genimp,
    apply is_proof.mp_,
    {
      exact h3,
    },
    {
      exact is_proof.eq_2_ x,
    }
  },
  {
    apply gen_right,
    {
      unfold is_free_in,
      push_neg,
      intros a1,
      exact h2,
    },
    {
      exact subspec P Q x y c1 h1 h3,
    }
  }
end


#lint
