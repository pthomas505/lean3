import .prop


set_option pp.parens true


open formula


theorem eq_symm
  (x y : variable_) :
  is_proof ((eq_ x y).imp_ (eq_ y x)) :=
begin
  apply is_proof.mp_ (eq_ y y),
  {
    apply is_proof.mp_ ((eq_ y y).imp_ ((eq_ x y).imp_ ((eq_ y x).imp_ (eq_ y y)))),
    {
      sorry,
    },
    {
      exact is_proof.eq_2_eq_ y x y y,
    }
  },
  {
    exact is_proof.eq_1_ y,
  },
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


theorem exists_left
  (P Q : formula)
  (x : variable_)
  (h1 : ¬ is_free_in x Q) :
  is_proof ((forall_ x (P.imp_ Q)).imp_ ((exists_ x P).imp_ Q)) :=
begin
  apply imp_swap,

end


#lint
