import .deduct


set_option pp.parens true


open formula


theorem imp_refl
  (P : formula) :
  is_proof (P.imp_ P) :=
begin
  apply is_proof.mp_ (P.imp_ (P.imp_ P)),
  {
    apply is_proof.mp_ (P.imp_ ((P.imp_ P).imp_ P)),
    {
      exact is_proof.prop_2_ P (P.imp_ P) P,
    },
    {
      exact is_proof.prop_1_ P (P.imp_ P),
    }
  },
  {
    exact is_proof.prop_1_ P P,
  },
end


theorem imp_unduplicate
  (P Q : formula)
  (h1 : is_proof (P.imp_ (P.imp_ Q))) :
  is_proof (P.imp_ Q) :=
begin
  apply is_proof.mp_ (P.imp_ P),
  {
    apply is_proof.mp_ (P.imp_ (P.imp_ Q)),
    {
      apply is_proof.prop_2_,
    },
    {
      exact h1,
    }
  },
  {
    exact imp_refl P,
  }
end


theorem add_assum
  (P Q : formula)
  (h1 : is_proof Q) :
  is_proof (P.imp_ Q) :=
begin
  apply is_proof.mp_ Q,
  {
    apply is_proof.prop_1_,
  },
  {
    exact h1,
  }
end


theorem imp_add_assum
  (P Q R : formula)
  (h1 : is_proof (Q.imp_ R)) :
  is_proof ((P.imp_ Q).imp_ (P.imp_ R)) :=
begin
  apply is_proof.mp_ (P.imp_ (Q.imp_ R)),
  {
    exact is_proof.prop_2_ P Q R,
  },
  {
    apply add_assum,
    exact h1,
  },
end


theorem imp_trans
  (P Q R : formula)
  (h1 : is_proof (P.imp_ Q))
  (h2 : is_proof (Q.imp_ R)) :
  is_proof (P.imp_ R) :=
begin
  apply is_proof.mp_ (P.imp_ Q),
  {
    exact imp_add_assum P Q R h2,
  },
  {
    exact h1,
  },
end


theorem imp_swap
  (P Q R : formula)
  (h1 : is_proof (P.imp_ (Q.imp_ R))) :
  is_proof (Q.imp_ (P.imp_ R)) :=
begin
  sorry,
end


#lint
