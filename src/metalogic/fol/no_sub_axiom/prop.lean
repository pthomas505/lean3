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


#lint
