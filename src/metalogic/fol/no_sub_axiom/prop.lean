import .deduct


set_option pp.parens true


open formula


theorem prop_refl
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


#lint
