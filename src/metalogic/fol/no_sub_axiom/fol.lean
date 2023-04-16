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


#lint
