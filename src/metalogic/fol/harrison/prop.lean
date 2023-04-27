import .deduct


set_option pp.parens true


namespace fol

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


theorem imp_insert
  (P Q R : formula)
  (h1 : is_proof (P.imp_ R)) :
  is_proof (P.imp_ (Q.imp_ R)) :=
begin
  apply imp_trans P R (Q.imp_ R),
  {
    exact h1,
  },
  {
    apply is_proof.prop_1_,
  }
end


theorem imp_swap
  (P Q R : formula)
  (h1 : is_proof (P.imp_ (Q.imp_ R))) :
  is_proof (Q.imp_ (P.imp_ R)) :=
begin
  apply imp_trans Q (P.imp_ Q) (P.imp_ R),
  {
    exact is_proof.prop_1_ Q P,
  },
  {
    apply is_proof.mp_ (P.imp_ (Q.imp_ R)),
    {
      apply is_proof.prop_2_,
    },
    {
      exact h1,
    },
  },
end


theorem imp_trans_th
  (P Q R : formula) :
  is_proof ((Q.imp_ R).imp_ ((P.imp_ Q).imp_ (P.imp_ R))) :=
begin
  apply imp_trans (Q.imp_ R) (P.imp_ (Q.imp_ R)) ((P.imp_ Q).imp_ (P.imp_ R)),
  {
    exact is_proof.prop_1_ (Q.imp_ R) P,
  },
  {
    exact is_proof.prop_2_ P Q R,
  }
end


theorem imp_add_concl
  (P Q R : formula)
  (h1 : is_proof (P.imp_ Q)) :
  is_proof ((Q.imp_ R).imp_ (P.imp_ R)) :=
begin
  apply is_proof.mp_ (P.imp_ Q),
  {
    apply imp_swap,
    exact imp_trans_th P Q R,
  },
  {
    exact h1,
  }
end


theorem imp_swap_th
  (P Q R : formula) :
  is_proof ((P.imp_ (Q.imp_ R)).imp_ (Q.imp_ (P.imp_ R))) :=
begin
  apply imp_trans (P.imp_ (Q.imp_ R)) ((P.imp_ Q).imp_ (P.imp_ R)) (Q.imp_ (P.imp_ R)),
  {
    apply is_proof.prop_2_ P Q R,
  },
  {
    apply imp_add_concl,
    apply is_proof.prop_1_,
  }
end


theorem imp_swap2
  (P Q R S T U : formula)
  (h1 : is_proof ((P.imp_ (Q.imp_ R)).imp_ (S.imp_ (T.imp_ U)))) :
  is_proof ((Q.imp_ (P.imp_ R)).imp_ (T.imp_ (S.imp_ U))) :=
begin
  apply imp_trans (Q.imp_ (P.imp_ R)) (P.imp_ (Q.imp_ R)) (T.imp_ (S.imp_ U)),
  {
    exact imp_swap_th Q P R,
  },
  {
    apply imp_trans (P.imp_ (Q.imp_ R)) (S.imp_ (T.imp_ U)) (T.imp_ (S.imp_ U)),
    {
      exact h1,
    },
    {
      exact imp_swap_th S T U,
    },
  },
end


theorem right_mp
  (P Q R : formula)
  (h1 : is_proof (P.imp_ (Q.imp_ R)))
  (h2 : is_proof (P.imp_ Q)) :
  is_proof (P.imp_ R) :=
begin
  apply imp_unduplicate,
  apply imp_trans P Q (P.imp_ R),
  {
    exact h2,
  },
  {
    exact imp_swap P Q R h1,
  }
end


theorem imp_trans2
  (P Q R S : formula)
  (h1 : is_proof (P.imp_ (Q.imp_ R)))
  (h2 : is_proof (R.imp_ S)) :
  is_proof (P.imp_ (Q.imp_ S)) :=
begin
  apply is_proof.mp_ (P.imp_ (Q.imp_ R)),
  {
    apply imp_add_assum,
    apply is_proof.mp_ (R.imp_ S),
    {
      exact imp_trans_th Q R S,
    },
    {
      exact h2,
    }
  },
  {
    exact h1,
  }
end


theorem axiom_doubleneg
  (P : formula) :
  is_proof (((P.imp_ false_).imp_ false_).imp_ P) :=
begin
  sorry,
end


theorem axiom_not
  (P : formula) :
  is_proof (P.not_.iff_ (P.imp_ false_)) :=
begin
  sorry,
end


theorem iff_imp1
  (P Q : formula)
  (h1 : is_proof (P.iff_ Q)) :
  is_proof (P.imp_ Q) :=
begin
  unfold formula.iff_ at h1,
  unfold formula.and_ at h1,
  sorry,
end


theorem iff_imp2
  (P Q : formula)
  (h1 : is_proof (P.iff_ Q)) :
  is_proof (Q.imp_ P) :=
begin
  unfold formula.iff_ at h1,
  unfold formula.and_ at h1,
  sorry,
end


theorem aux_2
  (P Q R : formula)
  (h1 : is_proof (P.imp_ (Q.imp_ R))) :
  is_proof ((Q.imp_ P).imp_ (Q.imp_ R)) := sorry

theorem aux_2'
  (P Q R S : formula)
  (h1 : is_proof S)
  (h2 : is_proof (P.imp_ (Q.imp_ R))) :
  is_proof ((S.imp_ P).imp_ (Q.imp_ R)) := sorry


#lint

end fol
