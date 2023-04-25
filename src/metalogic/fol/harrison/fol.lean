import .prop

import metalogic.fol.common.admits
import metalogic.fol.aux.misc_list


set_option pp.parens true


open formula


lemma eq_congr_eq
  (x_0 x_1 y_0 y_1 : variable_) :
  is_proof ((eq_ x_0 y_0).imp_ ((eq_ x_1 y_1).imp_
    ((eq_ x_0 x_1).imp_ (eq_ y_0 y_1)))) :=
begin
  apply is_proof.eq_3_ (pred_name_.mk "=") [x_0, x_1] [y_0, y_1],
  simp only [list.length],
end


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
      apply eq_congr_eq x x y x,
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
      apply eq_congr_eq,
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


lemma eq_imp_map
  (P : formula)
  (v t : variable_)
  (args : list variable_)
  (σ : variable_ → variable_) :
  is_proof ((list.foldr imp_ P (list.map (fun (x : variable_), eq_ x (ite (x = v) t x)) args)).imp_ ((eq_ v t).imp_ P)) :=
begin
  induction args,
  case list.nil
  {
    simp only [list.map_nil, list.foldr_nil],
    apply is_proof.prop_1_,
  },
  case list.cons : args_hd args_tl args_ih
  {
    simp only [list.map, list.foldr_cons],
    split_ifs,
    {
      subst h,
      apply aux_2,
      exact args_ih,
    },
    {
      apply aux_2',
      {
        apply is_proof.eq_2_,
      },
      {
        exact args_ih,
      }
    }
  },
end


lemma aux_12
  (P P' : formula)
  (x y z : variable_)
  (h1 : (¬is_free_in z (eq_ x y))) 
  (h2 : is_proof ((eq_ x y).imp_ (P.imp_ P'))) :
  is_proof ((eq_ x y).imp_ ((forall_ z P).imp_ (forall_ z P'))) :=
begin
  apply imp_trans (eq_ x y) (forall_ z (eq_ x y)) ((forall_ z P).imp_ (forall_ z P')),
  {
    apply is_proof.pred_2_,
    exact h1,
  },
  {
    apply imp_trans (forall_ z (eq_ x y)) (forall_ z (P.imp_ P')) ((forall_ z P).imp_ (forall_ z P')),
    {
      apply is_proof.mp_ (forall_ z ((eq_ x y).imp_ (P.imp_ P'))),
      {
        apply is_proof.pred_1_,
      },
      {
        apply is_proof.gen_,
        exact h2,
      }
    },
    {
      apply is_proof.pred_1_,
    },
  }
end


example
  (v t : variable_)
  (P : formula)
  (binders : finset variable_)
  (h1 : ¬ v = t)
  (h2 : fast_admits_aux v t binders P) :
  is_proof ((eq_ v t).imp_ (P.imp_ (fast_replace_free v t P))) :=
begin
  induction P generalizing binders,
  case formula.true_
  { admit },
  case formula.pred_ : name args
  {
    unfold fast_replace_free,

    set σ := fun (x : variable_), ite (x = v) t x,

    obtain s1 := is_proof.eq_3_ name args (args.map σ),
    simp only [list.length_map, eq_self_iff_true, forall_true_left] at s1,
    simp only [list_map₂_of_map] at s1,

    apply is_proof.mp_ (list.foldr imp_ ((pred_ name args).imp_ (pred_ name (list.map σ args))) (list.map (fun (x : variable_), eq_ x (σ x)) args)),
    {
      exact eq_imp_map ((pred_ name args).imp_ (pred_ name (list.map σ args))) v t args σ,
    },
    {
      exact s1,
    }
  },
  case formula.not_ : P_ᾰ P_ih
  { admit },
  case formula.imp_ : P_ᾰ P_ᾰ_1 P_ih_ᾰ P_ih_ᾰ_1
  { admit },
  case formula.forall_ : x P P_ih
  {
    unfold fast_admits_aux at h2,

    cases h2,
    {
      subst h2,
      unfold fast_replace_free,
      simp only [eq_self_iff_true, if_true],
      apply add_assum,
      apply imp_refl,
    },
    {
      by_cases c1 : t = x,
      {
        have s1 : (fast_replace_free v t (forall_ x P) = forall_ x P),
        apply not_free_in_fast_replace_free_self (forall_ x P) v t,
        unfold is_free_in,
        simp only [not_and],
        intros a1,
        apply fast_admits_aux_mem_binders P v t (binders ∪ {x}) h2,
        simp only [finset.mem_union, finset.mem_singleton],
        right,
        exact c1,

        simp only [s1],
        apply add_assum,
        apply imp_refl,
      },
      {
        unfold fast_replace_free,
        split_ifs,
        {
          apply add_assum,
          apply imp_refl,
        },
        {
          apply aux_12,
          unfold formula.eq_,
          unfold is_free_in,
          squeeze_simp,
          push_neg,
          tauto,
          apply P_ih (binders ∪ {x}),
          exact h2,
        }
      },
    },
  },
end


example
  (P : formula)
  (v t : variable_)
  (h1 : fast_admits v t P)
  (h2 : ¬ (v = t)) :
  is_proof ((forall_ v P).imp_ (fast_replace_free v t P)) :=
begin
  sorry,
end


#lint
