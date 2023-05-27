import metalogic.fol.common.sub.one.rec.sub_one_rec_admits


set_option pp.parens true


namespace fol

open formula


/--
  is_free_sub F v t F' := True if and only if F' is the result of replacing in F each free occurrence of v by a free occurrence of t.
-/
inductive is_free_sub : formula → var_name → var_name → formula → Prop
| true_
  (v t : var_name) :
  is_free_sub true_ v t true_

| pred_
  (X : pred_name) (xs : list var_name)
  (v t : var_name) :
    is_free_sub (pred_ X xs) v t (pred_ X (xs.map (fun (x : var_name), if x = v then t else x)))

| not_
  (phi : formula)
  (v t : var_name)
  (phi' : formula) :
  is_free_sub phi v t phi' →
  is_free_sub phi.not_ v t phi'.not_

| imp_
  (phi psi : formula)
  (v t : var_name)
  (phi' psi' : formula) :
  is_free_sub phi v t phi' →
  is_free_sub psi v t psi' →
  is_free_sub (phi.imp_ psi) v t (phi'.imp_ psi')

| forall_not_free_in
  (x : var_name) (phi : formula)
  (v t : var_name) :
  ¬ is_free_in v (forall_ x phi) →
  is_free_sub (forall_ x phi) v t (forall_ x phi)

| forall_free_in
  (x : var_name) (phi : formula)
  (v t : var_name)
  (phi' : formula) :
  is_free_in v (forall_ x phi) →
  ¬ x = t →
  is_free_sub phi v t phi' →
  is_free_sub (forall_ x phi) v t (forall_ x phi')


lemma fast_admits_aux_and_fast_replace_free_imp_is_free_sub
  (F F' : formula)
  (v u : var_name)
  (binders : finset var_name)
  (h1 : fast_admits_aux v u binders F)
  (h2 : fast_replace_free v u F = F') :
  is_free_sub F v u F' :=
begin
  subst h2,
  induction F generalizing binders,
  case formula.true_ : binders h1
  {
    unfold fast_replace_free,
    apply is_free_sub.true_,
  },
  case formula.pred_ : X xs binders h1
  {
    unfold fast_replace_free,
    apply is_free_sub.pred_,
  },
  case formula.not_ : phi phi_ih binders h1
  {
    unfold fast_admits_aux at h1,

    apply is_free_sub.not_,
    exact phi_ih binders h1,
  },
  case formula.imp_ : phi psi phi_ih psi_ih binders h1
  {
    unfold fast_admits_aux at h1,
    simp at h1,
    cases h1,

    apply is_free_sub.imp_,
    {
      exact phi_ih binders h1_left,
    },
    {
      exact psi_ih binders h1_right,
    }
  },
  case formula.forall_ : x phi phi_ih binders h1
  {
    unfold fast_admits_aux at h1,
    simp at h1,

    unfold fast_replace_free,
    cases h1,
    {
      split_ifs,
      apply is_free_sub.forall_not_free_in,
      subst h1,
      unfold is_free_in,
      simp,
    },
    {
      split_ifs,
      {
        apply is_free_sub.forall_not_free_in,
        subst h,
        unfold is_free_in,
        simp,
      },
      {
        by_cases c1 : ↥(is_free_in v phi),
        {
          apply is_free_sub.forall_free_in,
          {
            unfold is_free_in,
            simp,
            split,
            {
              exact h,
            },
            {
              exact c1,
            }
          },
          {
            obtain s1 := fast_admits_aux_is_free_in phi v u (binders ∪ {x}) h1 c1,
            simp only [finset.mem_union, finset.mem_singleton] at s1,
            push_neg at s1,
            cases s1,

            simp only [eq_comm],
            exact s1_right,
          },
          {
            exact phi_ih (binders ∪ {x}) h1,
          },
        },
        {
          have s1 : fast_replace_free v u phi = phi,
          apply not_free_in_fast_replace_free_self,
          exact c1,

          simp only [s1],
          apply is_free_sub.forall_not_free_in,
          unfold is_free_in,
          simp,
          intros a1,
          simp at c1,
          exact c1,
        },
      },
    },
  },
end


lemma is_free_sub_imp_fast_admits_aux
  (F : formula)
  (v u : var_name)
  (binders : finset var_name)
  (h1 : ∃ (F' : formula), is_free_sub F v u F')
  (h2 : u ∉ binders) :
  fast_admits_aux v u binders F :=
begin
  apply exists.elim h1,
  intros F' h1_1,
  clear h1,

  induction h1_1 generalizing binders,
  case is_free_sub.true_ : h1_1_v h1_1_t binders h2
  {
    unfold fast_admits_aux,
    simp,
  },
  case is_free_sub.pred_ : h1_1_X h1_1_xs h1_1_v h1_1_t binders h2
  {
    unfold fast_admits_aux,
    simp,
    intros a1,
    exact h2,
  },
  case is_free_sub.not_ : h1_1_phi h1_1_v h1_1_t h1_1_phi' h1_1_1 h1_1_ih binders h2
  {
    unfold fast_admits_aux,
    exact h1_1_ih binders h2,
  },
  case is_free_sub.imp_ : h1_1_phi h1_1_psi h1_1_v h1_1_t h1_1_phi' h1_1_psi' h1_1_1 h1_1_2 h1_1_ih_1 h1_1_ih_2 binders h2
  {
    unfold fast_admits_aux,
    simp,
    split,
    {
      exact h1_1_ih_1 binders h2,
    },
    {
      exact h1_1_ih_2 binders h2,
    }
  },
  case is_free_sub.forall_not_free_in : h1_1_x h1_1_phi h1_1_v h1_1_t h1_1_1 binders h2
  {
    unfold is_free_in at h1_1_1,
    simp only [bool.of_to_bool_iff, not_and] at h1_1_1,

    unfold fast_admits_aux,
    simp,
    by_cases c1 : h1_1_v = h1_1_x,
    {
      left,
      exact c1,
    },
    {
      right,
      apply not_is_free_in_imp_fast_admits_aux,
      exact h1_1_1 c1,
    },
  },
  case is_free_sub.forall_free_in : h1_1_x h1_1_phi h1_1_v h1_1_t h1_1_phi' h1_1_1 h1_1_2 h1_1_3 h1_1_ih binders h2
  {
    unfold is_free_in at h1_1_1,
    simp at h1_1_1,
    cases h1_1_1,

    unfold fast_admits_aux,
    simp,
    right,
    apply h1_1_ih,
    simp only [finset.mem_union, finset.mem_singleton],
    push_neg,
    split,
    {
      exact h2,
    },
    {
      simp only [ne_comm],
      exact h1_1_2,
    }
  },
end


lemma is_free_sub_imp_fast_replace_free
  (F F' : formula)
  (v u : var_name)
  (h1 : is_free_sub F v u F') :
  fast_replace_free v u F = F' :=
begin
  induction h1,
  case is_free_sub.true_ : h1_v h1_t
  {
    refl,
  },
  case is_free_sub.pred_ : h1_X h1_xs h1_v h1_t
  {
    unfold fast_replace_free,
  },
  case is_free_sub.not_ : h1_phi h1_v h1_t h1_phi' h1_1 h1_ih
  {
    unfold fast_replace_free,
    congr,
    exact h1_ih,
  },
  case is_free_sub.imp_ : h1_phi h1_psi h1_v h1_t h1_phi' h1_psi' h1_1 h1_2 h1_ih_1 h1_ih_2
  {
    unfold fast_replace_free,
    congr,
    {
      exact h1_ih_1,
    },
    {
      exact h1_ih_2,
    }
  },
  case is_free_sub.forall_not_free_in : h1_x h1_phi h1_v h1_t h1_1
  {
    unfold is_free_in at h1_1,
    simp only [bool.of_to_bool_iff, not_and] at h1_1,

    unfold fast_replace_free,
    split_ifs,
    {
      simp only [eq_self_iff_true, and_self],
    },
    {
      split,
      {
        refl,
      },
      {
        apply not_free_in_fast_replace_free_self,
        exact h1_1 h,
      }
    }
  },
  case is_free_sub.forall_free_in : h1_x h1_phi h1_v h1_t h1_phi' h1_1 h1_2 h1_3 h1_ih
  {
    unfold is_free_in at h1_1,
    simp at h1_1,
    cases h1_1,

    unfold fast_replace_free,
    split_ifs,
    split,
    {
      refl,
    },
    {
      exact h1_ih,
    }
  },
end


example
  (F F' : formula)
  (v u : var_name) :
  is_free_sub F v u F' ↔
    (fast_admits v u F ∧ fast_replace_free v u F = F') :=
begin
  unfold fast_admits,
  split,
  {
    intros a1,
    split,
    {
      apply is_free_sub_imp_fast_admits_aux,
      {
        apply exists.intro F',
        exact a1,
      },
      {
        simp only [finset.not_mem_empty, not_false_iff],
      }
    },
    {
      apply is_free_sub_imp_fast_replace_free,
      exact a1,
    }
  },
  {
    intros a1,
    cases a1,
    exact fast_admits_aux_and_fast_replace_free_imp_is_free_sub F F' v u ∅ a1_left a1_right,
  }
end



theorem substitution_theorem_ind
  {D : Type}
  (I : interpretation' D)
  (V : valuation D)
  (v t : var_name)
  (F F' : formula)
  (h1 : is_free_sub F v t F') :
  holds D I (function.update_ite V v (V t)) F ↔
    holds D I V F' :=
begin
  induction h1 generalizing V,
  case fol.is_free_sub.true_ : h1_v h1_t V
  {
    unfold holds,
  },
  case is_free_sub.pred_ : h1_X h1_xs h1_v h1_t
  {
    unfold holds,
    congr' 2,
    simp only [list.map_map],
    simp only [list.map_eq_map_iff],
    intros x a1,
    unfold function.update_ite,
    split_ifs,
    {
      simp only [function.comp_app],
      simp only [if_pos h],
    },
    {
      simp only [function.comp_app],
      simp only [if_neg h],
    }
  },
  case is_free_sub.not_ : h1_phi h1_v h1_t h1_phi' h1_1 h1_ih
  {
    unfold holds,
    apply not_congr,
    apply h1_ih,
  },
  case is_free_sub.imp_ : h1_phi h1_psi h1_v h1_t h1_phi' h1_psi' h1_1 h1_2 h1_ih_1 h1_ih_2
  {
    unfold holds,
    apply imp_congr,
    apply h1_ih_1,
    apply h1_ih_2,
  },
  case is_free_sub.forall_not_free_in : h1_x h1_phi h1_v h1_t h1_1
  {
    unfold is_free_in at h1_1,
    simp only [bool.of_to_bool_iff, not_and, eq_ff_eq_not_eq_tt] at h1_1,

    unfold holds,
    apply forall_congr,
    intros d,
    apply holds_congr_var,
    intros x a1,
    unfold function.update_ite,
    split_ifs,
    refl,
    subst h_1,
    specialize h1_1 h,
    rewrite h1_1 at a1,
    contradiction,
    refl,
  },
  case is_free_sub.forall_free_in : h1_x h1_phi h1_v h1_t h1_phi' h1_1 h1_2 h1_3 h1_ih
  {
    unfold is_free_in at h1_1,
    simp only [bool.of_to_bool_iff] at h1_1,
    cases h1_1,

    unfold holds,
    apply forall_congr,
    intros d,

    specialize h1_ih (function.update_ite V h1_x d),

    rewrite <- h1_ih,
    apply holds_congr_var,
    intros x a1,
    funext,
    unfold function.update_ite,
    split_ifs,
    refl,
    subst h_1,
    contradiction,
    refl,
    subst h_2,
    contradiction,
    refl,
    refl,
  },
end


#lint

end fol
