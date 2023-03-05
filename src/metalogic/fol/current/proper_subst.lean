import .admits
import .misc_list

import data.finset


set_option pp.parens true


open formula


inductive is_prop_sub : formula → variable_ → variable_ → formula → Prop
| true_
  (v t : variable_) :
  is_prop_sub true_ v t true_

| pred_
  (name : pred_name_) (args : list variable_)
  (v t : variable_) :
    is_prop_sub (pred_ name args) v t (pred_ name (args.map (fun (x : variable_), if x = v then t else x)))

| eq_
  (x y : variable_)
  (v t : variable_) :
    is_prop_sub (eq_ x y) v t (eq_ (if x = v then t else x) (if y = v then t else y))

| not_
  (P : formula)
  (v t : variable_)
  (P' : formula) :
  is_prop_sub P v t P' →
  is_prop_sub P.not_ v t P'.not_

| imp_
  (P Q : formula)
  (v t : variable_)
  (P' Q' : formula) :
  is_prop_sub P v t P' →
  is_prop_sub Q v t Q' →
  is_prop_sub (P.imp_ Q) v t (P'.imp_ Q')

| forall_same_
  (x : variable_) (P : formula)
  (v t : variable_) :
  v = x →
  is_prop_sub (forall_ x P) v t (forall_ x P)

| forall_diff_nel_
  (x : variable_) (P : formula)
  (v t : variable_)
  (P' : formula) :
  ¬ v = x →
  ¬ is_free_in v (forall_ x P) →
  is_prop_sub P v t P' →
  is_prop_sub (forall_ x P) v t (forall_ x P')

| forall_diff_
  (x : variable_) (P : formula)
  (v t : variable_)
  (P' : formula) :
  ¬ v = x →
  ¬ t = x →
  is_prop_sub P v t P' →
  is_prop_sub (forall_ x P) v t (forall_ x P')


lemma fast_admits_aux_and_fast_replace_free_imp_is_prop_sub
  (P P' : formula)
  (v u : variable_)
  (binders : finset variable_)
  (h1 : fast_admits_aux v u binders P)
  (h2 : fast_replace_free v u P = P') :
  is_prop_sub P v u P' :=
begin
  subst h2,
  induction P generalizing binders,
  case formula.true_ : binders h1
  {
    unfold fast_replace_free,
    apply is_prop_sub.true_,
  },
  case formula.pred_ : name args binders h1
  {
    unfold fast_replace_free,
    apply is_prop_sub.pred_,
  },
  case formula.eq_ : x y binders h1
  {
    unfold fast_replace_free,
    apply is_prop_sub.eq_,
  },
  case formula.not_ : P P_ih binders h1
  {
    unfold fast_admits_aux at h1,

    apply is_prop_sub.not_,
    exact P_ih binders h1,
  },
  case formula.imp_ : P Q P_ih Q_ih binders h1
  {
    unfold fast_admits_aux at h1,
    cases h1,

    apply is_prop_sub.imp_,
    {
      exact P_ih binders h1_left,
    },
    {
      exact Q_ih binders h1_right,
    }
  },
  case formula.forall_ : x P P_ih binders h1
  {
    unfold fast_admits_aux at h1,

    cases h1,
    {
      unfold fast_replace_free,
      split_ifs,
      apply is_prop_sub.forall_same_ x P v u h1,
    },
    {
      unfold fast_replace_free,
      split_ifs,
      {
        apply is_prop_sub.forall_same_ x P v u h,
      },
      {
        by_cases c1 : is_free_in v (forall_ x P),
        {
          apply is_prop_sub.forall_diff_,
          {
            exact h,
          },
          {
            unfold is_free_in at c1,
            cases c1,
            have s1 : u ∉ binders ∪ {x},
            apply fast_admits_aux_is_free_in P v u,
            {
              exact h1,
            },
            {
              exact c1_right,
            },

            simp only [finset.mem_union, finset.mem_singleton] at s1,
            push_neg at s1,
            cases s1,
            exact s1_right,
          },
          {
            apply P_ih (binders ∪ {x}),
            exact h1,
          }
        },
        {
          apply is_prop_sub.forall_diff_nel_,
          {
            exact h,
          },
          {
            exact c1,
          },
          {
            apply P_ih (binders ∪ {x}) h1,
          },
        }
      }
    }
  },
end


lemma is_prop_sub_imp_fast_admits_aux
  (P : formula)
  (v u : variable_)
  (binders : finset variable_)
  (h1 : ∃ (P' : formula), is_prop_sub P v u P')
  (h2 : u ∉ binders) :
  fast_admits_aux v u binders P :=
begin
  apply exists.elim h1,
  intros P' h1_1,
  clear h1,

  induction h1_1 generalizing binders,
  case is_prop_sub.true_ : h1_1_v h1_1_t binders h2
  {
    unfold fast_admits_aux,
  },
  case is_prop_sub.pred_ : h1_1_name h1_1_args h1_1_v h1_1_t binders h2
  {
    unfold fast_admits_aux,
    intros a1,
    exact h2,
  },
  case is_prop_sub.eq_ : h1_1_x h1_1_y h1_1_v h1_1_t binders h2
  {
    unfold fast_admits_aux,
    intros a1,
    exact h2,
  },
  case is_prop_sub.not_ : h1_1_P h1_1_v h1_1_t h1_1_P' h1_1_1 h1_1_ih binders h2
  {
    unfold fast_admits_aux,
    exact h1_1_ih binders h2,
  },
  case is_prop_sub.imp_ : h1_1_P h1_1_Q h1_1_v h1_1_t h1_1_P' h1_1_Q' h1_1_1 h1_1_2 h1_1_ih_1 h1_1_ih_2 binders h2
  {
    unfold fast_admits_aux,
    split,
    {
      exact h1_1_ih_1 binders h2,
    },
    {
      exact h1_1_ih_2 binders h2,
    }
  },
  case is_prop_sub.forall_same_ : h1_1_x h1_1_P h1_1_v h1_1_t h1_1_1 binders h2
  {
    unfold fast_admits_aux,
    apply or.intro_left,
    exact h1_1_1,
  },
  case is_prop_sub.forall_diff_nel_ : h1_1_x h1_1_P h1_1_v h1_1_t h1_1_P' h1_1_1 h1_1_2 h1_1_3 h1_1_ih binders h2
  {
    unfold is_free_in at h1_1_2,
    push_neg at h1_1_2,

    unfold fast_admits_aux,

    apply or.intro_right,
    apply not_is_free_in_imp_fast_admits_aux,
    apply h1_1_2,
    exact h1_1_1,
  },
  case is_prop_sub.forall_diff_ : h1_1_x h1_1_P h1_1_v h1_1_t h1_1_P' h1_1_1 h1_1_2 h1_1_3 h1_1_ih binders h2
  {
    unfold fast_admits_aux,
    apply or.intro_right,
    apply h1_1_ih,
    simp only [finset.mem_union, finset.mem_singleton],
    push_neg,
    split,
    {
      exact h2,
    },
    {
      exact h1_1_2,
    }
  },
end


lemma is_prop_sub_imp_fast_replace_free
  (P P' : formula)
  (v u : variable_)
  (h1 : is_prop_sub P v u P') :
  fast_replace_free v u P = P' :=
begin
  induction h1,
  case is_prop_sub.true_ : h1_v h1_t
  {
    refl,
  },
  case is_prop_sub.pred_ : h1_name h1_args h1_v h1_t
  {
    unfold fast_replace_free,
  },
  case is_prop_sub.eq_ : h1_x h1_y h1_v h1_t
  {
    unfold fast_replace_free,
  },
  case is_prop_sub.not_ : h1_P h1_v h1_t h1_P' h1_1 h1_ih
  {
    unfold fast_replace_free,
    congr,
    exact h1_ih,
  },
  case is_prop_sub.imp_ : h1_P h1_Q h1_v h1_t h1_P' h1_Q' h1_1 h1_2 h1_ih_1 h1_ih_2
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
  case is_prop_sub.forall_same_ : h1_x h1_P h1_v h1_t h1_1
  {
    apply not_free_in_fast_replace_free_id,
    unfold is_free_in,
    simp only [finset.mem_sdiff, finset.mem_singleton, not_and, not_not],
    intros a1,
    contradiction,
  },
  case is_prop_sub.forall_diff_nel_ : h1_x h1_P h1_v h1_t h1_P' h1_1 h1_2 h1_3 h1_ih
  {
    unfold fast_replace_free,
    split_ifs,
    simp only [eq_self_iff_true, true_and],
    apply h1_ih,
  },
  case is_prop_sub.forall_diff_ : h1_x h1_P h1_v h1_t h1_P' h1_1 h1_2 h1_3 h1_ih
  {
    unfold fast_replace_free,
    split_ifs,
    simp only [eq_self_iff_true, true_and],
    apply h1_ih,
  },
end


example
  (P P' : formula)
  (v u : variable_) :
  is_prop_sub P v u P' ↔
    (fast_admits v u P ∧ fast_replace_free v u P = P') :=
begin
  unfold fast_admits,
  split,
  {
    intros a1,
    split,
    {
      apply is_prop_sub_imp_fast_admits_aux,
      {
        apply exists.intro P',
        exact a1,
      },
      {
        simp only [finset.not_mem_empty, not_false_iff],
      }
    },
    {
      apply is_prop_sub_imp_fast_replace_free,
      exact a1,
    }
  },
  {
    intros a1,
    cases a1,
    exact fast_admits_aux_and_fast_replace_free_imp_is_prop_sub P P' v u ∅ a1_left a1_right,
  }
end
