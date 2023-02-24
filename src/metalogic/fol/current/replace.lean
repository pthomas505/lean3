import .binders
import .misc_list

import data.finset


set_option pp.parens true


open formula


/-
[margaris]
pg. 48

If $P$ is a formula, $v$ is a variable, and $t$ is a term, then $P(t/v)$ is the result of replacing each free occurrence of $v$ in $P$ by an occurrence of $t$.
-/

/--
  replace_free_aux v t ∅ P =
  P (t/v) ;
  v → t in P
-/
def replace_free_aux (v t : variable_) : finset variable_ → formula → formula
| _ (true_) := true_
| binders (pred_ name args) :=
    pred_ name (args.map (fun (x : variable_),
      if x = v ∧ x ∉ binders
      then t
      else x))
| binders (not_ P) := not_ (replace_free_aux binders P)
| binders (imp_ P Q) :=
    imp_ (replace_free_aux binders P) (replace_free_aux binders Q)
| binders (forall_ x P) := forall_ x (replace_free_aux (binders ∪ {x}) P)

/--
  replace_free v t P =
  P (t/v) ;
  v → t in P
-/
def replace_free (v t : variable_) (P : formula) : formula :=
  replace_free_aux v t ∅ P


/--
  fast_replace_free v t P =
  P (t/v) ;
  v → t in P
-/
def fast_replace_free (v t : variable_) : formula → formula
| (true_) := true_
| (pred_ name args) :=
    pred_ name (args.map (fun (x : variable_),
      if x = v
      then t
      else x))
| (not_ P) := not_ (fast_replace_free P)
| (imp_ P Q) := imp_ (fast_replace_free P) (fast_replace_free Q)
| (forall_ x P) :=
  if v = x
  then forall_ x P -- v is not free in P
  else forall_ x (fast_replace_free P)


theorem fast_replace_free_id
  (P : formula)
  (v : variable_) :
  fast_replace_free v v P = P :=
begin
  induction P,
  case formula.true_
  {
    refl,
  },
  case formula.pred_ : name args
  {
    unfold fast_replace_free,
    congr,
    simp only [list.map_eq_self_iff, ite_eq_right_iff],
    intros x a1 a2,
    subst a2,
  },
  case formula.not_ : P P_ih
  {
    unfold fast_replace_free,
    congr,
    exact P_ih,
  },
  case formula.imp_ : P Q P_ih Q_ih
  {
    unfold fast_replace_free,
    congr,
    {
      exact P_ih,
    },
    {
      exact Q_ih,
    }
  },
  case formula.forall_ : x P P_ih
  {
    unfold fast_replace_free,
    simp only [ite_eq_left_iff, eq_self_iff_true, true_and],
    intros a1,
    exact P_ih,
  },
end


theorem not_free_in_fast_replace_free_id
  (P : formula)
  (v t : variable_)
  (h1 : ¬ is_free_in v P) :
  fast_replace_free v t P = P :=
begin
  induction P,
  case formula.true_
  {
    refl,
  },
  case formula.pred_ : name args
  {
    unfold is_free_in at h1,
    simp only [list.mem_to_finset] at h1,

    unfold fast_replace_free,
    congr,
    simp only [list.map_eq_self_iff, ite_eq_right_iff],
    intros x a1 a2,
    subst a2,
    contradiction,
  },
  case formula.not_ : P P_ih
  {
    unfold is_free_in at h1,

    unfold fast_replace_free,
    congr,
    exact P_ih h1,
  },
  case formula.imp_ : P Q P_ih Q_ih
  {
    unfold is_free_in at h1,
    push_neg at h1,
    cases h1,

    unfold fast_replace_free,
    congr,
    {
      exact P_ih h1_left,
    },
    {
      exact Q_ih h1_right,
    }
  },
  case formula.forall_ : x P P_ih
  {
    unfold is_free_in at h1,
    push_neg at h1,

    unfold fast_replace_free,
    split_ifs,
    {
      simp only [eq_self_iff_true, and_self],
    },
    {
      simp only [eq_self_iff_true, true_and],
      apply P_ih,
      apply h1,
      exact h,
    }
  },
end


theorem fast_replace_free_inverse
  (P : formula)
  (v t : variable_)
  (h1 : ¬ occurs_in t P) :
  fast_replace_free t v (fast_replace_free v t P) = P :=
begin
  induction P,
  case formula.true_
  {
    refl,
  },
  case formula.pred_ : name args
  {
    unfold occurs_in at h1,

    unfold fast_replace_free,
    congr,
    simp only [list.map_map, list.map_eq_self_iff, function.comp_app],
    intros x a1,
    split_ifs,
    {
      symmetry,
      exact h,
    },
    {
      subst h_1,
      contradiction,
    },
    {
      refl,
    }
  },
  case formula.not_ : P P_ih
  {
    unfold occurs_in at h1,

    unfold fast_replace_free,
    congr,
    exact P_ih h1,
  },
  case formula.imp_ : P Q P_ih Q_ih
  {
    unfold occurs_in at h1,
    push_neg at h1,
    cases h1,

    unfold fast_replace_free,
    congr,
    {
      exact P_ih h1_left,
    },
    {
      exact Q_ih h1_right,
    }
  },
  case formula.forall_ : x P P_ih
  {
    unfold occurs_in at h1,
    push_neg at h1,
    cases h1,

    unfold fast_replace_free,
    split_ifs,
    {
      unfold fast_replace_free,
      simp [if_neg h1_left],
      apply not_free_in_fast_replace_free_id,
      intros contra,
      apply h1_right,
      apply is_free_in_imp_occurs_in,
      exact contra,
    },
    {
      unfold fast_replace_free,
      simp only [eq_comm],
      simp only [if_neg h1_left],
      simp only [eq_self_iff_true, true_and],
      symmetry,
      exact P_ih h1_right,
    }
  },
end


theorem not_is_free_in_fast_replace_free
  (P : formula)
  (v t : variable_)
  (h1 : ¬ v = t) :
  ¬ is_free_in v (fast_replace_free v t P) :=
begin
  induction P,
  case formula.true_
  {
    unfold fast_replace_free,
    unfold is_free_in,
    simp only [not_false_iff],
  },
  case formula.pred_ : name args
  {
    unfold fast_replace_free,
    unfold is_free_in,
    simp only [list.mem_to_finset, list.mem_map, not_exists, not_and],
    intros x a1,
    split_ifs,
    {
      simp only [eq_comm],
      exact h1,
    },
    {
      exact h,
    }
  },
  case formula.not_ : P P_ih
  {
    unfold fast_replace_free,
    unfold is_free_in,
    exact P_ih,
  },
  case formula.imp_ : P Q P_ih Q_ih
  {
    unfold fast_replace_free,
    unfold is_free_in,
    push_neg,
    split,
    {
      exact P_ih,
    },
    {
      exact Q_ih,
    }
  },
  case formula.forall_ : x P P_ih
  {
    unfold fast_replace_free,
    split_ifs,
    {
      unfold is_free_in,
      simp only [not_and],
      intros a1,
      contradiction,
    },
    {
      unfold is_free_in,
      push_neg,
      intros a1,
      exact P_ih,
    }
  },
end


lemma replace_free_aux_mem_binders
  (P : formula)
  (v t : variable_)
  (binders : finset variable_)
  (h1 : v ∈ binders) :
  replace_free_aux v t binders P = P :=
begin
  induction P generalizing binders,
  case formula.true_ : binders h1
  {
    refl,
  },
  case formula.pred_ : name args binders h1
  {
    unfold replace_free_aux,
    congr,
    simp only [list.map_eq_self_iff, ite_eq_right_iff, and_imp],
    intros x a1 a2 a3,
    subst a2,
    contradiction,
  },
  case formula.not_ : P P_ih binders h1
  {
    unfold replace_free_aux,
    congr,
    exact P_ih binders h1,
  },
  case formula.imp_ : P Q P_ih Q_ih binders h1
  {
    unfold replace_free_aux,
    congr,
    {
      exact P_ih binders h1,
    },
    {
      exact Q_ih binders h1,
    }
  },
  case formula.forall_ : x P P_ih binders h1
  {
    unfold replace_free_aux,
    simp only [eq_self_iff_true, true_and],
    apply P_ih,
    simp only [finset.mem_union, finset.mem_singleton],
    apply or.intro_left,
    exact h1,
  },
end


lemma replace_free_aux_eq_fast_replace_free
  (P : formula)
  (v t : variable_)
  (binders : finset variable_)
  (h1 : v ∉ binders) :
  replace_free_aux v t binders P = fast_replace_free v t P :=
begin
  induction P generalizing binders,
  case formula.true_ : binders h1
  {
    refl,
  },
  case formula.pred_ : name args binders h1
  {
    unfold replace_free_aux,
    unfold fast_replace_free,
    congr,
    funext,
    by_cases c1 : x = v,
    {
      simp only [if_pos c1],
      subst c1,
      simp only [eq_self_iff_true, true_and, ite_not, ite_eq_right_iff],
      intros a1,
      contradiction,
    },
    {
      simp only [if_neg c1],
      simp only [ite_eq_right_iff, and_imp],
      intros a1,
      contradiction,
    }
  },
  case formula.not_ : P P_ih binders h1
  {
    unfold replace_free_aux,
    unfold fast_replace_free,
    simp only,
    exact P_ih binders h1,
  },
  case formula.imp_ : P Q P_ih Q_ih binders h1
  {
    unfold replace_free_aux,
    unfold fast_replace_free,
    simp only,
    split,
    {
      exact P_ih binders h1,
    },
    {
      exact Q_ih binders h1,
    }
  },
  case formula.forall_ : x P P_ih binders h1
  {
    unfold replace_free_aux,
    unfold fast_replace_free,
    split_ifs,
    {
      simp only [eq_self_iff_true, true_and],
      apply replace_free_aux_mem_binders,
      simp only [finset.mem_union, finset.mem_singleton],
      apply or.intro_right,
      exact h,
    },
    {
      simp only [eq_self_iff_true, true_and],
      apply P_ih,
      simp only [finset.mem_union, finset.mem_singleton],
      push_neg,
      split,
      {
        exact h1,
      },
      {
        exact h,
      }
    }
  },
end

theorem replace_free_eq_fast_replace_free
  (P : formula)
  (v t : variable_) :
  replace_free v t P = fast_replace_free v t P :=
begin
  unfold replace_free,
  apply replace_free_aux_eq_fast_replace_free,
  simp only [finset.not_mem_empty, not_false_iff],
end


#lint
