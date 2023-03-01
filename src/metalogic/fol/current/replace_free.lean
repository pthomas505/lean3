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
  Helper function for replace_free.
-/
def replace_free_aux (v t : variable_) : finset variable_ → formula → formula
| _ (true_) := true_
| binders (pred_ name args) :=
    pred_
    name
    (args.map (fun (x : variable_), if x = v ∧ x ∉ binders then t else x))
| binders (eq_ x y) :=
    eq_
    (if x = v ∧ x ∉ binders then t else x)
    (if y = v ∧ y ∉ binders then t else y)
| binders (not_ P) := not_ (replace_free_aux binders P)
| binders (imp_ P Q) :=
    imp_
    (replace_free_aux binders P)
    (replace_free_aux binders Q)
| binders (forall_ x P) := forall_ x (replace_free_aux (binders ∪ {x}) P)

/--
  replace_free v t P :=

  P(t/v)

  v → t in P for each free occurrence of v in P

  The result of replacing each free occurrence of v in P by an occurrence of t.
-/
def replace_free (v t : variable_) (P : formula) : formula :=
  replace_free_aux v t ∅ P


/--
  fast_replace_free v t P :=

  P(t/v)

  v → t in P for each free occurrence of v in P

  The result of replacing each free occurrence of v in P by an occurrence of t.

  This is a more efficient version of replace_free.
-/
def fast_replace_free (v t : variable_) : formula → formula
| (true_) := true_
| (pred_ name args) :=
    pred_
    name
    (args.map (fun (x : variable_), if x = v then t else x))
| (eq_ x y) :=
    eq_
    (if x = v then t else x)
    (if y = v then t else y)
| (not_ P) := not_ (fast_replace_free P)
| (imp_ P Q) := imp_ (fast_replace_free P) (fast_replace_free Q)
| (forall_ x P) :=
    if v = x
    then forall_ x P -- v is not free in P
    else forall_ x (fast_replace_free P)


/--
  Specialized version of function.update.
-/
def function.update_ite
  {α β : Type}
  [decidable_eq α]
  (f : α → β)
  (a' : α) (b : β) (a : α) :=
  if a = a' then b else f a

/--
  fast_simult_replace_free σ P := The simultaneous replacement of each free occurence of any variable v in the formula P by σ v.
-/
def fast_simult_replace_free : (variable_ → variable_) → formula → formula
| _ true_ := true_
| σ (pred_ name args) := pred_ name (args.map σ)
| σ (eq_ x y) := eq_ (σ x) (σ y)
| σ (not_ P) := not_ (fast_simult_replace_free σ P)
| σ (imp_ P Q) := imp_ (fast_simult_replace_free σ P) (fast_simult_replace_free σ Q)
| σ (forall_ x P) := forall_ x (fast_simult_replace_free (function.update_ite σ x x) P)


def simult_replace_free (σ : variable_ → variable_) : finset variable_ → formula → formula
| _ true_ := true_
| binders (pred_ name args) :=
    pred_
    name
    (args.map (fun (x : variable_), if x ∈ binders then x else σ x))
| binders (eq_ x y) :=
    eq_
    (if x ∈ binders then x else σ x)
    (if y ∈ binders then y else σ y)
| binders (not_ P) := not_ (simult_replace_free binders P)
| binders (imp_ P Q) :=
    imp_
    (simult_replace_free binders P)
    (simult_replace_free binders Q)
| binders (forall_ x P) :=
    forall_ x (simult_replace_free (binders ∪ {x}) P)


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
    simp only [eq_self_iff_true, list.map_eq_self_iff, ite_eq_right_iff, true_and],
    tauto,
  },
  case formula.eq_ : x y
  {
    unfold fast_replace_free,
    simp only [ite_eq_right_iff],
    tauto,
  },
  case formula.not_ : P P_ih
  {
    solve_by_elim,
  },
  case formula.imp_ : P Q P_ih Q_ih
  {
    unfold fast_replace_free,
    simp only,
    tauto,
  },
  case formula.forall_ : x P P_ih
  {
    unfold fast_replace_free,
    simp only [ite_eq_left_iff, eq_self_iff_true, true_and],
    tauto,
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
  case formula.eq_ : x y
  {
    unfold is_free_in at h1,
    push_neg at h1,
    cases h1,

    unfold fast_replace_free,
    congr,
    {
      simp only [ite_eq_right_iff],
      tauto,
    },
    {
      simp only [ite_eq_right_iff],
      tauto,
    }
  },
  case formula.not_ : P P_ih
  {
    solve_by_elim,
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
    simp only [ite_eq_left_iff, eq_self_iff_true, true_and],
    tauto,
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
    simp only [list.mem_to_finset] at h1,

    unfold fast_replace_free,
    congr,
    simp only [list.map_map, list.map_eq_self_iff, function.comp_app, ite_eq_left_iff],
    intros x a1,
    by_cases c1 : x = v,
    {
      subst c1,
      simp only [eq_self_iff_true, not_true, is_empty.forall_iff, if_true],
    },
    {
      simp only [if_neg c1],
      simp only [ite_eq_right_iff],
      intros a2,
      specialize a2 c1,
      subst a2,
      contradiction,
    },
  },
  case formula.eq_ : x y
  {
    unfold occurs_in at h1,
    push_neg at h1,
    cases h1,

    unfold fast_replace_free,
    congr,
    {
      simp only [ite_eq_left_iff],
      by_cases c1 : x = v,
      {
        subst c1,
        simp only [eq_self_iff_true, not_true, is_empty.forall_iff, if_true],
      },
      {
        simp only [if_neg c1],
        simp only [ite_eq_right_iff],
        tauto,
      },
    },
    {
      simp only [ite_eq_left_iff],
      by_cases c1 : y = v,
      {
        subst c1,
        simp only [eq_self_iff_true, not_true, is_empty.forall_iff, if_true],
      },
      {
        simp only [if_neg c1],
        simp only [ite_eq_right_iff],
        tauto,
      },
    }
  },
  case formula.not_ : P P_ih
  {
    solve_by_elim,
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
      contrapose! h1_right,
      exact is_free_in_imp_occurs_in P t h1_right,
    },
    {
      unfold fast_replace_free,
      simp only [if_neg h1_left],
      tauto,
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
    intros a1,
    assumption,
  },
  case formula.pred_ : name args
  {
    unfold fast_replace_free,
    unfold is_free_in,
    simp only [list.mem_to_finset, list.mem_map, not_exists, not_and],
    intros x a1,
    split_ifs,
    {
      tauto,
    },
    {
      exact h,
    }
  },
  case formula.eq_ : x y
  {
    unfold fast_replace_free,
    unfold is_free_in,
    push_neg,
    split,
    {
      split_ifs,
      {
        exact h1,
      },
      {
        tauto,
      }
    },
    {
      split_ifs,
      {
        exact h1,
      },
      {
        tauto,
      }
    }
  },
  case formula.not_ : P P_ih
  {
    assumption,
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
      tauto,
    },
    {
      unfold is_free_in,
      tauto,
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
    simp only [eq_self_iff_true, list.map_eq_self_iff, ite_eq_right_iff, and_imp, true_and],
    intros x a1 a2 a3,
    subst a2,
    contradiction,
  },
  case formula.eq_ : x y binders h1
  {
    unfold replace_free_aux,
    congr,
    {
      simp only [ite_eq_right_iff, and_imp],
      intros a1 a2,
      subst a1,
      contradiction,
    },
    {
      simp only [ite_eq_right_iff, and_imp],
      intros a1 a2,
      subst a1,
      contradiction,
    }
  },
  case formula.not_ : P P_ih binders h1
  {
    solve_by_elim,
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
    tauto,
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
      subst c1,
      simp only [eq_self_iff_true, true_and, ite_not, if_true, ite_eq_right_iff],
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
  case formula.eq_ : x y binders h1
  {
    unfold replace_free_aux,
    unfold fast_replace_free,
    congr,
    {
      simp only [eq_iff_iff, and_iff_left_iff_imp],
      intros a1,
      subst a1,
      exact h1,
    },
    {
      simp only [eq_iff_iff, and_iff_left_iff_imp],
      intros a1,
      subst a1,
      exact h1,
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


@[simp]
lemma function.update_ite_idem
  {α β : Type}
  [decidable_eq α]
  (f : α → β)
  (a : α)
  (x y : β)  :
  function.update_ite (function.update_ite f a x) a y =
    function.update_ite f a y :=
begin
  funext,
  unfold function.update_ite,
  split_ifs,
  {
    refl,
  },
  {
    refl,
  }
end


lemma function.update_ite_id
  {α : Type}
  [decidable_eq α]
  (x : α) :
  function.update_ite (id : α → α) x x = id :=
begin
  funext,
  unfold function.update_ite,
  split_ifs,
  {
    subst h,
    simp only [id.def],
  },
  {
    refl,
  }
end


lemma fast_simult_replace_free_id
  (P : formula) :
  fast_simult_replace_free id P = P :=
begin
  induction P,
  case formula.true_
  {
    refl,
  },
  case formula.pred_ : name args
  {
    unfold fast_simult_replace_free,
    simp only [list.map_id, eq_self_iff_true, and_self],
  },
  case formula.eq_ : x y
  {
    refl,
  },
  case formula.not_ : P P_ih
  {
    solve_by_elim,
  },
  case formula.imp_ : P Q P_ih Q_ih
  {
    unfold fast_simult_replace_free,
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
    unfold fast_simult_replace_free,
    simp only [eq_self_iff_true, true_and],
    simp only [function.update_ite_id],
    exact P_ih,
  },
end


example
  (P : formula)
  (v t : variable_) :
  fast_simult_replace_free (function.update_ite id v t) P = fast_replace_free v t P :=
begin
  induction P,
  case formula.true_
  {
    refl,
  },
  case formula.pred_ : name args
  {
    refl,
  },
  case formula.eq_ : x y
  {
    refl,
  },
  case formula.not_ : P P_ih
  {
    unfold fast_simult_replace_free,
    unfold fast_replace_free,
    congr,
    exact P_ih,
  },
  case formula.imp_ : P Q P_ih Q_ih
  {
    unfold fast_simult_replace_free,
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
    unfold fast_simult_replace_free,
    unfold fast_replace_free,
    split_ifs,
    {
      subst h,
      simp only [eq_self_iff_true, function.update_ite_idem, true_and],

      simp only [function.update_ite_id],
      apply fast_simult_replace_free_id,
    },
    {
      have s1 : (function.update_ite (function.update_ite (id : variable_ → variable_) v t) x x) = function.update_ite id v t,
      funext,
      unfold function.update_ite,
      split_ifs,
      {
        subst h_1,
        tauto,
      },
      {
        subst h_1,
        simp only [id.def],
      },
      {
        refl,
      },
      {
        refl,
      },

      simp only [eq_self_iff_true, true_and],
      simp only [s1],
      exact P_ih,
    }
  },
end


#lint
