import .formula
import .misc_list

import data.finset


set_option pp.parens true


open formula


/-
[margaris]
pg. 48

An occurrence of a variable $v$ in a formula $P$ is bound if and only if it occurs in a subformula of $P$ of the form $\forall v Q$. An occurrence of $v$ in $P$ is free if and only if it is not a bound occurrence. The variable $v$ is free or bound in $P$ according as it has a free or bound occurrence in $P$.
-/


def formula.bound_var_set : formula → finset variable_
| (pred_ name args) := ∅
| (not_ P) := P.bound_var_set
| (imp_ P Q) := P.bound_var_set ∪ Q.bound_var_set
| (forall_ x P) := P.bound_var_set ∪ {x}

def is_bound_in (v : variable_) : formula → Prop
| (pred_ name args) := false
| (not_ P) := is_bound_in P
| (imp_ P Q) := is_bound_in P ∨ is_bound_in Q
| (forall_ x P) := v = x ∨ is_bound_in P


example
  (v : variable_)
  (P : formula) :
  is_bound_in v P ↔ v ∈ P.bound_var_set :=
begin
  induction P,
  case formula.pred_ : name args
  {
    refl,
  },
  case formula.not_ : P P_ih
  {
    unfold is_bound_in,
    unfold formula.bound_var_set,
    exact P_ih,
  },
  case formula.imp_ : P Q P_ih Q_ih
  {
    unfold is_bound_in,
    unfold formula.bound_var_set,
    simp only [finset.mem_union],
    exact iff.or P_ih Q_ih,
  },
  case formula.forall_ : x P P_ih
  {
    cases P_ih,

    unfold is_bound_in,
    unfold formula.bound_var_set,
    simp only [finset.mem_union, finset.mem_singleton],
    split,
    {
      intros a1,
      cases a1,
      {
        apply or.intro_right,
        exact a1,
      },
      {
        apply or.intro_left,
        exact P_ih_mp a1,
      }
    },
    {
      intros a1,
      cases a1,
      {
        apply or.intro_right,
        exact P_ih_mpr a1,
      },
      {
        apply or.intro_left,
        exact a1,
      }
    }
  },
end


def formula.free_var_set : formula → finset variable_
| (pred_ name args) := args.to_finset
| (not_ P) := P.free_var_set
| (imp_ P Q) := P.free_var_set ∪ Q.free_var_set
| (forall_ x P) := P.free_var_set \ {x}

def is_free_in (v : variable_) : formula → Prop
| (pred_ name args) := v ∈ args.to_finset
| (not_ P) := is_free_in P
| (imp_ P Q) := is_free_in P ∨ is_free_in Q
| (forall_ x P) := ¬ v = x ∧ is_free_in P


example
  (v : variable_)
  (P : formula) :
  is_free_in v P ↔ v ∈ P.free_var_set :=
begin
  induction P,
  case formula.pred_ : name args
  {
    refl,
  },
  case formula.not_ : P P_ih
  {
    unfold is_free_in,
    unfold formula.free_var_set,
    exact P_ih,
  },
  case formula.imp_ : P Q P_ih Q_ih
  {
    unfold is_free_in,
    unfold formula.free_var_set,
    simp only [finset.mem_union],
    exact iff.or P_ih Q_ih,
  },
  case formula.forall_ : x P P_ih
  {
    cases P_ih,

    unfold is_free_in,
    unfold formula.free_var_set,
    simp only [finset.mem_sdiff, finset.mem_singleton],
    split,
    {
      intros a1,
      cases a1,
      split,
      {
        exact P_ih_mp a1_right,
      },
      {
        exact a1_left,
      }
    },
    {
      intros a1,
      cases a1,
      split,
      {
        exact a1_right,
      },
      {
        exact P_ih_mpr a1_left,
      }
    }
  },
end


def occurs_in (v : variable_) : formula → Prop
| (pred_ name args) := v ∈ args
| (not_ P) := occurs_in P
| (imp_ P Q) := occurs_in P ∨ occurs_in Q
| (forall_ x P) := v = x ∨ occurs_in P


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
| binders (pred_ name args) :=
    pred_ name (args.map (fun (x : variable_),
      if v = x ∧ x ∉ binders
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


lemma replace_free_aux_id
  (P : formula)
  (v : variable_)
  (binders : finset variable_) :
  replace_free_aux v v binders P = P :=
begin
  induction P generalizing binders,
  case formula.pred_ : name args binders
  {
    unfold replace_free_aux,
    simp only [eq_self_iff_true, true_and],
    apply list.map_id',
    intro x,
    split_ifs,
    {
      cases h,
      exact h_left,
    },
    {
      refl,
    }
  },
  case formula.not_ : P P_ih binders
  {
    unfold replace_free_aux,
    congr,
    exact P_ih binders,
  },
  case formula.imp_ : P Q P_ih Q_ih binders
  {
    unfold replace_free_aux,
    congr,
    {
      exact P_ih binders,
    },
    {
      exact Q_ih binders,
    }
  },
  case formula.forall_ : x P P_ih binders
  {
    unfold replace_free_aux,
    congr,
    apply P_ih,
  },
end


lemma replace_free_id
  (P : formula)
  (v : variable_) :
  replace_free v v P = P :=
begin
  unfold replace_free,
  apply replace_free_aux_id,
end


lemma is_free_in_replace_free_aux
  (P : formula)
  (v t : variable_)
  (binders : finset variable_)
  (h1 : ¬ v = t)
  (h2 : v ∉ binders) :
  ¬ is_free_in v (replace_free_aux v t binders P) :=
begin
  induction P generalizing binders,
  case formula.pred_ : name args binders h2
  {
    unfold replace_free_aux,
    unfold is_free_in,
    simp only [list.mem_to_finset, list.mem_map, not_exists, not_and],
    intros x a1,
    split_ifs,
    {
      intros contra,
      apply h1,
      symmetry,
      exact contra,
    },
    {
      push_neg at h,
      intros contra,
      subst contra,
      simp only [eq_self_iff_true, forall_true_left] at h,
      contradiction,
    }
  },
  case formula.not_ : P P_ih binders h2
  {
    unfold replace_free_aux,
    unfold is_free_in,
    exact P_ih binders h2,
  },
  case formula.imp_ : P Q P_ih Q_ih binders h2
  {
    unfold replace_free_aux,
    unfold is_free_in,
    push_neg,
    split,
    {
      exact P_ih binders h2,
    },
    {
      exact Q_ih binders h2,
    }
  },
  case formula.forall_ : x P P_ih binders h2
  {
    unfold replace_free_aux,
    unfold is_free_in,
    simp only [not_and],
    intros a1,
    apply P_ih,
    simp only [finset.mem_union, finset.mem_singleton],
    push_neg,
    split,
    {
      exact h2,
    },
    {
      exact a1,
    }
  },
end


lemma is_free_in_replace_free
  (P : formula)
  (v t : variable_)
  (h1 : ¬ v = t) :
  ¬ is_free_in v (replace_free v t P) :=
begin
  unfold replace_free,
  apply is_free_in_replace_free_aux P v t ∅ h1,
  simp only [finset.not_mem_empty, not_false_iff],
end


lemma replace_free_aux_inverse
  (P : formula)
  (v t : variable_)
  (binders : finset variable_)
  (h1 : ¬ occurs_in t P)
  (h2 : t ∉ binders) :
  replace_free_aux t v binders (replace_free_aux v t binders P) = P :=
begin
  induction P generalizing binders,
  case formula.pred_ : name args binders
  {
    unfold occurs_in at h1,

    unfold replace_free_aux,
    congr,
    simp only [list.map_map],

    apply list.map_id'_alt,
    intros x a1,
    simp only [function.comp_app],
    by_cases c1 : (v = x) ∧ (x ∉ binders),
    {
      simp only [if_pos c1],
      simp only [eq_self_iff_true, true_and, ite_not],
      simp only [if_neg h2],
      cases c1,
      exact c1_left,
    },
    {
      simp only [if_neg c1],
      push_neg at c1,
      split_ifs,
      {
        cases h,
        subst h_left,
        contradiction,
      },
      {
        refl,
      }
    }
  },
  case formula.not_ : P P_ih binders
  {
    unfold occurs_in at h1,

    unfold replace_free_aux,
    congr,
    exact P_ih h1 binders h2,
  },
  case formula.imp_ : P Q P_ih Q_ih binders
  {
    unfold occurs_in at h1,
    push_neg at h1,
    cases h1,

    unfold replace_free_aux,
    congr,
    {
      exact P_ih h1_left binders h2,
    },
    {
      exact Q_ih h1_right binders h2,
    }
  },
  case formula.forall_ : x P P_ih binders
  {
    unfold occurs_in at h1,
    push_neg at h1,
    cases h1,

    unfold replace_free_aux,
    simp only [eq_self_iff_true, true_and],
    apply P_ih,
    {
      exact h1_right,
    },
    {
      simp only [finset.mem_union, finset.mem_singleton],
      push_neg,
      split,
      {
        exact h2,
      },
      {
        exact h1_left,
      }
    }
  },
end


lemma replace_free_inverse
  (P : formula)
  (v t : variable_)
  (h1 : ¬ occurs_in t P) :
  replace_free t v (replace_free v t P) = P :=
begin
  unfold replace_free,
  apply replace_free_aux_inverse P v t ∅ h1,
  simp only [finset.not_mem_empty, not_false_iff],
end


lemma replace_free_aux_mem_binders
  (P : formula)
  (v t : variable_)
  (binders : finset variable_)
  (h1 : v ∈ binders) :
  replace_free_aux v t binders P = P :=
begin
  induction P generalizing binders,
  case formula.pred_ : name args binders h1
  {
    unfold replace_free_aux,
    simp only [eq_self_iff_true, true_and],
    apply list.map_id',
    intros x,
    split_ifs,
    {
      cases h,
      subst h_left,
      contradiction,
    },
    {
      refl,
    }
  },
  case formula.not_ : P P_ih binders h1
  {
    unfold replace_free_aux,
    simp only,
    exact P_ih binders h1,
  },
  case formula.imp_ : P Q P_ih Q_ih binders h1
  {
    unfold replace_free_aux,
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
    simp only,
    split,
    {
      refl,
    },
    {
      apply P_ih,
      simp only [finset.mem_union, finset.mem_singleton],
      apply or.intro_left,
      exact h1,
    }
  },
end


/-- v → t -/
def replace
  {α : Type}
  [decidable_eq α]
  (v t x : α) : α :=
  if v = x then t else x

def fast_replace_free (v t : variable_) : formula → formula
| (pred_ name args) := pred_ name (args.map (replace v t))
| (not_ P) := not_ (fast_replace_free P)
| (imp_ P Q) := imp_ (fast_replace_free P) (fast_replace_free Q)
| (forall_ x P) :=
  if v = x
  then forall_ x P
  else forall_ x (fast_replace_free P)


lemma replace_free_aux_eq_fast_replace_free
  (P : formula)
  (v t : variable_)
  (binders : finset variable_)
  (h1 : v ∉ binders) :
  replace_free_aux v t binders P = fast_replace_free v t P :=
begin
  induction P generalizing binders,
  case formula.pred_ : name args binders h1
  {
    unfold replace_free_aux,
    unfold fast_replace_free,
    simp only [eq_self_iff_true, true_and],
    apply list.map_congr,
    intros x a1,
    split_ifs,
    {
      unfold replace,
      split_ifs,
      {
        refl,
      },
      {
        cases h,
        contradiction,
      }
    },
    {
      unfold replace,
      split_ifs,
      {
        subst h_1,
        push_neg at h,
        simp only [eq_self_iff_true, forall_true_left] at h,
        contradiction,
      },
      {
        refl,
      }
    },
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


example
  (P : formula)
  (v t : variable_) :
  replace_free v t P = fast_replace_free v t P :=
begin
  unfold replace_free,
  apply replace_free_aux_eq_fast_replace_free,
  simp only [finset.not_mem_empty, not_false_iff],
end


lemma fast_replace_free_not_mem_free
  (P : formula)
  (v t : variable_)
  (h1 : v ∉ P.free_var_set) :
  fast_replace_free v t P = P :=
begin
  induction P,
  case formula.pred_ : name args
  {
    induction args,
    case list.nil
    {
      unfold fast_replace_free,
      simp only [list.map_nil, eq_self_iff_true, and_self],
    },
    case list.cons : args_hd args_tl args_ih
    {
      unfold formula.free_var_set at h1,
      simp only [list.to_finset_cons, finset.mem_insert, list.mem_to_finset] at h1,
      push_neg at h1,
      cases h1,

      unfold formula.free_var_set at args_ih,
      unfold fast_replace_free at args_ih,
      simp only [list.mem_to_finset, eq_self_iff_true, true_and] at args_ih,

      unfold fast_replace_free,
      simp only [list.map, eq_self_iff_true, true_and],
      split,
      {
        unfold replace,
        split_ifs,
        {
          contradiction,
        },
        {
          refl,
        }
      },
      {
        exact args_ih h1_right,
      }
    },
  },
  case formula.not_ : P P_ih
  {
    unfold formula.free_var_set at h1,

    unfold fast_replace_free,
    congr,
    exact P_ih h1,
  },
  case formula.imp_ : P Q P_ih Q_ih
  {
    unfold formula.free_var_set at h1,
    simp only [finset.mem_union] at h1,
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
    unfold formula.free_var_set at h1,
    simp only [finset.mem_sdiff, finset.mem_singleton, not_and, not_not] at h1,

    unfold fast_replace_free,
    split_ifs,
    {
      simp only [eq_self_iff_true, and_self],
    },
    {
      simp only [eq_self_iff_true, true_and],
      apply P_ih,
      by_contradiction contra,
      apply h,
      exact h1 contra,
    }
  },
end


/-
[margaris]
pg. 48

If $v$ and $u$ are variables and $P$ is a formula, then $P$ admits $u$ for $v$ if and only if there is no free occurrence of $v$ in $P$ that becomes a bound occurrence of $u$ in $P(u/v)$. If $t$ is a term, then $P$ admits $t$ for $v$ if and only if $P$ admits for $v$ every variable in $t$.
-/

/--
  admits_aux v u ∅ P =
  P admits u for v ;
  v → u in P
-/
def admits_aux (v u : variable_) : finset variable_ → formula → Prop
| binders (pred_ name args) :=
    (v ∈ args ∧ v ∉ binders) → -- if there is a free occurrence of v in P
    u ∉ binders -- then it does not become a bound occurrence of u in P(u/v)
| binders (not_ P) := admits_aux binders P
| binders (imp_ P Q) := admits_aux binders P ∧ admits_aux binders Q
| binders (forall_ x P) := admits_aux (binders ∪ {x}) P

/--
  admits v u P = 
  P admits u for v ;
  v → u in P
-/
def admits (v u : variable_) (P : formula) : Prop :=
  admits_aux v u ∅ P


lemma admits_aux_id
  (P : formula)
  (v : variable_)
  (binders : finset variable_) :
  admits_aux v v binders P :=
begin
  induction P generalizing binders,
  case formula.pred_ : name args binders
  {
    unfold admits_aux,
    simp only [and_imp, imp_self, implies_true_iff],
  },
  case formula.not_ : P P_ih binders
  {
    unfold admits_aux,
    exact P_ih binders,
  },
  case formula.imp_ : P Q P_ih Q_ih binders
  {
    unfold admits_aux,
    split,
    {
      exact P_ih binders,
    },
    {
      exact Q_ih binders,
    }
  },
  case formula.forall_ : x P P_ih binders
  {
    unfold admits_aux,
    apply P_ih,
  },
end


lemma admits_id
  (P : formula)
  (v : variable_) :
  admits v v P :=
begin
  unfold admits,
  apply admits_aux_id,
end


lemma replace_free_aux_admits_aux
  (P : formula)
  (v t : variable_)
  (binders : finset variable_)
  (h1 : ¬ occurs_in t P) :
  admits_aux t v binders (replace_free_aux v t binders P) :=
begin
  induction P generalizing binders,
  case formula.pred_ : name args binders
  {
    unfold occurs_in at h1,

    unfold replace_free_aux,
    unfold admits_aux,
    simp only [list.mem_map, ite_eq_left_iff, not_and, not_not, and_imp, forall_exists_index],
    intros x a1 a2 a3 contra,

    have s1 : x = t,
    apply a2,
    intros a4,
    subst a4,
    exact contra,

    subst s1,
    apply h1,
    exact a1,
  },
  case formula.not_ : P P_ih binders
  {
    unfold occurs_in at h1,

    unfold replace_free_aux,
    unfold admits_aux,
    exact P_ih h1 binders,
  },
  case formula.imp_ : P Q P_ih Q_ih binders
  {
    unfold occurs_in at h1,
    push_neg at h1,
    cases h1,

    unfold replace_free_aux,
    unfold admits_aux,
    split,
    {
      exact P_ih h1_left binders,
    },
    {
      exact Q_ih h1_right binders,
    }
  },
  case formula.forall_ : x P P_ih binders
  {
    unfold occurs_in at h1,
    push_neg at h1,
    cases h1,

    unfold replace_free_aux,
    unfold admits_aux,
    apply P_ih,
    exact h1_right,
  },
end


lemma replace_free_admits
  (P : formula)
  (v t : variable_)
  (h1 : ¬ occurs_in t P) :
  admits t v (replace_free v t P) :=
begin
  unfold replace_free,
  unfold admits,
  apply replace_free_aux_admits_aux,
  exact h1,
end


example
  (P : formula)
  (v u : variable_)
  (S T : finset variable_)
  (h1 : admits_aux v u (S ∪ T) P)
  (h2 : v ∉ T) :
  admits_aux v u S P :=
begin
  induction P generalizing S,
  case formula.pred_ : name args S h1
  {
    unfold admits_aux at h1,
    simp only [finset.mem_union, and_imp] at h1,

    unfold admits_aux,
    intros a1 a2,
    cases a1,
    apply h1 a1_left,
    {
      push_neg,
      split,
      {
        exact a1_right,
      },
      {
        exact h2,
      }
    },
    {
      apply or.intro_left,
      exact a2,
    }
  },
  case formula.not_ : P P_ih S h1
  {
    unfold admits_aux at h1,

    unfold admits_aux,
    exact P_ih S h1,
  },
  case formula.imp_ : P Q P_ih Q_ih S h1
  {
    unfold admits_aux at h1,
    cases h1,

    unfold admits_aux,
    split,
    {
      exact P_ih S h1_left,
    },
    {
      exact Q_ih S h1_right,
    },
  },
  case formula.forall_ : x P P_ih S h1
  {
    unfold admits_aux at h1,
    simp only [finset.union_right_comm S T {x}] at h1,

    unfold admits_aux,
    apply P_ih,
    exact h1,
  },
end


example
  (P : formula)
  (v u : variable_)
  (S T : finset variable_)
  (h1 : admits_aux v u S P)
  (h2 : u ∉ T) :
  admits_aux v u (S ∪ T) P :=
begin
  induction P generalizing S,
  case formula.pred_ : name args S h1
  {
    unfold admits_aux at h1,
    simp only [and_imp] at h1,

    unfold admits_aux,
    simp only [finset.mem_union, and_imp],
    push_neg,
    intros a1 a2,
    cases a2,
    split,
    {
      exact h1 a1 a2_left,
    },
    {
      exact h2,
    },
  },
  case formula.not_ : P P_ih S h1
  {
    unfold admits_aux at h1,

    unfold admits_aux,
    exact P_ih S h1,
  },
  case formula.imp_ : P Q P_ih Q_ih S h1
  {
    unfold admits_aux at h1,
    cases h1,

    unfold admits_aux,
    split,
    {
      exact P_ih S h1_left,
    },
    {
      exact Q_ih S h1_right,
    },
  },
  case formula.forall_ : x P P_ih S h1
  {
    unfold admits_aux at h1,

    unfold admits_aux,
    simp only [finset.union_right_comm S T {x}],
    apply P_ih,
    exact h1,
  },
end


def fast_admits_aux (v u : variable_) : finset variable_ → formula → Prop
| binders (pred_ name args) :=
    v ∈ args → -- if there is a free occurrence of v in P
    u ∉ binders -- then it does not become a bound occurrence of u in P(u/v)
| binders (not_ P) := fast_admits_aux binders P
| binders (imp_ P Q) := fast_admits_aux binders P ∧ fast_admits_aux binders Q
| binders (forall_ x P) := v = x ∨ fast_admits_aux (binders ∪ {x}) P

def fast_admits (v u : variable_) (P : formula) : Prop :=
  fast_admits_aux v u ∅ P


lemma fast_admits_aux_del_binders
  (P : formula)
  (v u : variable_)
  (S T : finset variable_)
  (h1 : fast_admits_aux v u (S ∪ T) P) :
  fast_admits_aux v u S P :=
begin
  induction P generalizing S,
  case formula.pred_ : name args S h1
  {
    unfold fast_admits_aux at h1,
    simp only [finset.mem_union] at h1,
    push_neg at h1,

    unfold fast_admits_aux,
    intros a1,
    specialize h1 a1,
    cases h1,
    exact h1_left,
  },
  case formula.not_ : P P_ih S h1
  {
    unfold fast_admits_aux at h1,

    unfold fast_admits_aux,
    exact P_ih S h1,
  },
  case formula.imp_ : P Q P_ih Q_ih S h1
  {
    unfold fast_admits_aux at h1,
    cases h1,

    unfold fast_admits_aux,
    split,
    {
      exact P_ih S h1_left,
    },
    {
      exact Q_ih S h1_right,
    }
  },
  case formula.forall_ : x P P_ih S h1
  {
    unfold fast_admits_aux at h1,
    simp only [finset.union_right_comm S T {x}] at h1,

    unfold fast_admits_aux,
    cases h1,
    {
      apply or.intro_left,
      exact h1,
    },
    {
      apply or.intro_right,
      apply P_ih,
      exact h1,
    }
  },
end


lemma fast_admits_aux_mem_free
  (P : formula)
  (v u : variable_)
  (binders : finset variable_)
  (h1 : fast_admits_aux v u binders P)
  (h2 : v ∈ P.free_var_set) :
  u ∉ binders :=
begin
  induction P generalizing binders,
  case formula.pred_ : name args binders h1
  {
    unfold fast_admits_aux at h1,

    unfold formula.free_var_set at h2,
    simp only [list.mem_to_finset] at h2,
    exact h1 h2,
  },
  case formula.not_ : P P_ih binders h1
  {
    unfold fast_admits_aux at h1,

    unfold formula.free_var_set at h2,

    exact P_ih h2 binders h1,
  },
  case formula.imp_ : P Q P_ih Q_ih binders h1
  {
    unfold fast_admits_aux at h1,
    cases h1,

    unfold formula.free_var_set at h2,
    simp only [finset.mem_union] at h2,

    cases h2,
    {
      exact P_ih h2 binders h1_left,
    },
    {
      exact Q_ih h2 binders h1_right,
    }
  },
  case formula.forall_ : x P P_ih binders h1
  {
    unfold fast_admits_aux at h1,

    unfold formula.free_var_set at h2,
    simp only [finset.mem_sdiff, finset.mem_singleton] at h2,
    cases h2,

    apply P_ih h2_left,
    {
      cases h1,
      {
        contradiction,
      },
      {
        apply fast_admits_aux_del_binders P v u binders {x} h1,
      }
    }
  },
end


lemma admits_aux_imp_fast_admits_aux
  (P : formula)
  (v u : variable_)
  (binders : finset variable_)
  (h1 : admits_aux v u binders P)
  (h2 : v ∉ binders) :
  fast_admits_aux v u binders P :=
begin
  induction P generalizing binders,
  case formula.pred_ : name args binders h1 h2
  {
    unfold admits_aux at h1,

    unfold fast_admits_aux,
    intros a1,
    apply h1,
    split,
    {
      exact a1,
    },
    {
      exact h2,
    },
  },
  case formula.not_ : P P_ih binders h1 h2
  {
    unfold admits_aux at h1,

    unfold fast_admits_aux,
    exact P_ih binders h1 h2,
  },
  case formula.imp_ : P Q P_ih Q_ih binders h1 h2
  {
    unfold admits_aux at h1,
    cases h1,

    unfold fast_admits_aux,
    split,
    {
      exact P_ih binders h1_left h2,
    },
    {
      exact Q_ih binders h1_right h2,
    }
  },
  case formula.forall_ : x P P_ih binders h1 h2
  {
    unfold admits_aux at h1,

    unfold fast_admits_aux,
    by_cases c1 : v = x,
    {
      apply or.intro_left,
      exact c1,
    },
    {
      apply or.intro_right,
      apply P_ih,
      {
        exact h1,
      },
      {
        simp only [finset.mem_union, finset.mem_singleton],
        push_neg,
        split,
        {
          exact h2,
        },
        {
          exact c1,
        }
      }
    }
  },
end


lemma fast_admits_aux_imp_admits_aux
  (P : formula)
  (v u : variable_)
  (binders : finset variable_)
  (h1 : v ∈ binders ∨ fast_admits_aux v u binders P) :
  admits_aux v u binders P :=
begin
  induction P generalizing binders,
  case formula.pred_ : name args binders h1
  {
    unfold fast_admits_aux at h1,
    unfold admits_aux,
    intros a1,
    cases a1,
    cases h1,
    {
      contradiction,
    },
    {
      exact h1 a1_left,
    }
  },
  case formula.not_ : P P_ih binders h1
  {
    unfold fast_admits_aux at h1,

    unfold admits_aux,
    exact P_ih binders h1,
  },
  case formula.imp_ : P Q P_ih Q_ih binders h1
  {
    unfold fast_admits_aux at h1,
    unfold admits_aux,
    split,
    {
      apply P_ih,
      cases h1,
      {
        apply or.intro_left,
        exact h1,
      },
      {
        cases h1,
        apply or.intro_right,
        exact h1_left,
      }
    },
    {
      apply Q_ih,
      cases h1,
      {
        apply or.intro_left,
        exact h1,
      },
      {
        cases h1,
        apply or.intro_right,
        exact h1_right,
      }
    }
  },
  case formula.forall_ : x P P_ih binders h1
  {
    unfold fast_admits_aux at h1,

    unfold admits_aux,
    apply P_ih,
    cases h1,
    {
      apply or.intro_left,
      simp only [finset.mem_union, finset.mem_singleton],
      apply or.intro_left,
      exact h1,
    },
    {
      cases h1,
      {
        apply or.intro_left,
        simp only [finset.mem_union, finset.mem_singleton],
        apply or.intro_right,
        exact h1,
      },
      {
        apply or.intro_right,
        exact h1,
      }
    }
  },
end


example
  (P : formula)
  (v u : variable_) :
  admits v u P ↔ fast_admits v u P :=
begin
  unfold admits,
  unfold fast_admits,
  split,
  {
    intros a1,
    apply admits_aux_imp_fast_admits_aux,
    {
      exact a1,
    },
    {
      simp only [finset.not_mem_empty, not_false_iff],
    }
  },
  {
    intros a1,
    apply fast_admits_aux_imp_admits_aux,
    simp only [finset.not_mem_empty, false_or],
    exact a1,
  }
end


lemma not_mem_free_imp_fast_admits_aux
  (P : formula)
  (v u : variable_)
  (binders : finset variable_)
  (h1 : v ∉ P.free_var_set) :
  fast_admits_aux v u binders P :=
begin
  induction P generalizing binders,
  case formula.pred_ : name args
  {
    unfold formula.free_var_set at h1,

    unfold fast_admits_aux,
    intros a1,
    simp only [list.mem_to_finset] at h1,
    contradiction,
  },
  case formula.not_ : P P_ih
  {
    unfold formula.free_var_set at h1,

    unfold fast_admits_aux,
    exact P_ih h1 binders,
  },
  case formula.imp_ : P Q P_ih Q_ih
  {
    unfold formula.free_var_set at h1,
    simp only [finset.mem_union] at h1,
    push_neg at h1,
    cases h1,

    unfold fast_admits_aux,
    split,
    {
      exact P_ih h1_left binders,
    },
    {
      exact Q_ih h1_right binders,
    }
  },
  case formula.forall_ : x P P_ih
  {
    unfold formula.free_var_set at h1,
    simp only [finset.mem_sdiff, finset.mem_singleton, not_and, not_not] at h1,

    unfold fast_admits_aux,
    by_cases c1 : v ∈ P.free_var_set,
    {
      apply or.intro_left,
      exact h1 c1,
    },
    {
      apply or.intro_right,
      apply P_ih c1,
    }
  },
end


lemma not_mem_free_imp_fast_admits
  (P : formula)
  (v u : variable_)
  (h1 : v ∉ P.free_var_set) :
  fast_admits v u P :=
begin
  unfold fast_admits,
  apply not_mem_free_imp_fast_admits_aux,
  exact h1,
end


@[derive [inhabited, decidable_eq]]
inductive bool_formula : Type
| pred_ : pred_name_ → list bool → bool_formula
| not_ : bool_formula → bool_formula
| imp_ : bool_formula → bool_formula → bool_formula
| forall_ : bool → bool_formula → bool_formula


def to_is_bound_aux : finset variable_ → formula → bool_formula
| binders (pred_ name args) := bool_formula.pred_ name (args.map (fun (v : variable_), v ∈ binders))
| binders (not_ P) := bool_formula.not_ (to_is_bound_aux binders P)
| binders (imp_ P Q) := bool_formula.imp_ (to_is_bound_aux binders P) (to_is_bound_aux binders Q)
| binders (forall_ x P) := bool_formula.forall_ true (to_is_bound_aux (binders ∪ {x}) P)

def to_is_bound (P : formula) : bool_formula :=
  to_is_bound_aux ∅ P


lemma fast_admits_aux_imp_free_and_bound_unchanged
  (P : formula)
  (v u : variable_)
  (binders : finset variable_)
  (h1 : v ∉ binders)
  (h2 : fast_admits_aux v u binders P) :
  to_is_bound_aux binders P = to_is_bound_aux binders (fast_replace_free v u P) :=
begin
  induction P generalizing binders,
  case formula.pred_ : name args binders h1 h2
  {
    induction args,
    case list.nil
    {
      unfold fast_replace_free,
      simp only [list.map_nil],
    },
    case list.cons : args_hd args_tl args_ih
    {
      unfold fast_admits_aux at h2,
      simp only [list.mem_cons_iff] at h2,

      unfold fast_admits_aux at args_ih,
      unfold fast_replace_free at args_ih,
      unfold to_is_bound_aux at args_ih,
      simp only [list.map_map, eq_self_iff_true, true_and] at args_ih,

      unfold fast_replace_free,
      unfold to_is_bound_aux,
      simp only [list.map, list.map_map, eq_self_iff_true, bool.to_bool_eq, true_and],

      split,
      {
        unfold replace,
        split_ifs,
        {
          subst h,
          simp only [eq_self_iff_true, true_or, forall_true_left] at h2,
          split,
          {
            intros a1,
            contradiction,
          },
          {
            intros a1,
            contradiction,
          }
        },
        {
          refl,
        }
      },
      {
        apply args_ih,
        intros a1,
        apply h2,
        apply or.intro_right,
        exact a1,
      }
    },
  },
  case formula.not_ : P P_ih binders h1 h2
  {
    unfold fast_admits_aux at h2,

    unfold fast_replace_free,
    unfold to_is_bound_aux,
    congr' 1,
    exact P_ih binders h1 h2,
  },
  case formula.imp_ : P Q P_ih Q_ih binders h1 h2
  {
    unfold fast_admits_aux at h2,
    cases h2,

    unfold fast_replace_free,
    unfold to_is_bound_aux,
    congr' 1,
    {
      exact P_ih binders h1 h2_left,
    },
    {
      exact Q_ih binders h1 h2_right,
    }
  },
  case formula.forall_ : x P P_ih binders h1 h2
  {
    unfold fast_admits_aux at h2,

    unfold fast_replace_free,
    split_ifs,
    {
      refl,
    },
    {
      unfold to_is_bound_aux,
      simp only [eq_self_iff_true, true_and],
      apply P_ih,
      {
        simp only [finset.mem_union, finset.mem_singleton],
        push_neg,
        split,
        {
          exact h1,
        },
        {
          exact h,
        }
      },
      {
        cases h2,
        {
          contradiction,
        },
        {
          exact h2,
        }
      }
    }
  },
end


lemma free_and_bound_unchanged_imp_fast_admits_aux
  (P : formula)
  (v u : variable_)
  (binders : finset variable_)
  (h1 : v ∉ binders)
  (h2 : to_is_bound_aux binders P = to_is_bound_aux binders (fast_replace_free v u P)) :
  fast_admits_aux v u binders P :=
begin
  induction P generalizing binders,
  case formula.pred_ : name args binders h1 h2
  {
    induction args,
    case list.nil
    {
      unfold fast_admits_aux,
      simp only [list.not_mem_nil, is_empty.forall_iff],
    },
    case list.cons : args_hd args_tl args_ih
    {
      unfold fast_replace_free at h2,
      unfold to_is_bound_aux at h2,
      simp only [list.map, list.map_map, eq_self_iff_true, bool.to_bool_eq, true_and] at h2,
      cases h2,

      unfold fast_admits_aux at args_ih,
      unfold fast_replace_free at args_ih,
      unfold to_is_bound_aux at args_ih,
      simp only [list.map_map, eq_self_iff_true, true_and] at args_ih,

      specialize args_ih h2_right,

      unfold replace at h2_left,

      unfold fast_admits_aux,
      simp only [list.mem_cons_iff],
      intros a1,
      cases a1,
      {
        subst a1,
        simp only [eq_self_iff_true, if_true] at h2_left,
        cases h2_left,
        by_contradiction contra,
        apply h1,
        apply h2_left_mpr,
        exact contra,
      },
      {
        apply args_ih,
        exact a1,
      }
    },
  },
  case formula.not_ : P P_ih binders h1 h2
  {
    unfold fast_replace_free at h2,
    unfold to_is_bound_aux at h2,
    simp only at h2,

    unfold fast_admits_aux,
    exact P_ih binders h1 h2,
  },
  case formula.imp_ : P Q P_ih Q_ih binders h1 h2
  {
    unfold fast_replace_free at h2,
    unfold to_is_bound_aux at h2,
    simp only at h2,
    cases h2,

    unfold fast_admits_aux,
    split,
    {
      exact P_ih binders h1 h2_left,
    },
    {
      exact Q_ih binders h1 h2_right,
    }
  },
  case formula.forall_ : x P P_ih binders h1 h2
  {
    unfold fast_replace_free at h2,

    unfold fast_admits_aux,
    split_ifs at h2,
    {
      apply or.intro_left,
      exact h,
    },
    {
      apply or.intro_right,
      apply P_ih,
      {
        simp only [finset.mem_union, finset.mem_singleton],
        push_neg,
        split,
        {
          exact h1,
        },
        {
          exact h,
        }
      },
      {
        unfold to_is_bound_aux at h2,
        simp only [eq_self_iff_true, true_and] at h2,
        exact h2,
      }
    }
  },
end


/-
P admits u for v if and only if every free occurrence of a variable in P remains free in P(u/v) and every bound occurrence of a variable in P remains bound in P(u/v).
-/
example
  (P : formula)
  (v u : variable_) :
  fast_admits v u P ↔ to_is_bound P = to_is_bound (fast_replace_free v u P) :=
begin
  unfold fast_admits,
  unfold to_is_bound,
  split,
  {
    apply fast_admits_aux_imp_free_and_bound_unchanged,
    simp only [finset.not_mem_empty, not_false_iff],
  },
  {
    apply free_and_bound_unchanged_imp_fast_admits_aux,
    simp only [finset.not_mem_empty, not_false_iff],
  }
end


inductive is_prop_sub : formula → variable_ → variable_ → formula → Prop
| pred_
  (name : pred_name_) (args : list variable_)
  (v t : variable_) :
  is_prop_sub (pred_ name args) v t (pred_ name (args.map (replace v t)))

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
  (v t : variable_)
  (P' : formula) :
  v = x →
  is_prop_sub (forall_ x P) v t (forall_ x P)

| forall_diff_nel_
  (x : variable_) (P : formula)
  (v t : variable_)
  (P' : formula) :
  ¬ v = x →
  v ∉ (forall_ x P).free_var_set →
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
  case formula.pred_ : name args binders h1
  {
    unfold fast_replace_free,
    apply is_prop_sub.pred_,
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
      apply is_prop_sub.forall_same_ x P v u P h1,
    },
    {
      unfold fast_replace_free,
      split_ifs,
      {
        apply is_prop_sub.forall_same_ x P v u P h,
      },
      {
        by_cases c1 : v ∈ (forall_ x P).free_var_set,
        {
          apply is_prop_sub.forall_diff_,
          {
            exact h,
          },
          {
            unfold formula.free_var_set at c1,
            simp only [finset.mem_sdiff, finset.mem_singleton] at c1,

            cases c1,
            have s1 : u ∉ binders ∪ {x},
            apply fast_admits_aux_mem_free P v u,
            {
              exact h1,
            },
            {
              exact c1_left,
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
  case is_prop_sub.pred_ : h1_1_name h1_1_args h1_1_v h1_1_t binders h2
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
  case is_prop_sub.forall_same_ : h1_1_x h1_1_P h1_1_v h1_1_t h1_1_P' h1_1_1 binders h2
  {
    unfold fast_admits_aux,
    apply or.intro_left,
    exact h1_1_1,
  },
  case is_prop_sub.forall_diff_nel_ : h1_1_x h1_1_P h1_1_v h1_1_t h1_1_P' h1_1_1 h1_1_2 h1_1_3 h1_1_ih binders h2
  {
    unfold formula.free_var_set at h1_1_2,
    simp only [finset.mem_sdiff, finset.mem_singleton, not_and, not_not] at h1_1_2,

    unfold fast_admits_aux,

    apply or.intro_right,
    apply not_mem_free_imp_fast_admits_aux,
    intros contra,
    apply h1_1_1,
    apply h1_1_2,
    exact contra,
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
  case is_prop_sub.pred_ : h1_name h1_args h1_v h1_t
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
  case is_prop_sub.forall_same_ : h1_x h1_P h1_v h1_t h1_P' h1_1
  {
    apply fast_replace_free_not_mem_free,
    unfold formula.free_var_set,
    simp only [finset.mem_sdiff, finset.mem_singleton, not_and, not_not],
    intros a1,
    exact h1_1,
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


def function.update_ite
  {α β : Type}
  [decidable_eq α]
  (f : α → β)
  (a' : α) (b : β) (a : α) :=
  if a' = a then b else f a


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


/-
  The simultaneous replacement of the free variables in a formula.
-/
def fast_simult_replace_free : (variable_ → variable_) → formula → formula
| σ (pred_ name args) := pred_ name (args.map σ)
| σ (not_ P) := not_ (fast_simult_replace_free σ P)
| σ (imp_ P Q) := imp_ (fast_simult_replace_free σ P) (fast_simult_replace_free σ Q)
| σ (forall_ x P) := forall_ x (fast_simult_replace_free (function.update_ite σ x x) P)


lemma function.update_id
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
  case formula.pred_ : name args
  {
    unfold fast_simult_replace_free,
    simp only [list.map_id, eq_self_iff_true, and_self],
  },
  case formula.not_ : P P_ih
  {
    unfold fast_simult_replace_free,
    congr,
    exact P_ih,
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
    simp only [function.update_id],
    exact P_ih,
  },
end


example
  (P : formula)
  (v t : variable_) :
  fast_simult_replace_free (function.update_ite id v t) P = fast_replace_free v t P :=
begin
  induction P,
  case formula.pred_ : name args
  {
    unfold fast_simult_replace_free,
    unfold fast_replace_free,
    simp only [eq_self_iff_true, true_and],
    apply list.map_congr,
    intros x a1,
    unfold replace,
    unfold function.update_ite,
    split_ifs,
    {
      refl,
    },
    {
      simp only [id.def],
    },
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

      simp only [function.update_id],
      apply fast_simult_replace_free_id,
    },
    {
      have s1 : (function.update_ite (function.update_ite (id : variable_ → variable_) v t) x x) = function.update_ite id v t,
      funext,
      unfold function.update_ite,
      split_ifs,
      {
        subst h_1,
        contradiction,
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


def simult_admits_aux (σ : variable_ → variable_) : finset variable_ → formula → Prop
| binders (pred_ name args) :=
    ∀ (v : variable_), v ∈ args ∧ v ∉ binders → σ v ∉ binders
| binders (not_ P) := simult_admits_aux binders P
| binders (imp_ P Q) := simult_admits_aux binders P ∧ simult_admits_aux binders Q
| binders (forall_ x P) := simult_admits_aux (binders ∪ {x}) P


def simult_admits (σ : variable_ → variable_) (P : formula) : Prop :=
  simult_admits_aux σ ∅ P


#lint
