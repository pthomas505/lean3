import .replace_free

import data.finset


set_option pp.parens true


namespace fol

open formula


/-
[margaris]
pg. 48

If $v$ and $u$ are variables and $P$ is a formula, then $P$ admits $u$ for $v$ if and only if there is no free occurrence of $v$ in $P$ that becomes a bound occurrence of $u$ in $P(u/v)$. If $t$ is a term, then $P$ admits $t$ for $v$ if and only if $P$ admits for $v$ every variable in $t$.
-/

/--
  Helper function for admits.
-/
@[derive decidable]
def admits_aux (v u : var_name) : finset var_name → formula → bool
| _ true_ := true
| binders (pred_ name args) :=
    (v ∈ args ∧ v ∉ binders) → -- if there is a free occurrence of v in P
    u ∉ binders -- then it does not become a bound occurrence of u in P(u/v)
| binders (not_ P) := admits_aux binders P
| binders (imp_ P Q) := admits_aux binders P ∧ admits_aux binders Q
| binders (forall_ x P) := admits_aux (binders ∪ {x}) P

/--
  admits v u P := True if and only if there is no free occurrence of the variable v in the formula P that becomes a bound occurrence of the variable u in P(u/v).

  P admits u for v

  v → u in P
-/
def admits (v u : var_name) (P : formula) : Prop :=
  admits_aux v u ∅ P


/--
  Helper function for fast_admits.
-/
@[derive decidable]
def fast_admits_aux (v u : var_name) : finset var_name → formula → bool
| _ true_ := true
| binders (pred_ name args) :=
    v ∈ args → -- if there is a free occurrence of v in P
    u ∉ binders -- then it does not become a bound occurrence of u in P(u/v)
| binders (not_ P) := fast_admits_aux binders P
| binders (imp_ P Q) := fast_admits_aux binders P ∧ fast_admits_aux binders Q
| binders (forall_ x P) := v = x ∨ fast_admits_aux (binders ∪ {x}) P

/--
  fast_admits v u P := True if and only if there is no free occurrence of the variable v in the formula P that becomes a bound occurrence of the variable u in P(u/v).

  P admits u for v

  v → u in P

  This is a more efficient version of admits.
-/
@[derive decidable]
def fast_admits (v u : var_name) (P : formula) : bool :=
  fast_admits_aux v u ∅ P


/--
  Used to label each occurrence of a variable in a formula as free or bound.
-/
@[derive [inhabited, decidable_eq]]
inductive bool_formula : Type
| true_ : bool_formula
| pred_ : pred_name → list bool → bool_formula
| not_ : bool_formula → bool_formula
| imp_ : bool_formula → bool_formula → bool_formula
| forall_ : bool → bool_formula → bool_formula


/--
  Helper function for to_is_bound.
-/
def to_is_bound_aux : finset var_name → formula → bool_formula
| _ true_ := bool_formula.true_
| binders (pred_ name args) := bool_formula.pred_ name (args.map (fun (v : var_name), v ∈ binders))
| binders (not_ P) := bool_formula.not_ (to_is_bound_aux binders P)
| binders (imp_ P Q) := bool_formula.imp_ (to_is_bound_aux binders P) (to_is_bound_aux binders Q)
| binders (forall_ x P) := bool_formula.forall_ true (to_is_bound_aux (binders ∪ {x}) P)


/--
  Creates a bool_formula from a formula. Each bound occurence of a variable in the formula is mapped to true in the bool formula. Each free occurence of a variable in the formula is mapped to false in the bool formula.
-/
def to_is_bound (P : formula) : bool_formula :=
  to_is_bound_aux ∅ P


-- admits ↔ fast_admits

lemma admits_aux_imp_fast_admits_aux
  (P : formula)
  (v u : var_name)
  (binders : finset var_name)
  (h1 : v ∉ binders)
  (h2 : admits_aux v u binders P) :
  fast_admits_aux v u binders P :=
begin
  induction P generalizing binders,
  case formula.true_ : binders h1 h2
  {
    unfold fast_admits_aux,
    simp only [to_bool_true_eq_tt, coe_sort_tt],
  },
  case fol.formula.pred_ : X xs binders h1 h2
  {
    unfold admits_aux at h2,
    squeeze_simp at h2,

    unfold fast_admits_aux,
    squeeze_simp,
    intros a1,
    exact h2 a1 h1,
  },
  case fol.formula.not_ : P P_ih binders h1 h2
  {
    unfold admits_aux at h2,

    unfold fast_admits_aux,
    exact P_ih binders h1 h2,
  },
  case fol.formula.imp_ : P Q P_ih Q_ih binders h1 h2
  {
    unfold admits_aux at h2,
    squeeze_simp at h2,
    cases h2,

    unfold fast_admits_aux,
    squeeze_simp,
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
    unfold admits_aux at h2,

    unfold fast_admits_aux,
    squeeze_simp,
    by_cases c1 : v = x,
    {
      left,
      exact c1,
    },
    {
      right,
      apply P_ih,
      {
        simp only [finset.mem_union, finset.mem_singleton],
        tauto,
      },
      {
        exact h2,
      },
    }
  },
end


lemma mem_binders_imp_admits_aux
  (P : formula)
  (v u : var_name)
  (binders : finset var_name)
  (h1 : v ∈ binders) :
  admits_aux v u binders P :=
begin
  induction P generalizing binders,
  case formula.true_ : binders h1
  {
    unfold admits_aux,
    squeeze_simp,
  },
  case fol.formula.pred_ : X xs binders h1
  {
    unfold admits_aux,
    squeeze_simp,
    intros a1 a2,
    contradiction,
  },
  case fol.formula.not_ : P P_ih binders h1
  {
    unfold admits_aux,
    exact P_ih binders h1,
  },
  case fol.formula.imp_ : P Q P_ih Q_ih binders h1
  {
    unfold admits_aux,
    squeeze_simp,
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
    unfold admits_aux,
    apply P_ih,
    simp only [finset.mem_union, finset.mem_singleton],
    left,
    exact h1,
  },
end


lemma fast_admits_aux_imp_admits_aux
  (P : formula)
  (v u : var_name)
  (binders : finset var_name)
  (h1 : fast_admits_aux v u binders P) :
  admits_aux v u binders P :=
begin
  induction P generalizing binders,
  case formula.true_ : binders h1
  {
    unfold admits_aux,
  },
  case [formula.pred_, formula.not_, formula.imp_]
  {
    all_goals
    {
      unfold fast_admits_aux at h1,

      unfold admits_aux,
      tauto,
    }
  },
  case formula.forall_ : x P P_ih binders h1
  {
    unfold fast_admits_aux at h1,

    unfold admits_aux,
    cases h1,
    {
      apply mem_binders_imp_admits_aux,
      subst h1,
      simp only [finset.mem_union, finset.mem_singleton, eq_self_iff_true, or_true],
    },
    {
      apply P_ih,
      exact h1,
    }
  },
end


theorem admits_iff_fast_admits
  (P : formula)
  (v u : var_name) :
  admits v u P ↔ fast_admits v u P :=
begin
  unfold admits,
  unfold fast_admits,
  split,
  {
    apply admits_aux_imp_fast_admits_aux,
    simp only [finset.not_mem_empty, not_false_iff],
  },
  {
    apply fast_admits_aux_imp_admits_aux,
  }
end


-- fast_admits


lemma fast_admits_aux_self
  (P : formula)
  (v : var_name)
  (binders : finset var_name)
  (h1 : v ∉ binders) :
  fast_admits_aux v v binders P :=
begin
  induction P generalizing binders,
  case formula.true_ : binders h1
  {
    unfold fast_admits_aux,
  },
  case [formula.pred_, formula.not_, formula.imp_]
  {
    all_goals
    {
      unfold fast_admits_aux,
      tauto,
    }
  },
  case formula.forall_ : x P P_ih binders h1
  {
    unfold fast_admits_aux,
    by_cases c1 : v = x,
    {
      tauto,
    },
    {
      right,
      apply P_ih,
      simp only [finset.mem_union, finset.mem_singleton],
      tauto,
    }
  },
end


theorem fast_admits_self
  (P : formula)
  (v : var_name) :
  fast_admits v v P :=
begin
  unfold fast_admits,
  apply fast_admits_aux_self,
  simp only [finset.not_mem_empty, not_false_iff],
end

--

lemma not_is_free_in_imp_fast_admits_aux
  (P : formula)
  (v u : var_name)
  (binders : finset var_name)
  (h1 : ¬ is_free_in v P) :
  fast_admits_aux v u binders P :=
begin
  induction P generalizing binders,
  case formula.true_ : binders
  {
    unfold fast_admits_aux,
  },
  case formula.pred_ : name args
  {
    unfold is_free_in at h1,
    simp only [list.mem_to_finset] at h1,

    unfold fast_admits_aux,
    tauto,
  },
  case [formula.not_, formula.imp_, formula.forall_]
  {
    all_goals
    {
      unfold is_free_in at h1,

      unfold fast_admits_aux,
      tauto,
    }
  },
end


theorem not_is_free_in_imp_fast_admits
  (P : formula)
  (v u : var_name)
  (h1 : ¬ is_free_in v P) :
  fast_admits v u P :=
begin
  unfold fast_admits,
  apply not_is_free_in_imp_fast_admits_aux,
  exact h1,
end

--

lemma not_is_bound_in_imp_fast_admits_aux
  (P : formula)
  (v u : var_name)
  (binders : finset var_name)
  (h1 : ¬ is_bound_in u P)
  (h2 : u ∉ binders) :
  fast_admits_aux v u binders P :=
begin
  induction P generalizing binders,
  case formula.true_ : binders h2
  {
    unfold fast_admits_aux,
  },
  case formula.pred_ : name args binders h2
  {
    unfold fast_admits_aux,
    tauto,
  },
  case formula.not_ : P P_ih binders h2
  {
    unfold is_bound_in at h1,

    unfold fast_admits_aux,
    tauto,
  },
  case formula.imp_ : P Q P_ih Q_ih binders h2
  {
    unfold is_bound_in at h1,

    unfold fast_admits_aux,
    tauto,
  },
  case formula.forall_ : x P P_ih binders h2
  {
    unfold is_bound_in at h1,
    push_neg at h1,
    cases h1,

    unfold fast_admits_aux,
    right,
    apply P_ih,
    {
      exact h1_right,
    },
    {
      simp only [finset.mem_union, finset.mem_singleton],
      tauto,
    }
  },
end

theorem not_is_bound_in_imp_fast_admits
  (P : formula)
  (v u : var_name)
  (h1 : ¬ is_bound_in u P) :
  fast_admits v u P :=
begin
  unfold fast_admits,
  apply not_is_bound_in_imp_fast_admits_aux,
  {
    exact h1,
  },
  {
    simp only [finset.not_mem_empty, not_false_iff],
  }
end

--

lemma fast_replace_free_aux_fast_admits_aux
  (P : formula)
  (v t : var_name)
  (binders : finset var_name)
  (h1 : ¬ occurs_in t P)
  (h2 : v ∉ binders) :
  fast_admits_aux t v binders (fast_replace_free v t P) :=
begin
  induction P generalizing binders,
  case formula.true_ : binders h2
  {
    unfold fast_replace_free,
  },
  case formula.pred_ : name args binders h2
  {
    unfold fast_replace_free,
    unfold fast_admits_aux,
    tauto,
  },
  case formula.not_ : P P_ih binders h2
  {
    unfold occurs_in at h1,

    unfold fast_replace_free,
    unfold fast_admits_aux,
    tauto,
  },
  case formula.imp_ : P Q P_ih Q_ih binders h2
  {
    unfold occurs_in at h1,

    unfold fast_replace_free,
    unfold fast_admits_aux,
    tauto,
  },
  case formula.forall_ : x P P_ih binders h2
  {
    unfold occurs_in at h1,
    push_neg at h1,
    cases h1,

    unfold fast_replace_free,
    split_ifs,
    {
      unfold fast_admits_aux,
      subst h,
      right,
      apply not_is_free_in_imp_fast_admits_aux,
      intros contra,
      apply h1_right,
      apply is_free_in_imp_occurs_in,
      exact contra,
    },
    {
      unfold fast_admits_aux,
      right,
      apply P_ih h1_right,
      simp only [finset.mem_union, finset.mem_singleton],
      tauto,
    },
  },
end


lemma fast_replace_free_fast_admits
  (P : formula)
  (v t : var_name)
  (h1 : ¬ occurs_in t P) :
  fast_admits t v (fast_replace_free v t P) :=
begin
  unfold fast_admits,
  apply fast_replace_free_aux_fast_admits_aux P v t ∅ h1,
  simp only [finset.not_mem_empty, not_false_iff],
end

--

lemma replace_free_aux_fast_admits_aux
  (P : formula)
  (v t : var_name)
  (binders : finset var_name)
  (h1 : ¬ occurs_in t P) :
  fast_admits_aux t v binders (replace_free_aux v t binders P) :=
begin
  induction P generalizing binders,
  case formula.true_ : binders
  {
    unfold replace_free_aux,
  },
  case formula.pred_ : name args binders
  {
    unfold occurs_in at h1,
    simp only [list.mem_to_finset] at h1,

    unfold replace_free_aux,
    unfold fast_admits_aux,
    simp only [list.mem_map, forall_exists_index],
    intros x a1,
    cases a1,

    by_cases c1 : x = v ∧ x ∉ binders,
    {
      cases c1,
      subst c1_left,
      exact c1_right,
    },
    {
      simp only [if_neg c1] at a1_right,
      subst a1_right,
      contradiction,
    }
  },
  case formula.not_ : P P_ih binders
  {
    unfold occurs_in at h1,

    unfold replace_free_aux,
    unfold fast_admits_aux,
    tauto,
  },
  case formula.imp_ : P Q P_ih Q_ih binders
  {
    unfold occurs_in at h1,

    unfold replace_free_aux,
    unfold fast_admits_aux,
    tauto,
  },
  case formula.forall_ : x P P_ih binders
  {
    unfold occurs_in at h1,

    unfold replace_free_aux,
    unfold fast_admits_aux,
    tauto,
  },
end


lemma replace_free_fast_admits
  (P : formula)
  (v t : var_name)
  (h1 : ¬ occurs_in t P) :
  fast_admits t v (replace_free v t P) :=
begin
  unfold replace_free,
  unfold fast_admits,
  apply replace_free_aux_fast_admits_aux,
  exact h1,
end

--

lemma fast_admits_aux_add_binders
  (P : formula)
  (v u : var_name)
  (S T : finset var_name)
  (h1 : fast_admits_aux v u S P)
  (h2 : u ∉ T) :
  fast_admits_aux v u (S ∪ T) P :=
begin
  induction P generalizing S,
  case formula.true_ : S h1
  {
    unfold fast_admits_aux,
  },
  case formula.pred_ : name args S h1
  {
    unfold fast_admits_aux at h1,

    unfold fast_admits_aux,
    simp only [finset.mem_union],
    tauto,
  },
  case formula.not_ : P P_ih S h1
  {
    unfold fast_admits_aux at h1,

    unfold fast_admits_aux,
    tauto,
  },
  case formula.imp_ : P Q P_ih Q_ih S h1
  {
    unfold fast_admits_aux at h1,

    unfold fast_admits_aux,
    tauto,
  },
  case formula.forall_ : x P P_ih S h1
  {
    unfold fast_admits_aux at h1,

    unfold fast_admits_aux,
    cases h1,
    {
      tauto,
    },
    {
      right,
      simp only [finset.union_right_comm S T {x}],
      tauto,
    }
  },
end


lemma fast_admits_aux_del_binders
  (P : formula)
  (v u : var_name)
  (S T : finset var_name)
  (h1 : fast_admits_aux v u (S ∪ T) P) :
  fast_admits_aux v u S P :=
begin
  induction P generalizing S,
  case formula.true_ : S h1
  {
    unfold fast_admits_aux,
  },
  case formula.pred_ : name args S h1
  {
    unfold fast_admits_aux at h1,
    simp only [finset.mem_union] at h1,

    unfold fast_admits_aux,
    tauto,
  },
  case formula.not_ : P P_ih S h1
  {
    unfold fast_admits_aux at h1,

    unfold fast_admits_aux,
    tauto,
  },
  case formula.imp_ : P Q P_ih Q_ih S h1
  {
    unfold fast_admits_aux at h1,
    cases h1,

    unfold fast_admits_aux,
    tauto,
  },
  case formula.forall_ : x P P_ih S h1
  {
    unfold fast_admits_aux at h1,
    simp only [finset.union_right_comm S T {x}] at h1,

    unfold fast_admits_aux,
    tauto,
  },
end

--

lemma fast_admits_aux_is_free_in
  (P : formula)
  (v u : var_name)
  (binders : finset var_name)
  (h1 : fast_admits_aux v u binders P)
  (h2 : is_free_in v P) :
  u ∉ binders :=
begin
  induction P generalizing binders,
  case formula.true_ : binders h1
  {
    unfold is_free_in at h2,

    contradiction,
  },
  case formula.pred_ : name args binders h1
  {
    unfold fast_admits_aux at h1,

    unfold is_free_in at h2,
    simp only [list.mem_to_finset] at h2,

    tauto,
  },
  case formula.not_ : P P_ih binders h1
  {
    unfold fast_admits_aux at h1,

    unfold is_free_in at h2,

    exact P_ih h2 binders h1,
  },
  case formula.imp_ : P Q P_ih Q_ih binders h1
  {
    unfold fast_admits_aux at h1,
    cases h1,

    unfold is_free_in at h2,

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

    unfold is_free_in at h2,
    cases h2,

    apply P_ih h2_right,
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


lemma fast_admits_aux_mem_binders
  (P : formula)
  (v u : var_name)
  (binders : finset var_name)
  (h1 : fast_admits_aux v u binders P)
  (h2 : u ∈ binders) :
  ¬ is_free_in v P :=
begin
  contrapose! h2,
  exact fast_admits_aux_is_free_in P v u binders h1 h2,
end


--


lemma fast_admits_aux_imp_free_and_bound_unchanged
  (P : formula)
  (v u : var_name)
  (binders : finset var_name)
  (h1 : v ∉ binders)
  (h2 : fast_admits_aux v u binders P) :
  to_is_bound_aux binders P = to_is_bound_aux binders (fast_replace_free v u P) :=
begin
  induction P generalizing binders,
  case formula.true_ : binders h1 h2
  {
    refl,
  },
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
        split_ifs,
        {
          subst h,
          tauto,
        },
        {
          refl,
        }
      },
      {
        tauto,
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
        tauto,
      },
      {
        tauto,
      }
    }
  },
end


lemma free_and_bound_unchanged_imp_fast_admits_aux
  (P : formula)
  (v u : var_name)
  (binders : finset var_name)
  (h1 : v ∉ binders)
  (h2 : to_is_bound_aux binders P = to_is_bound_aux binders (fast_replace_free v u P)) :
  fast_admits_aux v u binders P :=
begin
  induction P generalizing binders,
  case formula.true_ : binders h1 h2
  {
    unfold fast_admits_aux,
  },
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

      unfold fast_admits_aux,
      simp only [list.mem_cons_iff],
      intros a1,
      cases a1,
      {
        subst a1,
        simp only [eq_self_iff_true, if_true] at h2_left,
        tauto,
      },
      {
        tauto,
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
    tauto,
  },
  case formula.forall_ : x P P_ih binders h1 h2
  {
    unfold fast_replace_free at h2,

    unfold fast_admits_aux,
    split_ifs at h2,
    {
      left,
      exact h,
    },
    {
      right,
      apply P_ih,
      {
        simp only [finset.mem_union, finset.mem_singleton],
        tauto,
      },
      {
        unfold to_is_bound_aux at h2,
        simp only [eq_self_iff_true, true_and] at h2,
        exact h2,
      }
    }
  },
end


example
  (P : formula)
  (v u : var_name) :
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


-- admits


lemma admits_aux_self
  (P : formula)
  (v : var_name)
  (binders : finset var_name) :
  admits_aux v v binders P :=
begin
  induction P generalizing binders;
  unfold admits_aux;
  tauto,
end


theorem admits_self
  (P : formula)
  (v : var_name) :
  admits v v P :=
begin
  unfold admits,
  apply admits_aux_self,
end

--

lemma not_is_free_in_imp_admits_aux
  (P : formula)
  (v u : var_name)
  (binders : finset var_name)
  (h1 : ¬ is_free_in v P) :
  admits_aux v u binders P :=
begin
  induction P generalizing binders,
  case formula.true_ : binders
  {
    unfold admits_aux,
  },
  case formula.pred_ : name args binders
  {
    unfold is_free_in at h1,
    simp only [list.mem_to_finset] at h1,

    unfold admits_aux,
    tauto,
  },
  case [formula.not_, formula.imp_]
  {
    all_goals
    {
      unfold is_free_in at h1,

      unfold admits_aux,
      tauto,
    }
  },
  case formula.forall_ : x P P_ih binders
  {
    unfold is_free_in at h1,

    unfold admits_aux,
    by_cases c1 : v = x,
    {
      apply mem_binders_imp_admits_aux,
      simp only [finset.mem_union, finset.mem_singleton],
      tauto,
    },
    {
      tauto,
    },
  },
end


theorem not_is_free_in_imp_admits
  (P : formula)
  (v u : var_name)
  (h1 : ¬ is_free_in v P) :
  admits v u P :=
begin
  unfold admits,
  apply not_is_free_in_imp_admits_aux,
  exact h1,
end

--

lemma not_is_bound_in_imp_admits_aux
  (P : formula)
  (v u : var_name)
  (binders : finset var_name)
  (h1 : ¬ is_bound_in u P)
  (h2 : u ∉ binders) :
  admits_aux v u binders P :=
begin
  induction P generalizing binders,
  case formula.true_ : binders h2
  {
    unfold admits_aux,
  },
  case formula.pred_ : name args binders h2
  {
    unfold admits_aux,
    tauto,
  },
  case formula.not_ : P P_ih binders h2
  {
    unfold is_bound_in at h1,

    unfold admits_aux,
    tauto,
  },
  case formula.imp_ : P Q P_ih Q_ih binders h2
  {
    unfold is_bound_in at h1,

    unfold admits_aux,
    tauto,
  },
  case formula.forall_ : x P P_ih binders h2
  {
    unfold is_bound_in at h1,
    push_neg at h1,
    cases h1,

    unfold admits_aux,
    apply P_ih h1_right,
    simp only [finset.mem_union, finset.mem_singleton],
    tauto,
  },
end


theorem not_is_bound_in_imp_admits
  (P : formula)
  (v u : var_name)
  (h1 : ¬ is_bound_in u P) :
  admits v u P :=
begin
  unfold admits,
  apply not_is_bound_in_imp_admits_aux,
  {
    exact h1,
  },
  {
    simp only [finset.not_mem_empty, not_false_iff],
  }
end

--

lemma replace_free_aux_admits_aux
  (P : formula)
  (v t : var_name)
  (binders : finset var_name)
  (h1 : ¬ occurs_in t P) :
  admits_aux t v binders (replace_free_aux v t binders P) :=
begin
  induction P generalizing binders,
  case formula.true_ : binders
  {
    unfold replace_free_aux,
  },
  case formula.pred_ : name args binders
  {
    unfold occurs_in at h1,
    simp only [list.mem_to_finset] at h1,

    unfold replace_free_aux,
    unfold admits_aux,
    simp only [list.mem_map, not_and, not_not, and_imp, forall_exists_index],
    intros x a1 a2 a3,

    by_cases c1 : x = v ∧ x ∉ binders,
    {
      cases c1,
      subst c1_left,
      exact c1_right,
    },
    {
      simp only [if_neg c1] at a2,
      subst a2,
      contradiction,
    }
  },
  case formula.not_ : P P_ih binders
  {
    unfold occurs_in at h1,

    unfold replace_free_aux,
    unfold admits_aux,
    tauto,
  },
  case formula.imp_ : P Q P_ih Q_ih binders
  {
    unfold occurs_in at h1,

    unfold replace_free_aux,
    unfold admits_aux,
    tauto,
  },
  case formula.forall_ : x P P_ih binders
  {
    unfold occurs_in at h1,

    unfold replace_free_aux,
    unfold admits_aux,
    tauto,
  },
end


theorem replace_free_admits
  (P : formula)
  (v t : var_name)
  (h1 : ¬ occurs_in t P) :
  admits t v (replace_free v t P) :=
begin
  unfold replace_free,
  unfold admits,
  apply replace_free_aux_admits_aux,
  exact h1,
end

--

lemma admits_aux_add_binders
  (P : formula)
  (v u : var_name)
  (S T : finset var_name)
  (h1 : admits_aux v u S P)
  (h2 : u ∉ T) :
  admits_aux v u (S ∪ T) P :=
begin
  induction P generalizing S,
  case formula.true_ : S h1
  {
    unfold admits_aux,
  },
  case formula.pred_ : name args S h1
  {
    unfold admits_aux at h1,

    unfold admits_aux,
    simp only [finset.mem_union, and_imp],
    tauto,
  },
  case formula.not_ : P P_ih S h1
  {
    unfold admits_aux at h1,

    unfold admits_aux,
    tauto,
  },
  case formula.imp_ : P Q P_ih Q_ih S h1
  {
    unfold admits_aux at h1,

    unfold admits_aux,
    tauto,
  },
  case formula.forall_ : x P P_ih S h1
  {
    unfold admits_aux at h1,

    unfold admits_aux,
    simp only [finset.union_right_comm S T {x}],
    tauto,
  },
end


lemma admits_aux_del_binders
  (P : formula)
  (v u : var_name)
  (S T : finset var_name)
  (h1 : admits_aux v u (S ∪ T) P)
  (h2 : v ∉ T) :
  admits_aux v u S P :=
begin
  induction P generalizing S,
  case formula.true_ : S h1
  {
    unfold admits_aux,
  },
  case formula.pred_ : name args S h1
  {
    unfold admits_aux at h1,
    simp only [finset.mem_union, and_imp] at h1,

    unfold admits_aux,
    tauto,
  },
  case formula.not_ : P P_ih S h1
  {
    unfold admits_aux at h1,

    unfold admits_aux,
    tauto,
  },
  case formula.imp_ : P Q P_ih Q_ih S h1
  {
    unfold admits_aux at h1,
    cases h1,

    unfold admits_aux,
    tauto,
  },
  case formula.forall_ : x P P_ih S h1
  {
    unfold admits_aux at h1,
    simp only [finset.union_right_comm S T {x}] at h1,

    unfold admits_aux,
    tauto,
  },
end


lemma admits_aux_is_free_in
  (P : formula)
  (v u : var_name)
  (binders : finset var_name)
  (h1 : admits_aux v u binders P)
  (h2 : is_free_in v P)
  (h3 : v ∉ binders) :
  u ∉ binders :=
begin
  induction P generalizing binders,
  case formula.true_ : binders h1
  {
    unfold is_free_in at h2,

    contradiction,
  },
  case formula.pred_ : name args binders h1
  {
    unfold admits_aux at h1,

    unfold is_free_in at h2,
    simp only [list.mem_to_finset] at h2,

    tauto,
  },
  case formula.not_ : P P_ih binders h1
  {
    unfold admits_aux at h1,

    unfold is_free_in at h2,

    exact P_ih h2 binders h1 h3,
  },
  case formula.imp_ : P Q P_ih Q_ih binders h1
  {
    unfold admits_aux at h1,
    cases h1,

    unfold is_free_in at h2,

    cases h2,
    {
      exact P_ih h2 binders h1_left h3,
    },
    {
      exact Q_ih h2 binders h1_right h3,
    }
  },
  case formula.forall_ : x P P_ih binders h1
  {
    unfold admits_aux at h1,

    unfold is_free_in at h2,
    cases h2,

    apply P_ih h2_right,
    {
      apply admits_aux_del_binders P v u binders {x},
      {
        exact h1,
      },
      {
        simp only [finset.mem_singleton],
        exact h2_left,
      },
    },
    {
      exact h3,
    },
  },
end


#lint

end fol
