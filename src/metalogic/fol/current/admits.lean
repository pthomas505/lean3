import .replace_free
import .misc_list

import data.finset


set_option pp.parens true


open formula


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
| _ true_ := true
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


def fast_admits_aux (v u : variable_) : finset variable_ → formula → Prop
| _ true_ := true
| binders (pred_ name args) :=
    v ∈ args → -- if there is a free occurrence of v in P
    u ∉ binders -- then it does not become a bound occurrence of u in P(u/v)
| binders (not_ P) := fast_admits_aux binders P
| binders (imp_ P Q) := fast_admits_aux binders P ∧ fast_admits_aux binders Q
| binders (forall_ x P) := v = x ∨ fast_admits_aux (binders ∪ {x}) P

def fast_admits (v u : variable_) (P : formula) : Prop :=
  fast_admits_aux v u ∅ P


lemma admits_aux_id
  (P : formula)
  (v : variable_)
  (binders : finset variable_) :
  admits_aux v v binders P :=
begin
  induction P generalizing binders,
  case formula.true_ : binders
  {
    unfold admits_aux,
  },
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

theorem admits_id
  (P : formula)
  (v : variable_) :
  admits v v P :=
begin
  unfold admits,
  apply admits_aux_id,
end


lemma not_free_in_imp_fast_admits_aux
  (P : formula)
  (v u : variable_)
  (binders : finset variable_)
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
    intros a1,
    contradiction,
  },
  case formula.not_ : P P_ih
  {
    unfold is_free_in at h1,

    unfold fast_admits_aux,
    exact P_ih h1 binders,
  },
  case formula.imp_ : P Q P_ih Q_ih
  {
    unfold is_free_in at h1,
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
    unfold is_free_in at h1,
    push_neg at h1,

    unfold fast_admits_aux,
    by_cases c1 : v = x,
    {
      apply or.intro_left,
      exact c1,
    },
    {
      apply or.intro_right,
      apply P_ih,
      exact h1 c1,
    }
  },
end


lemma not_free_in_imp_fast_admits
  (P : formula)
  (v u : variable_)
  (h1 : ¬ is_free_in v P) :
  fast_admits v u P :=
begin
  unfold fast_admits,
  apply not_free_in_imp_fast_admits_aux,
  exact h1,
end


lemma not_bound_in_imp_admits_aux
  (P : formula)
  (v u : variable_)
  (binders : finset variable_)
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
    intros a1,
    exact h2,
  },
  case formula.not_ : P P_ih binders h2
  {
    unfold is_bound_in at h1,

    unfold admits_aux,
    exact P_ih h1 binders h2,
  },
  case formula.imp_ : P Q P_ih Q_ih binders h2
  {
    unfold is_bound_in at h1,
    push_neg at h1,
    cases h1,

    unfold admits_aux,
    split,
    {
      exact P_ih h1_left binders h2,
    },
    {
      exact Q_ih h1_right binders h2,
    }
  },
  case formula.forall_ : x P P_ih binders h2
  {
    unfold is_bound_in at h1,
    push_neg at h1,
    cases h1,

    unfold admits_aux,
    apply P_ih h1_right,
    simp only [finset.mem_union, finset.mem_singleton],
    push_neg,
    split,
    {
      exact h2,
    },
    {
      exact h1_left,
    }
  },
end


lemma replace_free_aux_admits_aux
  (P : formula)
  (v t : variable_)
  (binders : finset variable_)
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
  case formula.true_ : S h1
  {
    unfold admits_aux,
  },
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
  case formula.true_ : S h1
  {
    unfold admits_aux,
  },
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




lemma fast_admits_aux_del_binders
  (P : formula)
  (v u : variable_)
  (S T : finset variable_)
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
  case formula.true_ : binders h1
  {
    unfold formula.free_var_set at h2,
    simp only [finset.not_mem_empty] at h2,

    contradiction,
  },
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
  case formula.true_ : binders h1 h2
  {
    unfold fast_admits_aux,
  },
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
  case formula.true_ : binders h1
  {
    unfold admits_aux,
  },
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




@[derive [inhabited, decidable_eq]]
inductive bool_formula : Type
| true_ : bool_formula
| pred_ : pred_name_ → list bool → bool_formula
| not_ : bool_formula → bool_formula
| imp_ : bool_formula → bool_formula → bool_formula
| forall_ : bool → bool_formula → bool_formula


def to_is_bound_aux : finset variable_ → formula → bool_formula
| _ true_ := bool_formula.true_
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

      specialize args_ih h2_right,

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


def simult_admits_aux (σ : variable_ → variable_) : finset variable_ → formula → Prop
| _ true_ := true
| binders (pred_ name args) :=
    ∀ (v : variable_), v ∈ args ∧ v ∉ binders → σ v ∉ binders
| binders (not_ P) := simult_admits_aux binders P
| binders (imp_ P Q) := simult_admits_aux binders P ∧ simult_admits_aux binders Q
| binders (forall_ x P) := simult_admits_aux (binders ∪ {x}) P

def simult_admits (σ : variable_ → variable_) (P : formula) : Prop :=
  simult_admits_aux σ ∅ P


#lint
