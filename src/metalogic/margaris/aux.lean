/-
Reference:
First Order Mathematical Logic (Dover Books on Mathematics)
by Angelo Margaris
-/


import data.finset

set_option pp.parens true


@[derive decidable_eq]
inductive variable_ : Type
| variable_ : string → variable_


@[derive decidable_eq]
inductive pred_name_ : Type
| pred_name_ : string → pred_name_


@[derive decidable_eq]
inductive formula : Type
| pred_ : pred_name_ → list variable_ → formula
| not_ : formula → formula
| imp_ : formula → formula → formula
| forall_ : variable_ → formula → formula

open formula


/-
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


/-
pg. 48

If $P$ is a formula, $v$ is a variable, and $t$ is a term, then $P(t/v)$ is the result of replacing each free occurrence of $v$ in $P$ by an occurrence of $t$.
-/

-- v -> t
def replace
  {α : Type}
  [decidable_eq α]
  (v t x : α) : α :=
  if v = x then t else x

-- P (t/v)
-- v -> t in P
def replace_free (v t : variable_) : formula → formula
| (pred_ name args) := pred_ name (args.map (replace v t))
| (not_ P) := not_ (replace_free P)
| (imp_ P Q) := imp_ (replace_free P) (replace_free Q)
| (forall_ x P) :=
  if v = x
  then forall_ x P
  else forall_ x (replace_free P)


/-
pg. 48

If $v$ and $u$ are variables and $P$ is a formula, then $P$ admits $u$ for $v$ if and only if there is no free occurrence of $v$ in $P$ that becomes a bound occurrence of $u$ in $P(u/v)$. If $t$ is a term, then $P$ admits $t$ for $v$ if and only if $P$ admits for $v$ every variable in $t$.
-/

-- P admits u for v
-- v → u in P

def admits_aux (v u : variable_) : finset variable_ → formula → Prop
| binders (pred_ name args) :=
    (v ∈ args ∧ v ∉ binders) → -- if there is a free occurrence of v in P
    u ∉ binders -- then it does not become a bound occurrence of u in P(u/v)
| binders (not_ P) := admits_aux binders P
| binders (imp_ P Q) := admits_aux binders P ∧ admits_aux binders Q
| binders (forall_ x P) := admits_aux (binders ∪ {x}) P

def admits (v u : variable_) (P : formula) : Prop :=
  admits_aux v u ∅ P


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


lemma admits_aux_eqv_left
  (P : formula)
  (v u : variable_)
  (S : finset variable_)
  (h1 : admits_aux v u S P)
  (h2 : v ∉ S) :
  fast_admits_aux v u S P :=
begin
  induction P generalizing S,
  case formula.pred_ : name args S h1 h2
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
  case formula.not_ : P P_ih S h1 h2
  {
    unfold admits_aux at h1,

    unfold fast_admits_aux,
    exact P_ih S h1 h2,
  },
  case formula.imp_ : P Q P_ih Q_ih S h1 h2
  {
    unfold admits_aux at h1,
    cases h1,

    unfold fast_admits_aux,
    split,
    {
      exact P_ih S h1_left h2,
    },
    {
      exact Q_ih S h1_right h2,
    }
  },
  case formula.forall_ : x P P_ih S h1 h2
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


lemma admits_aux_eqv_right
  (P : formula)
  (v u : variable_)
  (S : finset variable_)
  (h1 : v ∈ S ∨ fast_admits_aux v u S P) :
  admits_aux v u S P :=
begin
  induction P generalizing S,
  case formula.pred_ : name args S h1
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
  case formula.not_ : P P_ih S h1
  {
    unfold fast_admits_aux at h1,

    unfold admits_aux,
    exact P_ih S h1,
  },
  case formula.imp_ : P Q P_ih Q_ih S h1
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
  case formula.forall_ : x P P_ih S h1
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
    apply admits_aux_eqv_left,
    {
      exact a1,
    },
    {
      simp only [finset.not_mem_empty, not_false_iff],
    }
  },
  {
    intros a1,
    apply admits_aux_eqv_right,
    simp only [finset.not_mem_empty, false_or],
    exact a1,
  }
end


lemma not_free_imp_fast_admits_aux
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


lemma not_free_imp_fast_admits
  (P : formula)
  (v u : variable_)
  (h1 : v ∉ P.free_var_set) :
  fast_admits v u P :=
begin
  unfold fast_admits,
  apply not_free_imp_fast_admits_aux,
  exact h1,
end


inductive admits' : variable_ → variable_ → formula → Prop

| pred_ (name : pred_name_) (args : list variable_)
  (v u : variable_) :
  admits' v u (pred_ name args)

| not_ (P : formula)
  (v u : variable_) :
  admits' v u P →
  admits' v u (not_ P)

| imp_ (P Q : formula)
  (v u : variable_) :
  admits' v u P →
  admits' v u Q →
  admits' v u (imp_ P Q)

| not_free (P : formula)
  (v u : variable_) :
  v ∉ P.free_var_set →
  admits' v u P


@[derive decidable_eq]
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


lemma lem_1
  (P : formula)
  (v u : variable_)
  (binders : finset variable_)
  (h1 : fast_admits_aux v u binders P)
  (h2 : v ∉ binders) :
  to_is_bound_aux binders P = to_is_bound_aux binders (replace_free v u P) :=
begin
  induction P generalizing binders,
  case formula.pred_ : name args binders
  {
    unfold fast_admits_aux at h1,

    induction args generalizing binders,
    case list.nil
    {
      unfold replace_free,
      simp only [list.map_nil],
    },
    case list.cons : args_hd args_tl args_ih
    {
      squeeze_simp at h1,

      have s1 : ((v ∈ args_tl) → (u ∉ binders)) ,
      intros a1,
      apply h1,
      apply or.intro_right,
      exact a1,

      unfold replace_free at args_ih,
      unfold to_is_bound_aux at args_ih,

      unfold replace_free,
      unfold to_is_bound_aux,

      squeeze_simp,
      split,
      split,
      intros a1,
      unfold replace,
      split_ifs, -- v ∉ binders
      subst h,
      contradiction,
      exact a1,
      unfold replace,
      split_ifs,
      intros a1,
      exfalso,
      apply h1,
      apply or.intro_left,
      exact h,
      exact a1,
      simp only [imp_self],
      specialize args_ih binders h2 s1,
      injection args_ih,
      squeeze_simp at h_2,
      exact h_2,
    },
  },
  case formula.not_ : P P_ih binders h1
  {
    unfold fast_admits_aux at h1,

    unfold replace_free,
    unfold to_is_bound_aux,
    congr' 1,
    exact P_ih binders h1 h2,
  },
  case formula.imp_ : P Q P_ih Q_ih binders h1
  {
    unfold fast_admits_aux at h1,
    cases h1,

    unfold replace_free,
    unfold to_is_bound_aux,
    congr' 1,
    {
      exact P_ih binders h1_left h2,
    },
    {
      exact Q_ih binders h1_right h2,
    }
  },
  case formula.forall_ : x P P_ih binders h1
  {
    unfold fast_admits_aux at h1,

    unfold replace_free,
    split_ifs,
    {
      refl,
    },
    {
      unfold to_is_bound_aux,
      congr' 1,
      apply P_ih,
      cases h1,
      {
        contradiction,
      },
      {
        exact h1,
      },
      {
        simp only [finset.mem_union, finset.mem_singleton],
        push_neg,
        split,
        exact h2,
        exact h,
      }
    }
  },
end


example
  (P : formula)
  (v u : variable_)
  (binders : finset variable_)
  (h1 : fast_admits v u P) :
  to_is_bound P = to_is_bound (replace_free v u P) :=
begin
  apply lem_1,
  exact h1,
  simp only [finset.not_mem_empty, not_false_iff],
end


lemma lem_2
  (P : formula)
  (v u : variable_)
  (binders : finset variable_)
  (h1 : to_is_bound_aux binders P = to_is_bound_aux binders (replace_free v u P))
  (h2 : v ∉ binders) :
  fast_admits_aux v u binders P :=
begin
  induction P generalizing binders,
  case formula.pred_ : name args binders h1
  {
    unfold replace_free at h1,
    unfold to_is_bound_aux at h1,
    injection h1,

    unfold fast_admits_aux,
    intros a1,
    squeeze_simp at h_2,
    simp only [list.map_eq_map_iff] at h_2,
    specialize h_2 v a1,
    squeeze_simp at h_2,
    unfold replace at h_2,
    split_ifs at h_2,
    cases h_2,
    by_contra,
    apply h2,
    apply h_2_mpr,
    exact h,
    contradiction,
  },
  case formula.not_ : P P_ih binders h1
  {
    unfold replace_free at h1,
    unfold to_is_bound_aux at h1,
    injection h1,
    unfold fast_admits_aux,
    apply P_ih,
    exact h_1,
    exact h2,
  },
  case formula.imp_ : P Q P_ih Q_ih binders h1
  {
    unfold replace_free at h1,
    unfold to_is_bound_aux at h1,
    injection h1,
    unfold fast_admits_aux,
    split,
    apply P_ih,
    exact h_1,
    exact h2,
    apply Q_ih,
    exact h_2,
    exact h2,
  },
  case formula.forall_ : x P P_ih binders h1
  {
    unfold replace_free at h1,
    unfold to_is_bound_aux at h1,

    unfold fast_admits_aux,

    by_cases v = x,
    apply or.intro_left,
    exact h,

    apply or.intro_right,
    apply P_ih,
    split_ifs at h1,
    unfold to_is_bound_aux at h1,
    injection h1,
    squeeze_simp,
    push_neg,
    split,
    exact h2,
    exact h,

  },
end

example
  (P : formula)
  (v u : variable_)
  (h1 : to_is_bound P = to_is_bound (replace_free v u P)) :
  fast_admits v u P :=
begin
  apply lem_2,
  unfold to_is_bound at h1,
  exact h1,
  simp only [finset.not_mem_empty, not_false_iff],
end


example
  (P : formula)
  (v u : variable_)
  (binders : finset variable_)
  (h1 : v ∉ binders)
  (h2 : admits_aux v u binders P) :
  to_is_bound_aux binders P = to_is_bound_aux binders (replace_free v u P) :=
begin
  induction P generalizing binders,
  case formula.pred_ : name args binders h1 h2
  {
    induction args,
    case list.nil
    {
      unfold replace_free,
      simp only [list.map_nil],
    },
    case list.cons : args_hd args_tl args_ih
    {
      unfold admits_aux at h2,
      simp only [list.mem_cons_iff, and_imp] at h2,

      unfold admits_aux at args_ih,
      unfold replace_free at args_ih,
      unfold to_is_bound_aux at args_ih,

      simp only [and_imp, list.map_map, eq_self_iff_true, true_and] at args_ih,

      have s1 : ((v ∈ args_tl) → (v ∉ binders) → (u ∉ binders)),
      intros a1 a2,
      apply h2,
      {
        apply or.intro_right,
        exact a1,
      },
      {
        exact a2,
      },

      specialize args_ih s1,

      unfold replace_free,
      unfold to_is_bound_aux,

      simp only [list.map, list.map_map, eq_self_iff_true, bool.to_bool_eq, true_and],
      split,
      {
        unfold replace,
        split_ifs,
        {
          split,
          {
            intros a1,
            subst h,
            contradiction,
          },
          {
            intros a1,
            exfalso,
            apply h2,
            {
              apply or.intro_left,
              exact h,
            },
            {
              exact h1,
            },
            {
              exact a1,
            },
          }
        },
        {
          refl,
        }
      },
      {
        exact args_ih,
      }
    },
  },
  case formula.not_ : P P_ih binders h1 h2
  {
    unfold admits_aux at h2,

    unfold replace_free,
    unfold to_is_bound_aux,
    simp only,
    exact P_ih binders h1 h2,
  },
  case formula.imp_ : P Q P_ih Q_ih binders h1 h2
  {
    unfold admits_aux at h2,
    cases h2,

    unfold replace_free,
    unfold to_is_bound_aux,
    simp only,
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

    unfold replace_free,
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
        exact h2,
      }
    }
  },
end


example
  (P : formula)
  (v u : variable_)
  (binders : finset variable_)
  (h1 : to_is_bound_aux binders P = to_is_bound_aux binders (replace_free v u P)) :
  admits_aux v u binders P :=
begin
  induction P generalizing binders,
  case formula.pred_ : name args binders h1
  {
    induction args,
    case list.nil
    {
      unfold admits_aux,
      simp only [list.not_mem_nil, false_and, is_empty.forall_iff],
    },
    case list.cons : args_hd args_tl args_ih
    {
      unfold replace_free at h1,
      unfold to_is_bound_aux at h1,
      simp only [list.map, list.map_map, eq_self_iff_true, bool.to_bool_eq, true_and] at h1,
      cases h1,

      unfold admits_aux at args_ih,
      unfold replace_free at args_ih,
      unfold to_is_bound_aux at args_ih,
      simp only [list.map_map, eq_self_iff_true, true_and, and_imp] at args_ih,

      specialize args_ih h1_right,

      unfold admits_aux,
      simp only [list.mem_cons_iff, and_imp],
      intros a1 a2,

      unfold replace at h1_left,
      split_ifs at h1_left,
      {
        subst h,
        cases h1_left,
        by_contradiction contra,
        apply a2,
        apply h1_left_mpr,
        exact contra,
      },
      {
        apply args_ih,
        {
          cases a1,
          {
            contradiction,
          },
          {
            exact a1,
          },
        },
        {
          exact a2,
        }
      },
    },
  },
  case formula.not_ : P_ᾰ P_ih binders h1
  { admit },
  case formula.imp_ : P_ᾰ P_ᾰ_1 P_ih_ᾰ P_ih_ᾰ_1 binders h1
  { admit },
  case formula.forall_ : x P P_ih binders h1
  { admit },
end


example
  (P : formula)
  (v u : variable_)
  (binders : finset variable_)
  (h1 : v ∉ binders)
  (h2 : to_is_bound_aux binders P = to_is_bound_aux binders (replace_free v u P)) :
  admits_aux v u binders P :=
begin
  induction P generalizing binders,
  case formula.pred_ : name args binders h1 h2
  {
    induction args,
    case list.nil
    {
      unfold admits_aux,
      simp only [list.not_mem_nil, false_and, is_empty.forall_iff],
    },
    case list.cons : args_hd args_tl args_ih
    {
      unfold replace_free at h2,
      unfold to_is_bound_aux at h2,
      simp only [list.map, list.map_map, eq_self_iff_true, bool.to_bool_eq, true_and] at h2,
      cases h2,

      unfold admits_aux at args_ih,
      unfold replace_free at args_ih,
      unfold to_is_bound_aux at args_ih,
      simp only [list.map_map, eq_self_iff_true, true_and, and_imp] at args_ih,

      specialize args_ih h2_right,

      unfold admits_aux,
      simp only [list.mem_cons_iff, and_imp],
      intros a1 a2,

      unfold replace at h2_left,
      split_ifs at h2_left,
      {
        subst h,
        cases h2_left,
        by_contradiction contra,
        apply a2,
        apply h2_left_mpr,
        exact contra,
      },
      {
        apply args_ih,
        {
          cases a1,
          {
            contradiction,
          },
          {
            exact a1,
          },
        },
        {
          exact a2,
        }
      },
    },
  },
  case formula.not_ : P P_ih binders h1 h2
  { admit },
  case formula.imp_ : P Q P_ih Q_ih binders h1 h2
  { admit },
  case formula.forall_ : x P P_ih binders h1 h2
  { admit },
end
