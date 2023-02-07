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
  if x = v then t else x

-- P (t/v)
-- v -> t in P
def replace_free (v t : variable_) : formula → formula
| (pred_ name args) := pred_ name (args.map (replace v t))
| (not_ P) := not_ (replace_free P)
| (imp_ P Q) := imp_ (replace_free P) (replace_free Q)
| (forall_ x P) :=
  if x = v
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


def admits_alt (v u : variable_) : formula → Prop
| (pred_ name args) := true
| (not_ P) := admits_alt P
| (imp_ P Q) := admits_alt P ∧ admits_alt Q
| (forall_ x P) := x = v ∨ ((x = u → v ∉ P.free_var_set) ∧ admits_alt P)


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


example
  (P : formula)
  (v u : variable_)
  (binders : finset variable_)
  (h1 : fast_admits_aux v u binders P) :
  admits' v u P :=
begin
  induction P generalizing binders,
  case formula.pred_ : name args
  {
    apply admits'.pred_,
  },
  case formula.not_ : P P_ih
  {
    unfold fast_admits_aux at h1,

    apply admits'.not_,
    exact P_ih binders h1,
  },
  case formula.imp_ : P Q P_ih Q_ih
  {
    unfold fast_admits_aux at h1,
    cases h1,

    apply admits'.imp_,
    {
      exact P_ih binders h1_left,
    },
    {
      exact Q_ih binders h1_right,
    }
  },
  case formula.forall_ : x P P_ih
  {
    unfold fast_admits_aux at h1,
    sorry,
  },
end


example
  (P : formula)
  (v u : variable_)
  (binders : finset variable_)
  (h1 : admits' v u P) :
  fast_admits_aux v u ∅ P :=
begin
  induction h1,
  case admits'.pred_ : h1_name h1_args h1_v h1_u
  {
    unfold fast_admits_aux,
    simp only [finset.not_mem_empty, not_false_iff, implies_true_iff],
  },
  case admits'.not_ : h1_P h1_v h1_u h1_1 h1_ih
  {
    unfold fast_admits_aux,
    exact h1_ih,
  },
  case admits'.imp_ : h1_P h1_Q h1_v h1_u h1_1 h1_2 h1_ih_1 h1_ih_2
  {
    unfold fast_admits_aux,
    split,
    {
      exact h1_ih_1,
    },
    {
      exact h1_ih_2,
    }
  },
  case admits'.not_free : h1_P h1_v h1_u h1_1
  {
    sorry,
  },
end



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


example
  (P : formula)
  (v u : variable_)
  (binders : finset variable_)
  (h1 : admits_aux v u binders P) :
  to_is_bound_aux binders P = to_is_bound_aux binders (replace_free v u P) :=
begin
  induction P generalizing binders,
  case formula.pred_ : name args binders h1
  {
    unfold admits_aux at h1,

    induction args generalizing binders,
    case list.nil
    {
      unfold replace_free,
      simp only [list.map_nil],
    },
    case list.cons : args_hd args_tl args_ih
    {
      sorry,
    },
  },
  case formula.not_ : P P_ih binders h1
  {
    unfold admits_aux at h1,

    unfold replace_free,
    unfold to_is_bound_aux,
    congr' 1,
    exact P_ih binders h1,
  },
  case formula.imp_ : P Q P_ih Q_ih binders h1
  {
    unfold admits_aux at h1,
    cases h1,

    unfold replace_free,
    unfold to_is_bound_aux,
    congr' 1,
    {
      exact P_ih binders h1_left,
    },
    {
      exact Q_ih binders h1_right,
    }
  },
  case formula.forall_ : x P P_ih binders h1
  {
    unfold admits_aux at h1,

    unfold replace_free,
    split_ifs,
    {
      refl,
    },
    {
      unfold to_is_bound_aux,
      congr' 1,
      apply P_ih,
      exact h1,
    }
  },
end
