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
| _ true_ := true_
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


/-- v → t -/
def replace
  {α : Type}
  [decidable_eq α]
  (v t x : α) : α :=
  if v = x then t else x

def fast_replace_free (v t : variable_) : formula → formula
| (true_) := true_
| (pred_ name args) := pred_ name (args.map (replace v t))
| (not_ P) := not_ (fast_replace_free P)
| (imp_ P Q) := imp_ (fast_replace_free P) (fast_replace_free Q)
| (forall_ x P) :=
  if v = x
  then forall_ x P
  else forall_ x (fast_replace_free P)


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


inductive is_prop_sub : formula → variable_ → variable_ → formula → Prop
| true_
  (v t : variable_) :
  is_prop_sub true_ v t true_

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


def function.update_ite
  {α β : Type}
  [decidable_eq α]
  (f : α → β)
  (a' : α) (b : β) (a : α) :=
  if a' = a then b else f a

/-
  The simultaneous replacement of the free variables in a formula.
-/
def fast_simult_replace_free : (variable_ → variable_) → formula → formula
| _ true_ := true_
| σ (pred_ name args) := pred_ name (args.map σ)
| σ (not_ P) := not_ (fast_simult_replace_free σ P)
| σ (imp_ P Q) := imp_ (fast_simult_replace_free σ P) (fast_simult_replace_free σ Q)
| σ (forall_ x P) := forall_ x (fast_simult_replace_free (function.update_ite σ x x) P)


def simult_admits_aux (σ : variable_ → variable_) : finset variable_ → formula → Prop
| _ true_ := true
| binders (pred_ name args) :=
    ∀ (v : variable_), v ∈ args ∧ v ∉ binders → σ v ∉ binders
| binders (not_ P) := simult_admits_aux binders P
| binders (imp_ P Q) := simult_admits_aux binders P ∧ simult_admits_aux binders Q
| binders (forall_ x P) := simult_admits_aux (binders ∪ {x}) P

def simult_admits (σ : variable_ → variable_) (P : formula) : Prop :=
  simult_admits_aux σ ∅ P


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


-- replace free


lemma replace_free_aux_id
  (P : formula)
  (v : variable_)
  (binders : finset variable_) :
  replace_free_aux v v binders P = P :=
begin
  induction P generalizing binders,
  case formula.true_ : binders
  {
    refl,
  },
  case formula.pred_ : name args binders
  {
    unfold replace_free_aux,
    simp only [eq_self_iff_true, list.map_eq_self_iff, ite_eq_right_iff, and_imp, true_and],
    intros x a1 a2 a3,
    exact a2,
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

theorem replace_free_id
  (P : formula)
  (v : variable_) :
  replace_free v v P = P :=
begin
  unfold replace_free,
  apply replace_free_aux_id,
end


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
    simp only [eq_self_iff_true, list.map_eq_self_iff, true_and],
    unfold replace,
    simp only [ite_eq_right_iff, imp_self, implies_true_iff],
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
  (h1 : ¬ is_free_in t P) :
  fast_replace_free t v P = P :=
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
    simp only [eq_self_iff_true, list.map_eq_self_iff, true_and],
    intros x a1,
    unfold replace,
    split_ifs,
    {
      subst h,
      contradiction,
    },
    {
      refl,
    }
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
      exact h1 h,
    }
  },
end


lemma not_is_free_in_replace_free_aux
  (P : formula)
  (v t : variable_)
  (binders : finset variable_)
  (h1 : ¬ v = t)
  (h2 : v ∉ binders) :
  ¬ is_free_in v (replace_free_aux v t binders P) :=
begin
  induction P generalizing binders,
  case formula.true_ : binders h2
  {
    unfold replace_free_aux,
    unfold is_free_in,
    simp only [not_false_iff],
  },
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

theorem not_is_free_in_replace_free
  (P : formula)
  (v t : variable_)
  (h1 : ¬ v = t) :
  ¬ is_free_in v (replace_free v t P) :=
begin
  unfold replace_free,
  apply not_is_free_in_replace_free_aux P v t ∅ h1,
  simp only [finset.not_mem_empty, not_false_iff],
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
    unfold replace,
    split_ifs,
    {
      simp only [eq_comm],
      exact h1,
    },
    {
      simp only [eq_comm],
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


lemma replace_free_aux_inverse
  (P : formula)
  (v t : variable_)
  (binders : finset variable_)
  (h1 : ¬ occurs_in t P)
  (h2 : t ∉ binders) :
  replace_free_aux t v binders (replace_free_aux v t binders P) = P :=
begin
  induction P generalizing binders,
  case formula.true_ : binders h2
  {
    refl,
  },
  case formula.pred_ : name args binders
  {
    unfold occurs_in at h1,

    unfold replace_free_aux,
    congr,
    simp only [list.map_map, list.map_eq_self_iff, function.comp_app],
    intros x a1,
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

theorem replace_free_inverse
  (P : formula)
  (v t : variable_)
  (h1 : ¬ occurs_in t P) :
  replace_free t v (replace_free v t P) = P :=
begin
  unfold replace_free,
  apply replace_free_aux_inverse P v t ∅ h1,
  simp only [finset.not_mem_empty, not_false_iff],
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
    unfold fast_replace_free,
    simp only [list.map_map, eq_self_iff_true, list.map_eq_self_iff, function.comp_app, true_and],
    intros x a1,
    unfold replace,
    split_ifs,
    {
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
      simp only [if_neg h1_left],
      simp only [eq_self_iff_true, true_and],
      exact P_ih h1_right,
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


lemma replace_free_aux_not_mem_free
  (P : formula)
  (v t : variable_)
  (binders : finset variable_)
  (h1 : ¬ is_free_in v P) :
  replace_free_aux v t binders P = P :=
begin
  induction P generalizing binders,
  case formula.true_ : binders
  {
    unfold replace_free_aux,
  },
  case formula.pred_ : name args binders
  {
    induction args,
    case list.nil
    {
      unfold replace_free_aux,
      simp only [list.map_nil, eq_self_iff_true, and_self],
    },
    case list.cons : args_hd args_tl args_ih
    {
      unfold is_free_in at h1,
      simp only [list.to_finset_cons, finset.mem_insert, list.mem_to_finset] at h1,
      push_neg at h1,
      cases h1,

      unfold is_free_in at args_ih,
      unfold replace_free_aux at args_ih,
      simp only [list.mem_to_finset, eq_self_iff_true, list.map_eq_self_iff, ite_eq_right_iff, and_imp, true_and] at args_ih,

      unfold replace_free_aux,
      simp only [list.map, eq_self_iff_true, ite_eq_right_iff, and_imp, list.map_eq_self_iff, true_and],
      split,
      {
        intros a1,
        contradiction,
      },
      {
        exact args_ih h1_right,
      }
    },
  },
  case formula.not_ : P P_ih binders
  {
    unfold is_free_in at h1,

    unfold replace_free_aux,
    congr,
    exact P_ih h1 binders,
  },
  case formula.imp_ : P Q P_ih Q_ih binders
  {
    unfold is_free_in at h1,
    push_neg at h1,
    cases h1,

    unfold replace_free_aux,
    congr,
    {
      exact P_ih h1_left binders,
    },
    {
      exact Q_ih h1_right binders,
    }
  },
  case formula.forall_ : x P P_ih binders
  {
    unfold is_free_in at h1,
    simp only [not_and] at h1,

    unfold replace_free_aux,
    congr,
    by_cases v = x,
    {
      apply replace_free_aux_mem_binders,
      simp only [finset.mem_union, finset.mem_singleton],
      apply or.intro_right,
      exact h,
    },
    {
      apply P_ih,
      exact h1 h,
    }
  },
end

theorem replace_free_not_mem_free
  (P : formula)
  (v t : variable_)
  (h1 : ¬ is_free_in v P) :
  replace_free v t P = P :=
begin
  apply replace_free_aux_not_mem_free,
  exact h1,
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
    simp only [list.map_eq_map_iff, eq_self_iff_true, true_and],
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

theorem replace_free_eq_fast_replace_free
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
  case formula.true_
  {
    refl,
  },
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
      simp only [list.mem_to_finset, eq_self_iff_true, list.map_eq_self_iff, true_and] at args_ih,

      unfold fast_replace_free,
      simp only [list.map, eq_self_iff_true, list.map_eq_self_iff, true_and],
      split,
      {
        unfold replace,
        simp only [if_neg h1_left],
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
