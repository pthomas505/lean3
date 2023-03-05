import .replace_free
import .misc_list
import .admits

import data.finset


set_option pp.parens true


open formula

/--
  admits_alt v u P := True if and only if there is no free occurrence of the variable v in the formula P that becomes a bound occurrence of the variable u in P(u/v).

  P admits u for v

  v → u in P

  This is a version of admits that does not require the use of a binders variable.
-/
def admits_alt (v u : variable_) : formula → Prop
| (true_) := true
| (pred_ name args) := true
| (eq_ x y) := true
| (not_ P) := admits_alt P
| (imp_ P Q) := admits_alt P ∧ admits_alt Q
| (forall_ x P) := v = x ∨ ((x = u → ¬ is_free_in v P) ∧ admits_alt P)



lemma admits_alt_imp_fast_admits_aux
  (P : formula)
  (v u : variable_)
  (binders : finset variable_)
  (h1 : u ∉ binders)
  (h2 : admits_alt v u P) :
  fast_admits_aux v u binders P :=
begin
  induction P generalizing binders,
  case formula.true_ : binders
  {
    unfold fast_admits_aux,
  },
  case formula.pred_ : name args binders
  {
    unfold fast_admits_aux,
    tauto,
  },
  case formula.eq_ : x y binders h1
  {
    unfold fast_admits_aux,
    tauto,
  },
  case formula.not_ : P P_ih binders
  {
    unfold admits_alt at h2,

    unfold fast_admits_aux,
    tauto,
  },
  case formula.imp_ : P Q P_ih Q_ih binders
  {
    unfold admits_alt at h2,

    unfold fast_admits_aux,
    tauto,
  },
  case formula.forall_ : x P P_ih binders
  {
    unfold admits_alt at h2,

    unfold fast_admits_aux,
    by_cases c1 : x = u,
    {
      cases h2,
      {
        left,
        exact h2,
      },
      {
        right,
        subst c1,
        simp only [eq_self_iff_true, forall_true_left] at h2,
        cases h2,
        apply not_is_free_in_imp_fast_admits_aux,
        exact h2_left,
      }
    },
    {
      cases h2,
      {
        left,
        exact h2,
      },
      {
        right,
        cases h2,
        apply P_ih,
        {
          exact h2_right,
        },
        {
          simp only [finset.mem_union, finset.mem_singleton],
          tauto,
        }
      }
    }
  },
end


lemma fast_admits_aux_imp_admits_alt
  (P : formula)
  (v u : variable_)
  (binders : finset variable_)
  (h1 : fast_admits_aux v u binders P) :
  admits_alt v u P :=
begin
  induction P generalizing binders,
  case formula.true_ : binders
  {
    unfold admits_alt,
  },
  case formula.pred_ : name args binders
  {
    unfold admits_alt,
  },
  case formula.eq_ : x y binders
  {
    unfold admits_alt,
  },
  case formula.not_ : P P_ih binders
  {
    unfold fast_admits_aux at h1,

    unfold admits_alt,
    tauto,
  },
  case formula.imp_ : P Q P_ih Q_ih binders
  {
    unfold fast_admits_aux at h1,

    unfold admits_alt,
    tauto,
  },
  case formula.forall_ : x P P_ih binders
  {
    unfold fast_admits_aux at h1,

    unfold admits_alt,
    cases h1,
    {
      left,
      exact h1,
    },
    {
      right,
      split,
      {
        intros a1,
        subst a1,
        apply fast_admits_aux_mem_binders P v x (binders ∪ {x}) h1,
        {
          simp only [finset.mem_union, finset.mem_singleton, eq_self_iff_true, or_true],
        }
      },
      {
        apply P_ih,
        exact h1,
      }
    }
  },
end


theorem admits_alt_iff_fast_admits_
  (P : formula)
  (v u : variable_) :
  admits_alt v u P ↔ fast_admits v u P :=
begin
  unfold fast_admits,
  split,
  {
    apply admits_alt_imp_fast_admits_aux,
    simp only [finset.not_mem_empty, not_false_iff],
  },
  {
    apply fast_admits_aux_imp_admits_alt,
  }
end

--

lemma admits_alt_self
  (P : formula)
  (v : variable_) :
  admits_alt v v P :=
begin
  induction P;
  unfold admits_alt;
  tauto,
end


lemma not_is_free_in_imp_admits_alt
  (P : formula)
  (v u : variable_)
  (h1 : ¬ is_free_in v P) :
  admits_alt v u P :=
begin
  induction P;
  unfold is_free_in at h1;
  unfold admits_alt;
  tauto,
end


lemma not_is_bound_in_imp_admits_alt
  (P : formula)
  (v u : variable_)
  (h1 : ¬ is_bound_in u P) :
  admits_alt v u P :=
begin
  induction P;
  unfold is_bound_in at h1;
  unfold admits_alt;
  tauto,
end


lemma fast_replace_free_admits_alt
  (P : formula)
  (v t : variable_)
  (h1 : ¬ occurs_in t P) :
  admits_alt t v (fast_replace_free v t P) :=
begin
  induction P,
  case formula.true_
  {
    unfold fast_replace_free,
  },
  case formula.pred_ : name args
  {
    unfold fast_replace_free,
  },
  case formula.eq_ : x y
  {
    unfold fast_replace_free,
  },
  case formula.not_ : P P_ih
  {
    unfold occurs_in at h1,

    unfold fast_replace_free,
    unfold admits_alt,
    exact P_ih h1,
  },
  case formula.imp_ : P Q P_ih Q_ih
  {
    unfold occurs_in at h1,

    unfold fast_replace_free,
    unfold admits_alt,
    tauto,
  },
  case formula.forall_ : x P P_ih
  {
    unfold occurs_in at h1,
    push_neg at h1,
    cases h1,

    unfold fast_replace_free,
    split_ifs,
    {
      unfold admits_alt,
      subst h,
      right,
      simp only [eq_self_iff_true, forall_true_left],
      split,
      {
        intros contra,
        apply h1_right,
        apply is_free_in_imp_occurs_in,
        exact contra,
      },
      {
        apply not_is_free_in_imp_admits_alt,
        intros contra,
        apply h1_right,
        apply is_free_in_imp_occurs_in,
        exact contra,
      },
    },
    {
      unfold admits_alt,
      right,
      split,
      {
        intros a1,
        subst a1,
        contradiction,
      },
      {
        exact P_ih h1_right,
      }
    }
  },
end
