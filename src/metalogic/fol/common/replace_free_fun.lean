import .replace_free
import metalogic.fol.aux.function_update_ite

import data.finset


set_option pp.parens true


namespace fol

open formula


/--
  Helper function for replace_free_fun.
-/
def replace_free_fun_aux (σ : var_name → var_name) : finset var_name → formula → formula
| _ true_ := true_
| binders (pred_ name args) :=
    pred_
    name
    (args.map (fun (x : var_name), if x ∈ binders then x else σ x))
| binders (not_ P) := not_ (replace_free_fun_aux binders P)
| binders (imp_ P Q) :=
    imp_
    (replace_free_fun_aux binders P)
    (replace_free_fun_aux binders Q)
| binders (forall_ x P) :=
    forall_ x (replace_free_fun_aux (binders ∪ {x}) P)


/--
  replace_free_fun σ P := The simultaneous replacement of each free occurence of any variable v in the formula P by σ v.
-/
def replace_free_fun (σ : var_name → var_name) (P : formula) : formula := replace_free_fun_aux σ ∅ P


/--
  fast_replace_free_fun σ P := The simultaneous replacement of each free occurence of any variable v in the formula P by σ v.
-/
def fast_replace_free_fun : (var_name → var_name) → formula → formula
| _ true_ := true_
| σ (pred_ name args) := pred_ name (args.map σ)
| σ (not_ P) := not_ (fast_replace_free_fun σ P)
| σ (imp_ P Q) := imp_ (fast_replace_free_fun σ P) (fast_replace_free_fun σ Q)
| σ (forall_ x P) := forall_ x (fast_replace_free_fun (function.update_ite σ x x) P)



lemma fast_replace_free_fun_id
  (P : formula) :
  fast_replace_free_fun id P = P :=
begin
  induction P,
  case formula.true_
  {
    refl,
  },
  case formula.pred_ : name args
  {
    unfold fast_replace_free_fun,
    simp only [list.map_id, eq_self_iff_true, and_self],
  },
  case formula.not_ : P P_ih
  {
    solve_by_elim,
  },
  case formula.imp_ : P Q P_ih Q_ih
  {
    unfold fast_replace_free_fun,
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
    unfold fast_replace_free_fun,
    simp only [eq_self_iff_true, true_and],
    simp only [function.update_ite_id],
    exact P_ih,
  },
end


example
  (P : formula)
  (v t : var_name) :
  fast_replace_free_fun (function.update_ite id v t) P = fast_replace_free v t P :=
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
  case formula.not_ : P P_ih
  {
    unfold fast_replace_free_fun,
    unfold fast_replace_free,
    congr,
    exact P_ih,
  },
  case formula.imp_ : P Q P_ih Q_ih
  {
    unfold fast_replace_free_fun,
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
    unfold fast_replace_free_fun,
    unfold fast_replace_free,
    split_ifs,
    {
      subst h,
      simp only [eq_self_iff_true, function.update_ite_idem, true_and],

      simp only [function.update_ite_id],
      apply fast_replace_free_fun_id,
    },
    {
      have s1 : (function.update_ite (function.update_ite (id : var_name → var_name) v t) x x) = function.update_ite id v t,
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


lemma fast_replace_free_fun_same_on_free
  (P : formula)
  (σ σ' : var_name → var_name)
  (h1 : ∀ (v : var_name), is_free_in v P → σ v = σ' v) :
  fast_replace_free_fun σ P =
    fast_replace_free_fun σ' P :=
begin
  induction P generalizing σ σ',
  case formula.true_ : σ σ' h1
  {
    unfold fast_replace_free_fun,
  },
  case formula.pred_ : name args σ σ' h1
  {
    unfold is_free_in at h1,
    squeeze_simp at h1,

    unfold fast_replace_free_fun,
    congr' 1,
    simp only [list.map_eq_map_iff],
    intros x a1,
    exact h1 x a1,
  },
  case formula.not_ : P P_ih σ σ' h1
  {
    unfold is_free_in at h1,

    unfold fast_replace_free_fun,
    congr' 1,
    exact P_ih σ σ' h1,
  },
  case formula.imp_ : P Q P_ih Q_ih σ σ' h1
  {
    unfold is_free_in at h1,
    squeeze_simp at h1,

    unfold fast_replace_free_fun,
    congr' 1,
    {
      apply P_ih,
      intros v a1,
      apply h1,
      left,
      exact a1,
    },
    {
      apply Q_ih,
      intros v a1,
      apply h1,
      right,
      exact a1,
    },
  },
  case formula.forall_ : x P P_ih σ σ' h1
  {
    unfold fast_replace_free_fun,
    congr' 1,
    apply P_ih,
    intros v a1,
    unfold function.update_ite,
    split_ifs,
    {
      refl,
    },
    {
      apply h1,
      unfold is_free_in,
      squeeze_simp,
      split,
      {
        exact h,
      },
      {
        exact a1,
      }
    }
  },
end


lemma replace_free_fun_aux_same_on_free
  (P : formula)
  (σ σ' : var_name → var_name)
  (binders : finset var_name)
  (h1 : ∀ (v : var_name), v ∉ binders → σ v = σ' v) :
  replace_free_fun_aux σ binders P =
    replace_free_fun_aux σ' binders P :=
begin
  induction P generalizing binders,
  case formula.true_ : binders h1
  {
    refl,
  },
  case formula.pred_ : name args binders h1
  {
    unfold replace_free_fun_aux,
    congr' 1,
    simp only [list.map_eq_map_iff],
    intros x a1,
    split_ifs,
    {
      refl,
    },
    {
      exact h1 x h,
    }
  },
  case formula.not_ : P P_ih binders h1
  {
    unfold replace_free_fun_aux,
    congr' 1,
    exact P_ih binders h1,
  },
  case formula.imp_ : P Q P_ih Q_ih binders h1
  {
    unfold replace_free_fun_aux,
    congr' 1,
    {
      exact P_ih binders h1,
    },
    {
      exact Q_ih binders h1,
    }
  },
  case formula.forall_ : x P P_ih binders h1
  {
    unfold replace_free_fun_aux,
    congr' 1,
    apply P_ih,
    intros v a1,
    simp only [finset.mem_union, finset.mem_singleton] at a1,
    push_neg at a1,
    cases a1,
    apply h1 v a1_left,
  },
end


example
  (P : formula)
  (σ : var_name → var_name)
  (binders : finset var_name)
  (h1 : ∀ (v : var_name), v ∈ binders → v = σ v) :
  replace_free_fun_aux σ binders P =
    fast_replace_free_fun σ P :=
begin
  induction P generalizing binders σ,
  case formula.true_ : binders h1
  {
    refl,
  },
  case formula.pred_ : name args binders σ h1
  {
    unfold fast_replace_free_fun,
    unfold replace_free_fun_aux,
    congr' 1,
    simp only [list.map_eq_map_iff],
    intros x a1,
    split_ifs,
    {
      exact h1 x h,
    },
    {
      refl,
    }
  },
  case formula.not_ : P P_ih binders σ h1
  {
    unfold fast_replace_free_fun,
    unfold replace_free_fun_aux,
    congr,
    exact P_ih binders σ h1,
  },
  case formula.imp_ : P Q P_ih Q_ih binders σ h1
  {
    unfold fast_replace_free_fun,
    unfold replace_free_fun_aux,
    congr,
    {
      exact P_ih binders σ h1,
    },
    {
      exact Q_ih binders σ h1,
    }
  },
  case formula.forall_ : x P P_ih binders σ h1
  {
    unfold fast_replace_free_fun,
    unfold replace_free_fun_aux,
    congr,

    rewrite replace_free_fun_aux_same_on_free P σ (function.update_ite σ x x),

    apply P_ih,
    {
      intros v a1,
      unfold function.update_ite,
      split_ifs,
      {
        exact h,
      },
      {
        simp only [finset.mem_union, finset.mem_singleton] at a1,
        tauto,
      },
    },
    {
      simp only [finset.mem_union, finset.mem_singleton, eq_self_iff_true, or_true],
      push_neg,
      intros v a1,
      cases a1,
      unfold function.update_ite,
      split_ifs,
      {
        contradiction,
      },
      {
        refl,
      },
    }
  },
end


#lint

end fol
