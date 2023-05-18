import metalogic.fol.aux.misc_list
import metalogic.fol.aux.function_update_ite
import metalogic.fol.common.semantics
import metalogic.fol.common.subst_single.admits_single

import data.finset


set_option pp.parens true


namespace fol

open formula


/--
  Helper function for replace_free_fun.
-/
def replace_free_fun_aux (σ : var_name → var_name) : finset var_name → formula → formula
| _ true_ := true_
| binders (pred_ X xs) :=
    pred_
    X
    (xs.map (fun (x : var_name), if x ∈ binders then x else σ x))
| binders (not_ phi) := not_ (replace_free_fun_aux binders phi)
| binders (imp_ phi psi) :=
    imp_
    (replace_free_fun_aux binders phi)
    (replace_free_fun_aux binders psi)
| binders (forall_ x phi) :=
    forall_ x (replace_free_fun_aux (binders ∪ {x}) phi)


/--
  replace_free_fun σ F := The simultaneous replacement of each free occurence of any variable v in the formula F by σ v.
-/
def replace_free_fun (σ : var_name → var_name) (F : formula) : formula := replace_free_fun_aux σ ∅ F


/--
  fast_replace_free_fun σ F := The simultaneous replacement of each free occurence of any variable v in the formula F by σ v.
-/
def fast_replace_free_fun : (var_name → var_name) → formula → formula
| _ true_ := true_
| σ (pred_ X xs) := pred_ X (xs.map σ)
| σ (not_ phi) := not_ (fast_replace_free_fun σ phi)
| σ (imp_ phi psi) := imp_ (fast_replace_free_fun σ phi) (fast_replace_free_fun σ psi)
| σ (forall_ x phi) := forall_ x (fast_replace_free_fun (function.update_ite σ x x) phi)



lemma fast_replace_free_fun_id
  (F : formula) :
  fast_replace_free_fun id F = F :=
begin
  induction F,
  case formula.true_
  {
    refl,
  },
  case formula.pred_ : X xs
  {
    unfold fast_replace_free_fun,
    simp only [list.map_id, eq_self_iff_true, and_self],
  },
  case formula.not_ : phi phi_ih
  {
    solve_by_elim,
  },
  case formula.imp_ : phi psi phi_ih psi_ih
  {
    unfold fast_replace_free_fun,
    congr,
    {
      exact phi_ih,
    },
    {
      exact psi_ih,
    }
  },
  case formula.forall_ : x phi phi_ih
  {
    unfold fast_replace_free_fun,
    simp only [eq_self_iff_true, true_and],
    simp only [function.update_ite_id],
    exact phi_ih,
  },
end


example
  (F : formula)
  (v t : var_name) :
  fast_replace_free_fun (function.update_ite id v t) F = fast_replace_free v t F :=
begin
  induction F,
  case formula.true_
  {
    refl,
  },
  case formula.pred_ : X xs
  {
    refl,
  },
  case formula.not_ : phi phi_ih
  {
    unfold fast_replace_free_fun,
    unfold fast_replace_free,
    congr,
    exact phi_ih,
  },
  case formula.imp_ : phi psi phi_ih psi_ih
  {
    unfold fast_replace_free_fun,
    unfold fast_replace_free,
    congr,
    {
      exact phi_ih,
    },
    {
      exact psi_ih,
    }
  },
  case formula.forall_ : x phi phi_ih
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
      exact phi_ih,
    }
  },
end


lemma fast_replace_free_fun_same_on_free
  (F : formula)
  (σ σ' : var_name → var_name)
  (h1 : ∀ (v : var_name), is_free_in v F → σ v = σ' v) :
  fast_replace_free_fun σ F =
    fast_replace_free_fun σ' F :=
begin
  induction F generalizing σ σ',
  case formula.true_ : σ σ' h1
  {
    unfold fast_replace_free_fun,
  },
  case formula.pred_ : X xs σ σ' h1
  {
    unfold is_free_in at h1,
    simp at h1,

    unfold fast_replace_free_fun,
    congr' 1,
    simp only [list.map_eq_map_iff],
    intros x a1,
    exact h1 x a1,
  },
  case formula.not_ : phi phi_ih σ σ' h1
  {
    unfold is_free_in at h1,

    unfold fast_replace_free_fun,
    congr' 1,
    exact phi_ih σ σ' h1,
  },
  case formula.imp_ : phi psi phi_ih psi_ih σ σ' h1
  {
    unfold is_free_in at h1,
    simp at h1,

    unfold fast_replace_free_fun,
    congr' 1,
    {
      apply phi_ih,
      intros v a1,
      apply h1,
      left,
      exact a1,
    },
    {
      apply psi_ih,
      intros v a1,
      apply h1,
      right,
      exact a1,
    },
  },
  case formula.forall_ : x phi phi_ih σ σ' h1
  {
    unfold fast_replace_free_fun,
    congr' 1,
    apply phi_ih,
    intros v a1,
    unfold function.update_ite,
    split_ifs,
    {
      refl,
    },
    {
      apply h1,
      unfold is_free_in,
      simp,
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
  (F : formula)
  (σ σ' : var_name → var_name)
  (binders : finset var_name)
  (h1 : ∀ (v : var_name), v ∉ binders → σ v = σ' v) :
  replace_free_fun_aux σ binders F =
    replace_free_fun_aux σ' binders F :=
begin
  induction F generalizing binders,
  case formula.true_ : binders h1
  {
    refl,
  },
  case formula.pred_ : X xs binders h1
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
  case formula.not_ : phi phi_ih binders h1
  {
    unfold replace_free_fun_aux,
    congr' 1,
    exact phi_ih binders h1,
  },
  case formula.imp_ : phi psi phi_ih psi_ih binders h1
  {
    unfold replace_free_fun_aux,
    congr' 1,
    {
      exact phi_ih binders h1,
    },
    {
      exact psi_ih binders h1,
    }
  },
  case formula.forall_ : x phi phi_ih binders h1
  {
    unfold replace_free_fun_aux,
    congr' 1,
    apply phi_ih,
    intros v a1,
    simp only [finset.mem_union, finset.mem_singleton] at a1,
    push_neg at a1,
    cases a1,
    apply h1 v a1_left,
  },
end


example
  (F : formula)
  (σ : var_name → var_name)
  (binders : finset var_name)
  (h1 : ∀ (v : var_name), v ∈ binders → v = σ v) :
  replace_free_fun_aux σ binders F =
    fast_replace_free_fun σ F :=
begin
  induction F generalizing binders σ,
  case formula.true_ : binders h1
  {
    refl,
  },
  case formula.pred_ : X xs binders σ h1
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
  case formula.not_ : phi phi_ih binders σ h1
  {
    unfold fast_replace_free_fun,
    unfold replace_free_fun_aux,
    congr,
    exact phi_ih binders σ h1,
  },
  case formula.imp_ : phi psi phi_ih psi_ih binders σ h1
  {
    unfold fast_replace_free_fun,
    unfold replace_free_fun_aux,
    congr,
    {
      exact phi_ih binders σ h1,
    },
    {
      exact psi_ih binders σ h1,
    }
  },
  case formula.forall_ : x phi phi_ih binders σ h1
  {
    unfold fast_replace_free_fun,
    unfold replace_free_fun_aux,
    congr,

    rewrite replace_free_fun_aux_same_on_free phi σ (function.update_ite σ x x),

    apply phi_ih,
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



end fol
