import metalogic.fol.aux.misc_list
import metalogic.fol.aux.function_update_ite
import metalogic.fol.common.semantics
import metalogic.fol.common.binders

import .replace_free_multiple

import data.finset


set_option pp.parens true


namespace fol

open formula




@[derive decidable]
def admits_fun_aux (σ : var_name → var_name) :
  finset var_name → formula → bool
| _ true_ := tt
| binders (pred_ X xs) :=
    ∀ (v : var_name), v ∈ xs → v ∉ binders → σ v ∉ binders 
| binders (not_ phi) := admits_fun_aux binders phi
| binders (imp_ phi psi) := admits_fun_aux binders phi ∧ admits_fun_aux binders psi
| binders (forall_ x phi) := admits_fun_aux (binders ∪ {x}) phi

@[derive decidable]
def admits_fun (σ : var_name → var_name) (phi : formula) : bool :=
  admits_fun_aux σ ∅ phi


lemma substitution_fun_theorem_aux
  {D : Type}
  (I : interpretation D)
  (V V' : valuation D)
  (σ σ' : var_name → var_name)
  (binders : finset var_name)
  (F : formula)
  (h1 : admits_fun_aux σ binders F)
  (h2 : ∀ (v : var_name), v ∈ binders ∨ σ' v ∉ binders → (V v = V' (σ' v)))
  (h2' : ∀ (v : var_name), v ∈ binders → v = σ' v)
  (h3 : ∀ (v : var_name), v ∉ binders → σ' v = σ v) :
  holds D I V F ↔
    holds D I V' (fast_replace_free_fun σ' F) :=
begin
  induction F generalizing binders V V' σ σ',
  case formula.true_ : binders V V' σ σ' h1 h2 h2' h3
  {
    unfold fast_replace_free_fun,
    unfold holds,
  },
  case formula.pred_ : X xs binders V V' σ σ' h1 h2 h2' h3
  {
    unfold admits_fun_aux at h1,
    simp only [bool.of_to_bool_iff] at h1,

    unfold fast_replace_free_fun,
    unfold holds,
    congr' 2,
    simp only [list.map_map],
    simp only [list.map_eq_map_iff],
    intros v a1,
    apply h2,
    by_cases c1 : v ∈ binders,
    {
      left,
      exact c1,
    },
    {
      right,
      simp only [h3 v c1],
      exact h1 v a1 c1,
    }
  },
  case formula.not_ : phi phi_ih binders V V' σ σ' h1 h2 h2' h3
  {
    unfold admits_fun_aux at h1,

    unfold fast_replace_free_fun,
    unfold holds,
    apply not_congr,
    exact phi_ih binders V V' σ σ' h1 h2 h2' h3,
  },
  case formula.imp_ : phi psi phi_ih psi_ih binders V V' σ σ' h1 h2 h2' h3
  {
    unfold admits_fun_aux at h1,
    simp only [bool.of_to_bool_iff] at h1,
    cases h1,

    unfold holds,
    apply imp_congr,
    {
      exact phi_ih binders V V' σ σ' h1_left h2 h2' h3,
    },
    {
      exact psi_ih binders V V' σ σ' h1_right h2 h2' h3,
    }
  },
  case formula.forall_ : x phi phi_ih binders V V' σ σ' h1 h2 h2' h3
  {
    unfold admits_fun_aux at h1,

    unfold fast_replace_free_fun,
    unfold holds,
    apply forall_congr,
    intros d,

    apply phi_ih (binders ∪ {x}) (function.update_ite V x d) (function.update_ite V' x d) σ (function.update_ite σ' x x) h1,
    {
      intros v a1,
      unfold function.update_ite at a1,
      simp only [finset.mem_union, finset.mem_singleton, ite_eq_left_iff] at a1,
      push_neg at a1,

      unfold function.update_ite,
      split_ifs,
      {
        refl,
      },
      {
        subst h_1,
        tauto,
      },
      {
        simp only [if_neg h] at a1,
        apply h2,
        tauto,
      },
    },
    {
      intros v a1,
      simp only [finset.mem_union, finset.mem_singleton] at a1,

      unfold function.update_ite,
      split_ifs,
      {
        exact h,
      },
      {
        tauto,
      },
    },
    {
      intros v a1,
      simp only [finset.mem_union, finset.mem_singleton] at a1,
      push_neg at a1,
      cases a1,
      unfold function.update_ite,
      simp only [if_neg a1_right],
      exact h3 v a1_left,
    },
  },
end


theorem substitution_fun_theorem
  {D : Type}
  (I : interpretation D)
  (V : valuation D)
  (σ : var_name → var_name)
  (F : formula)
  (h1 : admits_fun σ F) :
  holds D I (V ∘ σ) F ↔
    holds D I V (fast_replace_free_fun σ F) :=
begin
  apply substitution_fun_theorem_aux I (V ∘ σ) V σ σ ∅ F h1,
  {
    simp only [finset.not_mem_empty, not_false_iff, false_or, eq_self_iff_true, forall_const],
  },
  {
    simp only [finset.not_mem_empty, is_empty.forall_iff, forall_const],
  },
  {
    simp only [finset.not_mem_empty, not_false_iff, eq_self_iff_true, forall_const],
  },
end


theorem substitution_fun_valid
  (σ : var_name → var_name)
  (F : formula)
  (h1 : admits_fun σ F)
  (h2 : F.is_valid) :
  (fast_replace_free_fun σ F).is_valid :=
begin
  unfold formula.is_valid at h2,

  unfold formula.is_valid,
  intros D I V,
  rewrite <- substitution_fun_theorem I V σ F h1,
  exact h2 D I (V ∘ σ),
end


end fol
