import metalogic.fol.aux.misc_list
import metalogic.fol.aux.function_update_ite
import metalogic.fol.common.subst_fun.admits_multiple

import data.finset


set_option pp.parens true


namespace fol

open formula


-- multiple

/--
  The recursive simultaneous uniform substitution of all of the predicate variables in a formula.
-/
def replace_pred_fun
  (τ : pred_name → ℕ → list var_name × formula) : formula → formula
| true_ := true_
| (pred_ P ts) :=
  if ts.length = (τ P ts.length).fst.length
  then
  fast_replace_free_fun
    (function.update_list_ite id (τ P ts.length).fst ts) (τ P ts.length).snd
  else
  pred_ P ts
| (not_ phi) := not_ (replace_pred_fun phi)
| (imp_ phi psi) := imp_ (replace_pred_fun phi) (replace_pred_fun psi)
| (forall_ x phi) := forall_ x (replace_pred_fun phi)


@[derive decidable]
def admits_pred_fun_aux (τ : pred_name → ℕ → list var_name × formula) :
  finset var_name → formula → bool
| _ true_ := tt
| binders (pred_ P ts) :=
  (admits_fun (function.update_list_ite id (τ P ts.length).fst ts) (τ P ts.length).snd) ∧
 (∀ (x : var_name), x ∈ binders → ¬ (is_free_in x (τ P ts.length).snd ∧ x ∉ (τ P ts.length).fst)) ∧
  ts.length = (τ P ts.length).fst.length
| binders (not_ phi) := admits_pred_fun_aux binders phi
| binders (imp_ phi psi) := admits_pred_fun_aux binders phi ∧ admits_pred_fun_aux binders psi
| binders (forall_ x phi) := admits_pred_fun_aux (binders ∪ {x}) phi


lemma pred_sub_aux
  (D : Type)
  (I : interpretation D)
  (V V' : valuation D)
  (τ : pred_name → ℕ → list var_name × formula)
  (binders : finset var_name)
  (F : formula)
  (h1 : admits_pred_fun_aux τ binders F)
  (h2 : ∀ (x : var_name), x ∉ binders → V x = V' x) :
  holds
    D
    ⟨
      I.nonempty,
      fun (P : pred_name) (ds : list D),
      if ds.length = (τ P ds.length).fst.length
      then holds D I (function.update_list_ite V' (τ P ds.length).fst ds) (τ P ds.length).snd
      else I.pred P ds
    ⟩
    V F ↔
    holds D I V (replace_pred_fun τ F) :=
begin
  induction F generalizing binders V,
  case formula.true_ : binders V h1 h2
  {
    unfold replace_pred_fun,
    unfold holds,
  },
  case formula.pred_ : X xs binders V h1 h2
  {
    unfold admits_pred_fun_aux at h1,
    simp only [not_and, not_not, bool.of_to_bool_iff] at h1,
    cases h1,
    cases h1_right,

    obtain s1 := substitution_fun_theorem I V (function.update_list_ite id (τ X xs.length).fst xs) (τ X xs.length).snd h1_left,
    simp only [function.update_list_ite_comp] at s1,
    simp only [function.comp.right_id] at s1,

    have s2 : holds D I (function.update_list_ite V (τ X xs.length).fst (list.map V xs)) (τ X xs.length).snd ↔ holds D I (function.update_list_ite V' (τ X xs.length).fst (list.map V xs)) (τ X xs.length).snd,
    {
      apply holds_congr_var,

      intros v a1,
      by_cases c1 : v ∈ (τ X xs.length).fst,
      {
        apply function.update_list_ite_mem_eq_len V V' v (τ X xs.length).fst (list.map V xs) c1,
        simp only [list.length_map],
        symmetry,
        exact h1_right_right,
      },
      {
        by_cases c2 : v ∈ binders,
        {
          specialize h1_right_left v c2 a1,
          contradiction,
        },
        {
          specialize h2 v c2,
          apply function.update_list_ite_mem',
          exact h2,
        },
      },
    },

    simp only [s2] at s1,
    clear s2,

    unfold holds,
    unfold replace_pred_fun,
    simp only [list.length_map],
    split_ifs,
    exact s1,
  },
  case formula.not_ : phi phi_ih binders V h1 h2
  {
    unfold admits_pred_fun_aux at h1,

    unfold replace_pred_fun,
    unfold holds,
    apply not_congr,
    exact phi_ih binders V h1 h2,
  },
  case formula.imp_ : phi psi phi_ih psi_ih binders V h1 h2
  {
    unfold admits_pred_fun_aux at h1,
    simp only [bool.of_to_bool_iff] at h1,
    cases h1,

    unfold replace_pred_fun,
    unfold holds,
    apply imp_congr,
    {
      exact phi_ih binders V h1_left h2,
    },
    {
      exact psi_ih binders V h1_right h2,
    },
  },
  case formula.forall_ : x phi phi_ih binders V h1 h2
  {
    unfold admits_pred_fun_aux at h1,

    unfold replace_pred_fun,
    unfold holds,
    apply forall_congr,
    intros d,
    apply phi_ih (binders ∪ {x}) (function.update_ite V x d) h1,
    intros v a1,
    unfold function.update_ite,
    simp only [finset.mem_union, finset.mem_singleton] at a1,
    push_neg at a1,
    cases a1,
    simp only [if_neg a1_right],
    exact h2 v a1_left,
  },
end


theorem pred_sub_valid
  (phi : formula)
  (τ : pred_name → ℕ → list var_name × formula)
  (h1 : admits_pred_fun_aux τ ∅ phi)
  (h2 : phi.is_valid) :
  (replace_pred_fun τ phi).is_valid :=
begin
  unfold formula.is_valid at h2,

  unfold formula.is_valid,
  intros D I V,

  obtain s1 := pred_sub_aux D I V V τ ∅ phi h1,
  simp only [eq_self_iff_true, forall_const] at s1,

  rewrite <- s1,
  apply h2,
end


#lint

end fol
