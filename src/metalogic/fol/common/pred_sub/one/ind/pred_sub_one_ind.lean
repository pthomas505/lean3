import metalogic.fol.aux.misc_list
import metalogic.fol.aux.function_update_ite
import metalogic.fol.common.semantics
import metalogic.fol.common.binders

import metalogic.fol.common.subst_fun.admits_multiple

import data.finset


set_option pp.parens true


namespace fol

open formula



/--
  The inductive simultaneous uniform substitution of a single predicate variable in a formula.

  is_pred_sub A P zs H B := The formula A is said to be transformed into the formula B by a substitution of H* for P z₁ ... zₙ, abbreviated: Sub A (P zⁿ / H*) B, iff B is obtained from A upon replacing in A each occurrence of a derivative of the name form P z₁ ... zₙ by the corresponding derivative of the substituend H*, provided that: (i) P does not occur in a component formula (∀ x A₁) of A if x is a parameter of H*, and (ii) the name variable zₖ, k = 1, ..., n, is not free in a component formula (∀ x H) of H* if P t₁ ... tₙ occurs in A with x occurring in tₖ. If conditions (i) and (ii) are not satisfied, then the indicated substitution for predicate variables is left undefined.
-/
inductive is_pred_sub (P : pred_name) (zs : list var_name) (H : formula) : formula → formula → Prop

| true_ :
  is_pred_sub true_ true_

/-
  If A is an atomic formula not containing P then Sub A (P zⁿ / H*) A.
-/
| pred_not_occurs_in
  (X : pred_name) (ts : list var_name) :
  ¬ (X = P ∧ ts.length = zs.length) →
  is_pred_sub (pred_ X ts) (pred_ X ts)

  /-
  If A = P t₁ ... tₙ and Sf H* (zⁿ / tⁿ) B, then Sub A (P zⁿ / H*) B.

  Sf H* (zⁿ / tⁿ) B :=
    admits_fun (function.update_list_ite id zs.to_list ts.to_list) H* ∧ 
    fast_replace_free_fun (function.update_list_ite id zs.to_list ts.to_list) H* = B
  -/
| pred_occurs_in
  (X : pred_name) (ts : list var_name) :
  X = P ∧ ts.length = zs.length →
  admits_fun (function.update_list_ite id zs ts) H →
  is_pred_sub (pred_ P ts) (fast_replace_free_fun (function.update_list_ite id zs ts) H)

/-
  If A = (¬ A₁) and Sub A₁ (P zⁿ / H*) B₁, then Sub A (P zⁿ / H*) (¬ B₁).
-/
| not_
  (phi : formula)
  (phi' : formula) :
  is_pred_sub phi phi' →
  is_pred_sub phi.not_ phi'.not_

/-
  If A = (A₁ → A₂), Sub A₁ (P zⁿ / H*) B₁, and Sub A₂ (P zⁿ / H*) B₂, then Sub A (P zⁿ / H*) (B₁ → B₁).
-/
| imp_
  (phi psi : formula)
  (phi' psi' : formula) :
  is_pred_sub phi phi' →
  is_pred_sub psi psi' →
  is_pred_sub (phi.imp_ psi) (phi'.imp_ psi')

/-
  If A = (∀ x A₁) and P does not occur in A then Sub A (P zⁿ / H*) A.

  If A = (∀ x A₁), P occurs in A, x is not free in H*, and Sub A₁ (P zⁿ / H*) B₁, then Sub A (P zⁿ / H*) (∀ x B₁).
-/
| forall_
  (x : var_name)
  (phi : formula)
  (phi' : formula) :
  ¬ is_free_in x H →
  is_pred_sub phi phi' →
  is_pred_sub (forall_ x phi) (forall_ x phi')


theorem is_pred_sub_theorem
  (D : Type)
  (I J : interpretation D)
  (V : valuation D)
  (A : formula)
  (P : pred_name)
  (zs : list var_name)
  (H : formula)
  (B : formula)
  (h1 : is_pred_sub P zs H A B)
  (h2 : ∀ (Q : pred_name) (ds : list D), (Q = P ∧ ds.length = zs.length) → (holds D I (function.update_list_ite V zs ds) H ↔ J.pred P ds))
  (h3 : ∀ (Q : pred_name) (ds : list D), ¬ (Q = P ∧ ds.length = zs.length) → (I.pred Q ds ↔ J.pred Q ds)) :
  holds D I V B ↔ holds D J V A :=
begin
  induction h1 generalizing V,
  case is_pred_sub.true_ : V h2
  {
    unfold holds,
  },
  case is_pred_sub.pred_not_occurs_in : h1_X h1_ts h1_1 V h2
  {
    simp only [not_and] at h1_1,

    apply coincidence_theorem,
    unfold coincide,
    split,
    {
      unfold pred.occurs_in,
      intros X ds a1,
      simp only [bool.of_to_bool_iff] at a1,
      cases a1,
      subst a1_left,
      apply h3,
      simp only [not_and],
      intros a2,
      subst a2,
      simp only [eq_self_iff_true, forall_true_left] at h1_1,
      intros contra,
      apply h1_1,
      exact eq.trans a1_right contra,
    },
    {
      simp only [eq_self_iff_true, implies_true_iff],
    }
  },
  case is_pred_sub.pred_occurs_in : h1_X h1_ts h1_1 h1_2 V h2
  {
    obtain s1 := substitution_fun_theorem I V (function.update_list_ite id zs h1_ts) H h1_2,

    obtain s2 := function.update_list_ite_comp id V zs h1_ts,

    simp only [s2] at s1,
    simp only [function.comp.right_id] at s1,

    unfold holds,
    specialize h2 h1_X (list.map V h1_ts),
    simp only [s1] at h2,
    apply h2,
    {
      simp only [list.length_map],
      exact h1_1,
    },
  },
  case is_pred_sub.not_ : h1_phi h1_phi' h1_1 h1_ih V h2
  {
    unfold holds,
    apply not_congr,
    exact h1_ih V h2,
  },
  case is_pred_sub.imp_ : h1_phi h1_psi h1_phi' h1_psi' h1_1 h1_2 h1_ih_1 h1_ih_2 V h2
  {
    unfold holds,
    apply imp_congr,
    {
      exact h1_ih_1 V h2,
    },
    {
      exact h1_ih_2 V h2,
    },
  },
  case is_pred_sub.forall_ : h1_x h1_phi h1_phi' h1_1 h1_2 h1_ih V h2
  {
    unfold holds,
    apply forall_congr,
    intros d,
    apply h1_ih,
    intros Q ds a1,
    specialize h2 Q ds a1,

    have s1 : holds D I (function.update_list_ite (function.update_ite V h1_x d) zs ds) H ↔ holds D I (function.update_list_ite V zs ds) H,
    {
      apply coincidence_theorem,
      unfold coincide,
      split,
      {
        simp only [eq_iff_iff, iff_self, implies_true_iff, forall_const],
      },
      {
        intros v a1,
        apply function.update_list_ite_update_ite,
        intros contra,
        subst contra,
        contradiction,
      }
    },

    simp only [h2] at s1,
    exact s1,
  },
end


theorem is_pred_sub_valid
  (phi phi' : formula)
  (P : pred_name)
  (zs : list var_name)
  (H : formula)
  (h1 : is_pred_sub P zs H phi phi')
  (h2 : phi.is_valid) :
  phi'.is_valid :=
begin
  unfold formula.is_valid at h2,

  unfold formula.is_valid,
  intros D I V,

  let J : interpretation D := {
    nonempty := I.nonempty,
    pred := fun (Q : pred_name) (ds : list D), ite (Q = P ∧ ds.length = zs.length) (holds D I (function.update_list_ite V zs ds) H) (I.pred Q ds)
  },

  obtain s1 := is_pred_sub_theorem D I J V phi P zs H phi' h1,
  simp only [eq_self_iff_true, true_and] at s1,

  have s2 : holds D I V phi' ↔ holds D J V phi,
  {
    apply s1,
    {
      intros Q ds a1,
      cases a1,
      simp only [if_pos a1_right],
    },
    {
      intros Q ds a1,
      simp only [if_neg a1],
    },
  },

  simp only [s2],
  apply h2,
end


end fol
