import metalogic.fol.common.sub.all.rec.sub_all_rec_admits


set_option pp.parens true


namespace fol

open formula


-- predicate substitution

-- single

-- https://math.stackexchange.com/a/1374989

/--
  The recursive simultaneous uniform substitution of a single predicate variable in a formula.
-/
def replace_pred
  (P : pred_name) (zs : list var_name) (H : formula) : formula → formula
| true_ := true_
| (pred_ X ts) :=
  if X = P ∧ ts.length = zs.length
  then
  fast_replace_free_fun
    (function.update_list_ite id zs ts) H
  else pred_ X ts
| (not_ phi) := not_ (replace_pred phi)
| (imp_ phi psi) := imp_ (replace_pred phi) (replace_pred psi)
| (forall_ x phi) := forall_ x (replace_pred phi)


@[derive decidable]
def admits_pred_aux (P : pred_name) (zs : list var_name) (H : formula) : finset var_name → formula → bool
| _ true_ := tt
| binders (pred_ X ts) :=
  if X = P ∧ ts.length = zs.length
  then
  (admits_fun (function.update_list_ite id zs ts) H) ∧

  /-
    Suppose F is the formula that the predicate X ts occurs in.
    Ensures that the free variables in H that are not being replaced by a variable in ts do not become bound variables in F. The bound variables in F are in the 'binders' set.
    The zs are the free variables in H that are being replaced by the variables in ts.
   (is_free_in x H ∧ x ∉ zs) := x is a free variable in H that is not being replaced by a variable in ts.
  -/
  (∀ (x : var_name), x ∈ binders → ¬ (is_free_in x H ∧ x ∉ zs))
  else true
| binders (not_ phi) := admits_pred_aux binders phi
| binders (imp_ phi psi) := admits_pred_aux binders phi ∧ admits_pred_aux binders psi
| binders (forall_ x phi) := admits_pred_aux (binders ∪ {x}) phi


lemma pred_sub_single_aux
  (D : Type)
  (I : interpretation D)
  (V V' : valuation D)
  (F : formula)
  (P : pred_name)
  (zs : list var_name)
  (H : formula)
  (binders : finset var_name)
  (h1 : admits_pred_aux P zs H binders F)
  (h2 : ∀ (x : var_name), x ∉ binders → V x = V' x) :
  holds
    D
    ⟨
      I.nonempty,
      fun (Q : pred_name) (ds : list D),
      if Q = P ∧ ds.length = zs.length
      then holds D I (function.update_list_ite V' zs ds) H
      else I.pred Q ds
    ⟩
    V F ↔
    holds D I V (replace_pred P zs H F) :=
begin
  induction F generalizing binders V,
  case formula.true_ : binders V h1 h2
  {
    unfold replace_pred,
    unfold holds,
  },
  case formula.pred_ : X xs binders V h1 h2
  {
    unfold admits_pred_aux at h1,

    unfold replace_pred,
    unfold holds,
    simp only [list.length_map],

    split_ifs at h1,
    {
      simp only [not_and, not_not, bool.of_to_bool_iff] at h1,
      cases h1,
      unfold admits_fun at h1_left,

      split_ifs,

      obtain s1 := substitution_fun_theorem I V (function.update_list_ite id zs xs) H h1_left,
      simp only [function.update_list_ite_comp] at s1,
      simp only [function.comp.right_id] at s1,

      have s2 : holds D I (function.update_list_ite V zs (list.map V xs)) H ↔ holds D I (function.update_list_ite V' zs (list.map V xs)) H,
      {
        apply holds_congr_var,
        intros v a1,
        by_cases c1 : v ∈ zs,
        {
          specialize h2 v,
          apply function.update_list_ite_mem_eq_len V V' v zs (list.map V xs) c1,
          cases h,
          simp only [list.length_map],
          symmetry,
          exact h_right,
        },
        {
          by_cases c2 : v ∈ binders,
          {
            specialize h1_right v c2 a1,
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
      exact s1,
    },
    {
      split_ifs,
      unfold holds,
    }
  },
  case formula.not_ : phi phi_ih binders V h1 h2
  {
    unfold admits_pred_aux at h1,

    unfold replace_pred,
    unfold holds,
    apply not_congr,
    exact phi_ih binders V h1 h2,
  },
  case formula.imp_ : phi psi phi_ih psi_ih binders V h1 h2
  {
    unfold admits_pred_aux at h1,
    simp only [bool.of_to_bool_iff] at h1,
    cases h1,

    unfold replace_pred,
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
    unfold admits_pred_aux at h1,

    unfold replace_pred,
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


theorem pred_sub_single_valid
  (phi : formula)
  (P : pred_name)
  (zs : list var_name)
  (H : formula)
  (h1 : admits_pred_aux P zs H ∅ phi)
  (h2 : phi.is_valid) :
  (replace_pred P zs H phi).is_valid :=
begin
  unfold formula.is_valid at h2,

  unfold formula.is_valid,
  intros D I V,

  obtain s1 := pred_sub_single_aux D I V V phi P zs H ∅ h1,
  simp only [eq_self_iff_true, forall_const] at s1,

  rewrite <- s1,
  apply h2,
end


#lint

end fol
