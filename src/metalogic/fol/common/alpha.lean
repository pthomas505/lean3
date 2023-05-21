import metalogic.fol.common.sub.one.rec.sub_one_rec_replace_free
import .semantics


set_option pp.parens true


namespace fol

open formula


inductive alpha_eqv : formula → formula → Prop

| rename_
  (phi : formula) (x y : var_name) :
  ¬ is_free_in y phi →
  ¬ is_bound_in y phi →
  alpha_eqv (forall_ x phi) (forall_ y (fast_replace_free x y phi))

| compat_not_
  (phi phi' : formula) :
  alpha_eqv phi phi' →
  alpha_eqv (not_ phi) (not_ phi')

| compat_imp_
  (phi phi' psi psi' : formula) :
  alpha_eqv phi phi' →
  alpha_eqv psi psi' →
  alpha_eqv (imp_ phi psi) (imp_ phi' psi')

| compat_forall_
  (phi phi' : formula) (x : var_name) :
  alpha_eqv phi phi' →
  alpha_eqv (forall_ x phi) (forall_ x phi')

| refl_
  (phi : formula) :
  alpha_eqv phi phi

| symm_
  (phi phi' : formula) :
  alpha_eqv phi phi' →
  alpha_eqv phi' phi

| trans_
  (phi phi' phi'' : formula) :
  alpha_eqv phi phi' →
  alpha_eqv phi' phi'' →
  alpha_eqv phi phi''


lemma replace_empty_holds
  (D : Type)
  (I : interpretation D)
  (V : valuation D)
  (u v : var_name)
  (F : formula)
  (a : D)
  (h1 : ¬ is_free_in v F)
  (h2 : ¬ is_bound_in v F) :
  holds D I (function.update_ite V u a) F ↔
    holds D I (function.update_ite V v a) (fast_replace_free u v F) :=
begin
  induction F generalizing V,
  case fol.formula.true_ : V
  {
    unfold fast_replace_free,
    unfold holds,
  },
  case fol.formula.pred_ : X xs V
  {
    unfold is_free_in at h1,
    simp only [list.mem_to_finset, bool.of_to_bool_iff] at h1,

    unfold fast_replace_free,
    unfold holds,
    congr' 2,
    simp only [list.map_map],
    simp only [list.map_eq_map_iff],
    intros v a1,
    simp only [function.comp_app],
    unfold function.update_ite,
    split_ifs,
    {
      refl,
    },
    {
      subst h_1,
      contradiction,
    },
    {
      refl,
    }
  },
  case fol.formula.not_ : phi phi_ih V
  {
    unfold is_free_in at h1,

    unfold is_bound_in at h2,

    unfold fast_replace_free,
    unfold holds,
    apply not_congr,
    exact phi_ih h1 h2 V,
  },
  case fol.formula.imp_ : phi psi phi_ih psi_ih V
  {
    unfold is_free_in at h1,
    simp only [bool.of_to_bool_iff] at h1,
    push_neg at h1,
    cases h1,

    unfold is_bound_in at h2,
    simp only [bool.of_to_bool_iff] at h2,
    push_neg at h2,
    cases h2,

    unfold fast_replace_free,
    unfold holds,
    apply imp_congr,
    {
      exact phi_ih h1_left h2_left V,
    },
    {
      exact psi_ih h1_right h2_right V,
    }
  },
  case fol.formula.forall_ : x phi phi_ih V
  {
    unfold is_free_in at h1,
    simp only [bool.of_to_bool_iff, not_and] at h1,

    unfold is_bound_in at h2,
    simp only [bool.of_to_bool_iff] at h2,
    push_neg at h2,
    simp only [ne.def] at h2,
    cases h2,

    unfold fast_replace_free,
    split_ifs,
    {
      subst h,
      apply holds_congr_var,
      intros x a1,
      unfold is_free_in at a1,
      simp only [bool.of_to_bool_iff] at a1,
      cases a1,
      unfold function.update_ite,
      simp only [if_neg a1_left],
      split_ifs,
      {
        subst h,
        specialize h1 a1_left,
        contradiction,
      },
      {
        refl,
      }
    },
    {
      unfold holds,
      apply forall_congr,
      intros d,
      specialize h1 h2_left,
      simp only [function.update_ite_comm V v x d a h2_left],
      simp only [function.update_ite_comm V u x d a h],
      apply phi_ih h1 h2_right,
    }
  },
end


theorem holds_iff_alpha_eqv_holds
  (D : Type)
  (I : interpretation D)
  (V : valuation D)
  (F F' : formula)
  (h1 : alpha_eqv F F') :
  holds D I V F ↔ holds D I V F' :=
begin
  induction h1 generalizing V,
  case fol.alpha_eqv.rename_ : h1_phi h1_x h1_y h1_1 h1_2 V
  {
    unfold holds,
    apply forall_congr,
    intros d,
    exact replace_empty_holds D I V h1_x h1_y h1_phi d h1_1 h1_2,
  },
  case fol.alpha_eqv.compat_not_ : h1_phi h1_phi' h1_1 h1_ih V
  { admit },
  case fol.alpha_eqv.compat_imp_ : h1_phi h1_phi' h1_psi h1_psi' h1_ᾰ h1_ᾰ_1 h1_ih_ᾰ h1_ih_ᾰ_1 V
  { admit },
  case fol.alpha_eqv.compat_forall_ : h1_phi h1_psi h1_x h1_ᾰ h1_ih V
  { admit },
  case fol.alpha_eqv.refl_ : h1 V
  { admit },
  case fol.alpha_eqv.symm_ : h1_phi h1_phi' h1_ᾰ h1_ih V
  { admit },
  case fol.alpha_eqv.trans_ : h1_phi h1_phi' h1_phi'' h1_ᾰ h1_ᾰ_1 h1_ih_ᾰ h1_ih_ᾰ_1 V
  { admit },
end


@[derive decidable]
def is_alpha_eqv_var : list (var_name × var_name) → var_name → var_name → bool

| [] x y := x = y

| (hd :: tl) x y :=
  (x = hd.fst ∧ y = hd.snd) ∨
    ((¬ x = hd.fst ∧ ¬ y = hd.snd) ∧ is_alpha_eqv_var tl x y)

/-
    if x = hd.fst
    then y = hd.snd
    else ¬ y = hd.snd ∧ is_alpha_eqv_var tl x y
-/


@[derive decidable]
def is_alpha_eqv_var_list (binders : list (var_name × var_name)) : list var_name → list var_name → bool

| [] [] := tt

| (x_hd :: x_tl) (y_hd :: y_tl) := is_alpha_eqv_var binders x_hd y_hd ∧ (is_alpha_eqv_var_list x_tl y_tl)

| _ _ := ff


@[derive decidable]
def is_alpha_eqv :
  list (var_name × var_name) → formula → formula → bool

| binders true_ true_ := tt

| binders (pred_ X xs) (pred_ Y ys) :=
  X = Y ∧ is_alpha_eqv_var_list binders xs ys

| binders (not_ phi) (not_ phi') := is_alpha_eqv binders phi phi'

| binders (imp_ phi psi) (imp_ phi' psi') := is_alpha_eqv binders phi phi' ∧ is_alpha_eqv binders psi psi'

| binders (forall_ x phi) (forall_ x' phi') := is_alpha_eqv ((x, x') :: binders) phi phi'

| _ _ _ := ff


example
  (D : Type)
  (I : interpretation D)
  (V : valuation D)
  (F F' : formula)
  (h1 : is_alpha_eqv list.nil F F') :
  holds D I V F ↔ holds D I V F' :=
begin
  induction F generalizing F',
  case fol.formula.true_ : F' h1
  { admit },
  case fol.formula.pred_ : F_ᾰ F_ᾰ_1 F' h1
  { admit },
  case fol.formula.not_ : F_ᾰ F_ih F' h1
  { admit },
  case fol.formula.imp_ : F_ᾰ F_ᾰ_1 F_ih_ᾰ F_ih_ᾰ_1 F' h1
  { admit },
  case fol.formula.forall_ : x phi phi_ih F' h1
  {
    cases F',
    case fol.formula.true_
    { admit },
    case fol.formula.pred_ : F'_ᾰ F'_ᾰ_1
    { admit },
    case fol.formula.not_ : F'
    { admit },
    case fol.formula.imp_ : F'_ᾰ F'_ᾰ_1
    { admit },
    case fol.formula.forall_ : x' phi'
    {
      unfold is_alpha_eqv at h1,

      unfold holds,
      apply forall_congr,
      intros d,

      sorry
    },
  },
end


#lint

end fol
