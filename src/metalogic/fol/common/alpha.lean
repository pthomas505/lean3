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
| ((a, b) :: tl) x y :=
    if x = a
    then y = b
    else ¬ y = b ∧ is_alpha_eqv_var tl x y
-- (x = a ∧ y = b) ∨ (¬ (x = a ∧ y = b) ∧ is_alpha_eqv_var tl x y


@[derive decidable]
def is_alpha_eqv_var_list (σ : list (var_name × var_name)) : list var_name → list var_name → bool

| [] [] := tt

| (x_hd :: x_tl) (y_hd :: y_tl) := is_alpha_eqv_var σ x_hd y_hd ∧ (is_alpha_eqv_var_list x_tl y_tl)

| _ _ := ff


@[derive decidable]
def is_alpha_eqv :
  list (var_name × var_name) → formula → formula → bool

| σ true_ true_ := tt

| σ (pred_ X xs) (pred_ Y ys) :=
  X = Y ∧ is_alpha_eqv_var_list σ xs ys

| σ (not_ phi) (not_ phi') := is_alpha_eqv σ phi phi'

| σ (imp_ phi psi) (imp_ phi' psi') := is_alpha_eqv σ phi phi' ∧ is_alpha_eqv σ psi psi'

| σ (forall_ x phi) (forall_ x' phi') := is_alpha_eqv ((x, x') :: σ) phi phi'

| _ _ _ := ff


example
  (D : Type)
  (I : interpretation D)
  (V : valuation D)
  (F F' : formula)
  (h1 : is_alpha_eqv [] F F') :
  holds D I V F ↔ holds D I V F' :=
begin
  induction F generalizing F' V,
  case fol.formula.true_ : F' V h1
  {
    cases F',
    case fol.formula.true_
    {
      unfold holds,
    },
    case [pred_, not_, imp_, forall_]
    {
      all_goals
      {
        unfold is_alpha_eqv at h1,
        contradiction,
      },
    },
  },
  case fol.formula.pred_ : X xs F' V h1
  {
    cases F',
    case fol.formula.pred_ : Y ys
    {
      unfold is_alpha_eqv at h1,
      simp only [bool.of_to_bool_iff] at h1,
      cases h1,

      subst h1_left,
      unfold holds,
      congr' 2,
      induction xs generalizing ys,
      case list.nil : ys h1_right
      {
        cases ys,
        case list.nil
        {
          refl,
        },
        case list.cons : ys_hd ys_tl
        {
          unfold is_alpha_eqv_var_list at h1_right,
          contradiction,
        },
      },
      case list.cons : xs_hd xs_tl xs_ih ys h1_right
      {
        cases ys,
        case list.nil
        {
          unfold is_alpha_eqv_var_list at h1_right,
          contradiction,
        },
        case list.cons : ys_hd ys_tl
        {
          unfold is_alpha_eqv_var_list at h1_right,
          squeeze_simp at h1_right,
          cases h1_right,
          unfold is_alpha_eqv_var at h1_right_left,
          simp only [bool.of_to_bool_iff] at h1_right_left,
          subst h1_right_left,

          simp only [list.map, eq_self_iff_true, true_and],
          apply xs_ih,
          exact h1_right_right,
        },
      },
    },
    case [true_, not_, imp_, forall_]
    {
      all_goals
      {
        unfold is_alpha_eqv at h1,
        contradiction,
      },
    },
  },
  case fol.formula.not_ : phi phi_ih F' V h1
  {
    cases F',
    case fol.formula.not_ : phi'
    {
      unfold is_alpha_eqv at h1,

      unfold holds,
      apply not_congr,
      apply phi_ih,
      exact h1,
    },
    case [true_, pred_, imp_, forall_]
    {
      all_goals
      {
        unfold is_alpha_eqv at h1,
        contradiction,
      },
    },
  },
  case fol.formula.imp_ : phi psi phi_ih psi_ih F' V h1
  {
    induction F',
    case fol.formula.imp_ : phi' psi' phi'_ih psi'_ih
    {
      unfold is_alpha_eqv at h1,
      squeeze_simp at h1,
      cases h1,

      unfold holds,
      apply imp_congr,
      {
        apply phi_ih,
        exact h1_left,
      },
      {
        apply psi_ih,
        exact h1_right,
      }
    },
    case [true_, pred_, not_, forall_]
    {
      all_goals
      {
        unfold is_alpha_eqv at h1,
        contradiction,
      },
    },
  },
  case fol.formula.forall_ : F_ᾰ F_ᾰ_1 F_ih F' V h1
  { admit },
end


#lint

end fol
