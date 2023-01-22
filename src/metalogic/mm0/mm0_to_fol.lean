import metalogic.mm0.mm0
import metalogic.mm0.fol


/-
noncomputable
def mm0.formula.to_fol_formula
  (M : mm0.meta_var_name → fol.formula) :
  mm0.env → mm0.formula → fol.formula
| E (mm0.formula.meta_var_ X) := M X
| E (mm0.formula.false_) := fol.formula.false_
| E (mm0.formula.pred_ name args) := fol.formula.pred_ name args
| E (mm0.formula.not_ φ) :=
    fol.formula.not_ (mm0.formula.to_fol_formula E φ)
| E (mm0.formula.imp_ φ ψ) :=
    fol.formula.imp_ (mm0.formula.to_fol_formula E φ) (mm0.formula.to_fol_formula E ψ)
| E (mm0.formula.eq_ x y) := fol.formula.eq_ x y
| E (mm0.formula.forall_ x φ) :=
    fol.formula.forall_ x (mm0.formula.to_fol_formula E φ)
| [] (mm0.formula.def_ _ _) := fol.formula.false_
| (d :: E) (mm0.formula.def_ name args) :=
  by classical; exact
  if h : name = d.name ∧ ∃ (σ : mm0.instantiation), args = d.args.map σ.1
  then
    let σ := classical.some h.right in
    mm0.formula.to_fol_formula E (d.q.subst σ mm0.formula.meta_var_)
  else mm0.formula.to_fol_formula E (mm0.formula.def_ name args)
-/


noncomputable
def mm0.formula.to_fol_formula'
  (M : mm0.meta_var_name → fol.formula)
  (mm0_formula_to_fol_formula : mm0.formula → fol.formula)
  (d : option mm0.definition_) :
  mm0.formula → fol.formula
| (mm0.formula.meta_var_ X) := M X
| (mm0.formula.false_) := fol.formula.false_
| (mm0.formula.pred_ name args) := fol.formula.pred_ name args
| (mm0.formula.not_ φ) := fol.formula.not_ φ.to_fol_formula'
| (mm0.formula.imp_ φ ψ) := fol.formula.imp_ φ.to_fol_formula' ψ.to_fol_formula'
| (mm0.formula.eq_ x y) := fol.formula.eq_ x y
| (mm0.formula.forall_ x φ) := fol.formula.forall_ x φ.to_fol_formula'
| (mm0.formula.def_ name args) :=
    option.elim
      fol.formula.false_
      (
        fun (d : mm0.definition_),
          by classical; exact
          if h : name = d.name ∧ ∃ (σ : mm0.instantiation), args = d.args.map σ.1
          then
            let σ := classical.some h.right in
            mm0_formula_to_fol_formula (d.q.subst σ mm0.formula.meta_var_)
          else
            mm0_formula_to_fol_formula (mm0.formula.def_ name args)
      )
      d


noncomputable
def mm0.formula.to_fol_formula
  (M : mm0.meta_var_name → fol.formula) :
  mm0.env → mm0.formula → fol.formula
| [] := mm0.formula.to_fol_formula' M (fun _, fol.formula.false_) option.none
| (d :: E) := mm0.formula.to_fol_formula' M (mm0.formula.to_fol_formula E) (option.some d)


@[simp]
lemma meta_var_to_fol_formula
  (M : mm0.meta_var_name → fol.formula)
  (E : mm0.env)
  (X : mm0.meta_var_name) :
  mm0.formula.to_fol_formula M E (mm0.formula.meta_var_ X) =
    M X := by {cases E; refl}


@[simp]
lemma false_to_fol_formula
  (M : mm0.meta_var_name → fol.formula)
  (E : mm0.env) :
  mm0.formula.to_fol_formula M E mm0.formula.false_ =
    fol.formula.false_ := by {cases E; refl}


@[simp]
lemma pred_to_fol_formula
  (M : mm0.meta_var_name → fol.formula)
  (E : mm0.env)
  (name : mm0.pred_name)
  (args : list mm0.var_name) :
  mm0.formula.to_fol_formula M E (mm0.formula.pred_ name args) =
    fol.formula.pred_ name args := by {cases E; refl}


@[simp]
lemma not_to_fol_formula
  (M : mm0.meta_var_name → fol.formula)
  (E : mm0.env)
  (φ : mm0.formula) :
  mm0.formula.to_fol_formula M E (mm0.formula.not_ φ) =
    fol.formula.not_ (mm0.formula.to_fol_formula M E φ) :=
begin
  cases E,
  case list.nil
  {
    unfold mm0.formula.to_fol_formula,
    unfold mm0.formula.to_fol_formula',
  },
  case list.cons : E_hd E_tl
  {
    unfold mm0.formula.to_fol_formula,
    unfold mm0.formula.to_fol_formula',
  },
end


@[simp]
lemma imp_to_fol_formula
  (M : mm0.meta_var_name → fol.formula)
  (E : mm0.env)
  (φ ψ : mm0.formula) :
  mm0.formula.to_fol_formula M E (mm0.formula.imp_ φ ψ) =
    fol.formula.imp_ (mm0.formula.to_fol_formula M E φ) (mm0.formula.to_fol_formula M E ψ) :=
begin
  cases E,
  case list.nil
  {
    unfold mm0.formula.to_fol_formula,
    unfold mm0.formula.to_fol_formula',
  },
  case list.cons : E_hd E_tl
  {
    unfold mm0.formula.to_fol_formula,
    unfold mm0.formula.to_fol_formula',
  },
end


@[simp]
lemma eq_to_fol_formula
  (M : mm0.meta_var_name → fol.formula)
  (E : mm0.env)
  (x y : mm0.var_name) :
  mm0.formula.to_fol_formula M E (mm0.formula.eq_ x y) =
    fol.formula.eq_ x y := by {cases E; refl}


@[simp]
lemma forall_to_fol_formula
  (M : mm0.meta_var_name → fol.formula)
  (E : mm0.env)
  (x : mm0.var_name)
  (φ : mm0.formula) :
  mm0.formula.to_fol_formula M E (mm0.formula.forall_ x φ) =
    fol.formula.forall_ x (mm0.formula.to_fol_formula M E φ) :=
begin
  cases E,
  case list.nil
  {
    unfold mm0.formula.to_fol_formula,
    unfold mm0.formula.to_fol_formula',
  },
  case list.cons : E_hd E_tl
  {
    unfold mm0.formula.to_fol_formula,
    unfold mm0.formula.to_fol_formula',
  },
end


@[simp]
lemma nil_def_to_fol_formula
  (M : mm0.meta_var_name → fol.formula)
  (name : mm0.pred_name)
  (args : list mm0.var_name) :
  mm0.formula.to_fol_formula M [] (mm0.formula.def_ name args) =
    fol.formula.false_ := by {refl}


@[simp]
lemma not_nil_def_to_fol_formula
  (M : mm0.meta_var_name → fol.formula)
  (d : mm0.definition_)
  (E : mm0.env)
  (name : mm0.pred_name)
  (args : list mm0.var_name) :
  mm0.formula.to_fol_formula M (d :: E) (mm0.formula.def_ name args) =
  by classical; exact
  if h : name = d.name ∧ ∃ (σ : mm0.instantiation), args = d.args.map σ.1
  then
    let σ := classical.some h.right in
    mm0.formula.to_fol_formula M E (d.q.subst σ mm0.formula.meta_var_)
  else mm0.formula.to_fol_formula M E (mm0.formula.def_ name args) :=
begin
  unfold mm0.formula.to_fol_formula,
  unfold mm0.formula.to_fol_formula',
  simp only [option.elim],
end


lemma not_nil_def_to_fol_formula'
  (M : mm0.meta_var_name → fol.formula)
  (d : mm0.definition_)
  (E : mm0.env)
  (name : mm0.def_name)
  (args : list mm0.var_name)
  (h1 : name = d.name ∧ ∃ (σ : mm0.instantiation), args = d.args.map σ.1) :
  ∃ (σ : mm0.instantiation), args = d.args.map σ.1 ∧
  mm0.formula.to_fol_formula M (d :: E) (mm0.formula.def_ name args) =
    mm0.formula.to_fol_formula M E (d.q.subst σ mm0.formula.meta_var_) :=
begin
  let σ := classical.some h1.right,
  have h2 := classical.some_spec h1.right,
  simp only [not_nil_def_to_fol_formula, dif_pos h1],
  exact ⟨σ, h2, rfl⟩,
end


lemma to_fol_formula_no_def
  (name : mm0.def_name)
  (args : list mm0.var_name)
  (M : mm0.meta_var_name → fol.formula)
  (E : mm0.env)
  (h1 : ∀ (d : mm0.definition_), d ∈ E →
    name = d.name →
      ∀ (σ : mm0.instantiation), ¬ args = list.map σ.val d.args) :
  mm0.formula.to_fol_formula M E (mm0.formula.def_ name args)
    = fol.formula.false_ :=
begin
  induction E,
  case list.nil
  {
    simp only [nil_def_to_fol_formula],
  },
  case list.cons : E_hd E_tl E_ih
  {
    simp only [not_nil_def_to_fol_formula],
    split_ifs,
    {
      cases h,
      apply exists.elim h_right,
      intros σ h_right_1,
      dsimp,

      exfalso,
      apply h1 E_hd _ h_left σ h_right_1,
      simp only [list.mem_cons_iff, eq_self_iff_true, true_or],
    },
    {
      apply E_ih,
      intros d a1 a2 contra,
      apply h1,
      {
        simp only [list.mem_cons_iff],
        apply or.intro_right,
        exact a1,
      },
      {
        exact a2,
      }
    }
  },
end


lemma to_fol_formula_env_ext
  (M : mm0.meta_var_name → fol.formula)
  (d : mm0.definition_)
  (E : mm0.env)
  (name : mm0.def_name)
  (args : list mm0.var_name)
  (h1 : ¬((name = d.name) ∧ (∃ (σ : mm0.instantiation), (args = list.map σ.val d.args)))) :
  (mm0.formula.to_fol_formula M (d :: E) (mm0.formula.def_ name args)) =
    (mm0.formula.to_fol_formula M E (mm0.formula.def_ name args)) :=
begin
  simp only [not_nil_def_to_fol_formula, dite_eq_right_iff],
  intros contra,
  contradiction,
end


example
  (M : mm0.meta_var_name → fol.formula)
  (E E' : mm0.env)
  (φ : mm0.formula)
  (h1 : ∃ (E1 : mm0.env), E' = E1 ++ E)
  (h2 : φ.is_meta_var_or_all_def_in_env E)
  (h3 : E'.well_formed) :
  (mm0.formula.to_fol_formula M E φ) =
    (mm0.formula.to_fol_formula M E' φ) :=
begin
  induction E' generalizing φ,
  case list.nil : φ h2
  {
    simp only [list.nil_eq_append_iff, exists_eq_left] at h1,
    rewrite h1,
  },
  case list.cons : E'_hd E'_tl E'_ih φ h2
  {
    induction φ generalizing E'_tl,
    case mm0.formula.meta_var_ : X
    {
      simp only [meta_var_to_fol_formula],
    },
    case mm0.formula.false_
    {
      simp only [false_to_fol_formula],
    },
    case mm0.formula.pred_ : name args
    {
      simp only [pred_to_fol_formula, eq_self_iff_true, and_self],
    },
    case mm0.formula.not_ : φ φ_ih
    {
      unfold mm0.formula.is_meta_var_or_all_def_in_env at h2,

      simp only [not_to_fol_formula],
      apply φ_ih h2,
      {
        intros a1 a2 φ' a3,
        exact E'_ih a1 a2 φ' a3,
      },
      {
        exact h1,
      },
      {
        exact h3,
      }
    },
    case mm0.formula.imp_ : φ ψ φ_ih ψ_ih
    {
      unfold mm0.formula.is_meta_var_or_all_def_in_env at h2,
      cases h2,

      simp only [imp_to_fol_formula],
      split,
      {
        apply φ_ih h2_left,
        {
          intros a1 a2 φ' a3,
          exact E'_ih a1 a2 φ' a3,
        },
        {
          exact h1,
        },
        {
          exact h3,
        }
      },
      {
        apply ψ_ih h2_right,
        {
          intros a1 a2 ψ' a3,
          exact E'_ih a1 a2 ψ' a3,
        },
        {
          exact h1,
        },
        {
          exact h3,
        }
      }
    },
    case mm0.formula.eq_ : x y
    {
      simp only [eq_to_fol_formula, eq_self_iff_true, and_self],
    },
    case mm0.formula.forall_ : x φ φ_ih
    {
      unfold mm0.formula.is_meta_var_or_all_def_in_env at h2,

      simp only [forall_to_fol_formula, eq_self_iff_true, true_and],
      exact φ_ih h2 E'_tl E'_ih h1 h3,
    },
    case mm0.formula.def_ : name args
    {
      apply exists.elim h1,
      intros E1 h1_1,
      cases E1,
      {
        simp only [list.nil_append] at h1_1,
        rewrite <- h1_1,
      },
      {
        simp only [list.cons_append] at h1_1,
        have s1 : ∃ (E1 : mm0.env), (E'_tl = (E1 ++ E)),
        apply exists.intro E1_tl,
        injection h1_1,

        unfold mm0.formula.is_meta_var_or_all_def_in_env at h2,
        apply exists.elim h2,
        intros d h2_1,
        cases h2_1,
        cases h2_1_right,
        clear h2,

        have s2 : d ∈ E'_tl,
        injection h1_1,
        rewrite h_2,
        simp only [list.mem_append],
        apply or.intro_right,
        exact h2_1_left,

        unfold mm0.env.well_formed at h3,
        cases h3,
        cases h3_right,

        specialize h3_left d s2,

        have s3 : ¬ ((name = E'_hd.name) ∧ (∃ (a : mm0.instantiation), (args = list.map (a.val) E'_hd.args))),
        push_neg,
        intros a1 σ contra,
        apply h3_left,
        rewrite <- h2_1_right_left,
        rewrite a1,
        rewrite <- h2_1_right_right,
        rewrite contra,
        symmetry,
        apply list.length_map,

        simp only [subtype.val_eq_coe, not_nil_def_to_fol_formula],
        rewrite dif_neg,
        rewrite E'_ih s1 h3_right_right,
        {
          push_neg at s3,
          unfold mm0.formula.is_meta_var_or_all_def_in_env,
          apply exists.intro d,
          split,
          exact h2_1_left,
          split,
          exact h2_1_right_left,
          exact h2_1_right_right,
        },
        {
          exact s3,
        }
      }
    },
  },
end


lemma to_fol_formula_no_meta_var
  (M M' : mm0.meta_var_name → fol.formula)
  (E : mm0.env)
  (φ : mm0.formula)
  (h1 : φ.meta_var_set = ∅) :
  mm0.formula.to_fol_formula M E φ = mm0.formula.to_fol_formula M' E φ :=
begin
  induction E generalizing φ,
  case list.nil : φ h1
  {
    induction φ,
    case mm0.formula.meta_var_ : X
    {
      unfold mm0.formula.meta_var_set at h1,
      simp only [finset.singleton_ne_empty] at h1,
      contradiction,
    },
    case mm0.formula.false_
    {
      refl,
    },
    case mm0.formula.pred_ : name args
    {
      refl,
    },
    case mm0.formula.not_ : φ φ_ih
    {
      unfold mm0.formula.meta_var_set at h1,
      simp only [not_to_fol_formula],
      exact φ_ih h1,
    },
    case mm0.formula.imp_ : φ ψ φ_ih ψ_ih
    {
      unfold mm0.formula.meta_var_set at h1,
      simp only [finset.union_eq_empty_iff] at h1,
      cases h1,

      simp only [imp_to_fol_formula],
      split,
      {
        exact φ_ih h1_left,
      },
      {
        exact ψ_ih h1_right,
      }
    },
    case mm0.formula.eq_ : x y
    {
      refl,
    },
    case mm0.formula.forall_ : x φ φ_ih
    {
      unfold mm0.formula.meta_var_set at h1,

      simp only [forall_to_fol_formula, eq_self_iff_true, true_and],
      exact φ_ih h1,
    },
    case mm0.formula.def_ : name args
    {
      refl,
    },
  },
  case list.cons : E_hd E_tl E_ih φ h1
  {
    induction φ,
    case mm0.formula.meta_var_ : X
    {
      unfold mm0.formula.meta_var_set at h1,
      simp only [finset.singleton_ne_empty] at h1,
      contradiction,
    },
    case mm0.formula.false_
    {
      refl,
    },
    case mm0.formula.pred_ : name args
    {
      refl,
    },
    case mm0.formula.not_ : φ φ_ih
    {
      unfold mm0.formula.meta_var_set at h1,
      simp only [not_to_fol_formula],
      exact φ_ih h1,
    },
    case mm0.formula.imp_ : φ ψ φ_ih ψ_ih
    {
      unfold mm0.formula.meta_var_set at h1,
      simp only [finset.union_eq_empty_iff] at h1,
      cases h1,

      simp only [imp_to_fol_formula],
      split,
      {
        exact φ_ih h1_left,
      },
      {
        exact ψ_ih h1_right,
      }
    },
    case mm0.formula.eq_ : x y
    {
      refl,
    },
    case mm0.formula.forall_ : x φ φ_ih
    {
      unfold mm0.formula.meta_var_set at h1,

      simp only [forall_to_fol_formula, eq_self_iff_true, true_and],
      exact φ_ih h1,
    },
    case mm0.formula.def_ : name args
    {
      simp only [not_nil_def_to_fol_formula],
      split_ifs,
      {
        apply E_ih,
        apply mm0.subst_no_meta_var,
        apply mm0.no_meta_var_imp_meta_var_set_is_empty E_hd.q E_hd.args E_hd.nf,
      },
      {
        apply E_ih _ h1,
      }
    },
  },
end


def fol.formula.to_mm0_formula : fol.formula → mm0.formula
| (fol.formula.false_) := mm0.formula.false_
| (fol.formula.pred_ name args) := mm0.formula.pred_ name args
| (fol.formula.not_ φ) := mm0.formula.not_ φ.to_mm0_formula
| (fol.formula.imp_ φ ψ) := mm0.formula.imp_ φ.to_mm0_formula ψ.to_mm0_formula
| (fol.formula.eq_ x y) := mm0.formula.eq_ x y
| (fol.formula.forall_ x φ) := mm0.formula.forall_ x φ.to_mm0_formula


example
  (φ : fol.formula)
  (M : mm0.meta_var_name → fol.formula)
  (E : mm0.env):
  mm0.formula.to_fol_formula M E (fol.formula.to_mm0_formula φ) = φ :=
begin
  induction φ,
  case fol.formula.false_
  {
    unfold fol.formula.to_mm0_formula,
    simp only [false_to_fol_formula],
  },
  case fol.formula.pred_ : name args
  {
    unfold fol.formula.to_mm0_formula,
    simp only [pred_to_fol_formula, eq_self_iff_true, and_self],
  },
  case fol.formula.not_ : φ φ_ih
  {
    unfold fol.formula.to_mm0_formula,
    simp only [not_to_fol_formula],
    exact φ_ih,
  },
  case fol.formula.imp_ : φ ψ φ_ih ψ_ih
  {
    unfold fol.formula.to_mm0_formula,
    simp only [imp_to_fol_formula],
    split,
    {
      exact φ_ih,
    },
    {
      exact ψ_ih,
    }
  },
  case fol.formula.eq_ : x y
  {
    unfold fol.formula.to_mm0_formula,
    simp only [eq_to_fol_formula, eq_self_iff_true, and_self],
  },
  case fol.formula.forall_ : x φ φ_ih
  {
    unfold fol.formula.to_mm0_formula,
    simp only [forall_to_fol_formula, eq_self_iff_true, true_and],
    exact φ_ih,
  },
end


lemma fol_not_free_imp_mm0_not_free
  (Γ : list (mm0.var_name × mm0.meta_var_name))
  (v : fol.var_name)
  (φ : fol.formula)
  (h1 : fol.not_free v φ) :
  mm0.not_free Γ v (fol.formula.to_mm0_formula φ) :=
begin
  induction φ,
  case fol.formula.false_
  {
    unfold fol.formula.to_mm0_formula,
  },
  case fol.formula.pred_ : name args
  {
    unfold fol.formula.to_mm0_formula,
    exact h1,
  },
  case fol.formula.not_ : φ φ_ih
  {
    unfold fol.not_free at h1,

    unfold fol.formula.to_mm0_formula,
    exact φ_ih h1,
  },
  case fol.formula.imp_ : φ ψ φ_ih ψ_ih
  {
    unfold fol.not_free at h1,
    cases h1,

    unfold fol.formula.to_mm0_formula,
    unfold mm0.not_free,
    split,
    {
      exact φ_ih h1_left,
    },
    {
      exact ψ_ih h1_right,
    }
  },
  case fol.formula.eq_ : x y
  {
    unfold fol.not_free at h1,
    cases h1,

    unfold fol.formula.to_mm0_formula,
    unfold mm0.not_free,
    split,
    {
      exact h1_left,
    },
    {
      exact h1_right,
    }
  },
  case fol.formula.forall_ : x φ φ_ih
  {
    unfold fol.not_free at h1,

    unfold fol.formula.to_mm0_formula,
    unfold mm0.not_free,
    cases h1,
    {
      apply or.intro_left,
      exact h1,
    },
    {
      apply or.intro_right,
      exact φ_ih h1,
    }
  },
end


lemma mm0_not_free_imp_fol_not_free
  (M : mm0.meta_var_name → fol.formula)
  (Γ : list (mm0.var_name × mm0.meta_var_name))
  (E : mm0.env)
  (v : mm0.var_name)
  (φ : mm0.formula)
  (h1 : mm0.not_free Γ v φ)
  (h2 : ∀ (x : mm0.var_name) (X : mm0.meta_var_name),
    (x, X) ∈ Γ → fol.not_free x (M X)) :
  fol.not_free v (mm0.formula.to_fol_formula M E φ) :=
begin
  induction E generalizing φ,
  case list.nil : φ h1
  {
    induction φ,
    case mm0.formula.meta_var_ : X
    {
      unfold mm0.not_free at h1,
      simp only [meta_var_to_fol_formula],
      exact h2 v X h1,
    },
    case mm0.formula.false_
    {
      simp only [false_to_fol_formula],
    },
    case mm0.formula.pred_ : name args
    {
      simp only [pred_to_fol_formula],
      exact h1,
    },
    case mm0.formula.not_ : φ φ_ih
    {
      unfold mm0.not_free at h1,
      simp only [not_to_fol_formula],
      unfold fol.not_free,
      exact φ_ih h1,
    },
    case mm0.formula.imp_ : φ ψ φ_ih ψ_ih
    {
      unfold mm0.not_free at h1,
      cases h1,
      simp only [imp_to_fol_formula],
      unfold fol.not_free,
      split,
      {
        exact φ_ih h1_left,
      },
      {
        exact ψ_ih h1_right,
      }
    },
    case mm0.formula.eq_ : x y
    {
      unfold mm0.not_free at h1,
      simp only [eq_to_fol_formula],
      unfold fol.not_free,
      exact h1,
    },
    case mm0.formula.forall_ : x φ φ_ih
    {
      unfold mm0.not_free at h1,
      simp only [forall_to_fol_formula],
      unfold fol.not_free,
      cases h1,
      {
        apply or.intro_left,
        exact h1,
      },
      {
        apply or.intro_right,
        exact φ_ih h1,
      }
    },
    case mm0.formula.def_ : name args
    {
      simp only [nil_def_to_fol_formula],
    },
  },
  case list.cons : E_hd E_tl E_ih φ h1
  {
    induction φ,
    case mm0.formula.meta_var_ : X
    {
      unfold mm0.not_free at h1,
      simp only [meta_var_to_fol_formula],
      exact h2 v X h1,
    },
    case mm0.formula.false_
    {
      simp only [false_to_fol_formula],
    },
    case mm0.formula.pred_ : name args
    {
      simp only [pred_to_fol_formula],
      exact h1,
    },
    case mm0.formula.not_ : φ φ_ih
    {
      unfold mm0.not_free at h1,
      simp only [not_to_fol_formula],
      unfold fol.not_free,
      exact φ_ih h1,
    },
    case mm0.formula.imp_ : φ ψ φ_ih ψ_ih
    {
      unfold mm0.not_free at h1,
      cases h1,
      simp only [imp_to_fol_formula],
      unfold fol.not_free,
      split,
      {
        exact φ_ih h1_left,
      },
      {
        exact ψ_ih h1_right,
      }
    },
    case mm0.formula.eq_ : x y
    {
      unfold mm0.not_free at h1,
      simp only [eq_to_fol_formula],
      unfold fol.not_free,
      exact h1,
    },
    case mm0.formula.forall_ : x φ φ_ih
    {
      unfold mm0.not_free at h1,
      simp only [forall_to_fol_formula],
      unfold fol.not_free,
      cases h1,
      {
        apply or.intro_left,
        exact h1,
      },
      {
        apply or.intro_right,
        exact φ_ih h1,
      }
    },
    case mm0.formula.def_ : name args
    {
      simp only [not_nil_def_to_fol_formula],
      split_ifs,
      {
        unfold mm0.not_free at h1,

        cases h,

        apply E_ih,
        apply mm0.all_free_in_list_and_not_in_list_imp_not_free _ (list.map (classical.some h_right).val E_hd.args),
        apply mm0.no_meta_var_and_all_free_in_list_subst,
        exact E_hd.nf,
        rewrite <- classical.some_spec h_right,
        exact h1,
      },
      {
        apply E_ih,
        exact h1,
      }
    },
  },
end


lemma fol_is_proof_forall
  (φ : mm0.formula)
  (x y : fol.var_name)
  (S : list mm0.var_name)
  (M : mm0.meta_var_name → fol.formula)
  (E : mm0.env)
  (σ σ' : mm0.instantiation) :
  fol.is_proof
  ((fol.formula.forall_ x (mm0.formula.to_fol_formula M E (mm0.formula.subst σ mm0.formula.meta_var_ φ))).imp_
  (fol.formula.forall_ y (mm0.formula.to_fol_formula M E (mm0.formula.subst σ' mm0.formula.meta_var_ φ)))) :=
begin
  sorry,
end


lemma proof_eqv_to_fol_formula_subst
  (φ : mm0.formula)
  (l : list mm0.var_name)
  (M : mm0.meta_var_name → fol.formula)
  (E : mm0.env)
  (σ σ' : mm0.instantiation)
  (h1 : φ.no_meta_var_and_all_free_in_list l)
  (h2 : ∀ (x : mm0.var_name), x ∈ l → σ.val x = σ'.val x) :
  fol.proof_eqv
  (mm0.formula.to_fol_formula M E (mm0.formula.subst σ mm0.formula.meta_var_ φ))
  (mm0.formula.to_fol_formula M E (mm0.formula.subst σ' mm0.formula.meta_var_ φ)) :=
begin
  induction φ generalizing l,
  case mm0.formula.meta_var_ : X l h1 h2
  {
    apply fol.proof_eqv_refl,
    unfold mm0.formula.subst,
  },
  case mm0.formula.false_ : l h1 h2
  {
    apply fol.proof_eqv_refl,
    unfold mm0.formula.subst,
  },
  case mm0.formula.pred_ : name args l h1 h2
  {
    apply fol.proof_eqv_refl,

    unfold mm0.formula.no_meta_var_and_all_free_in_list at h1,

    unfold mm0.formula.subst,
    rewrite list.map_congr,
    intros x a1,
    apply h2 x,
    exact h1 a1,
  },
  case mm0.formula.not_ : φ φ_ih l h1 h2
  {
    unfold mm0.formula.no_meta_var_and_all_free_in_list at h1,

    unfold mm0.formula.subst,
    simp only [not_to_fol_formula],

    apply fol.proof_eqv_compat_not,
    exact φ_ih l h1 h2,
  },
  case mm0.formula.imp_ : φ ψ φ_ih ψ_ih l h1 h2
  {
    unfold mm0.formula.no_meta_var_and_all_free_in_list at h1,
    cases h1,

    unfold mm0.formula.subst,
    simp only [imp_to_fol_formula],
    apply fol.proof_eqv_compat_imp,
    {
      exact φ_ih l h1_left h2,
    },
    {
      exact ψ_ih l h1_right h2,
    }
  },
  case mm0.formula.eq_ : x y l h1 h2
  {
    apply fol.proof_eqv_refl,
    unfold mm0.formula.no_meta_var_and_all_free_in_list at h1,
    cases h1,

    unfold mm0.formula.subst,
    congr' 1,
    simp only [eq_to_fol_formula],
    split,
    {
      exact h2 x h1_left,
    },
    {
      exact h2 y h1_right,
    }
  },
  case mm0.formula.forall_ : x φ φ_ih l h1 h2
  {
    unfold mm0.formula.no_meta_var_and_all_free_in_list at h1,

    unfold mm0.formula.subst,
    simp only [forall_to_fol_formula],
    unfold fol.proof_eqv,
    split,
    {
      apply fol_is_proof_forall _ _ _ l,
    },
    {
      apply fol_is_proof_forall _ _ _ l,
    },
  },
  case mm0.formula.def_ : name args l h1 h2
  {
    apply fol.proof_eqv_refl,

    unfold mm0.formula.no_meta_var_and_all_free_in_list at h1,

    unfold mm0.formula.subst,
    rewrite list.map_congr,
    intros x a1,
    apply h2 x,
    exact h1 a1,
  },
end


lemma proof_eqv_subst_to_fol_formula_subst
  (φ : mm0.formula)
  (M : mm0.meta_var_name → fol.formula)
  (E : mm0.env)
  (σ σ_inv : mm0.instantiation)
  (τ : mm0.meta_instantiation)
  (h_inv_left : σ.val ∘ σ_inv.val = id)
  (h_inv_right : σ_inv.val ∘ σ.val = id) :
  fol.proof_eqv
    (mm0.formula.to_fol_formula M E (mm0.formula.subst σ τ φ))
    (fol.formula.subst σ (mm0.formula.to_fol_formula (fol.formula.subst σ_inv ∘ (mm0.formula.to_fol_formula M E ∘ τ)) E φ)) :=
begin
  induction E generalizing φ,
  case list.nil : φ
  {
    induction φ,
    case mm0.formula.meta_var_ : X
    {
      apply fol.proof_eqv_refl,
      unfold mm0.formula.subst,
      simp only [meta_var_to_fol_formula, function.comp_app],
      rewrite fol.subst_inv _ σ_inv σ h_inv_right h_inv_left,
    },
    case mm0.formula.false_
    {
      apply fol.proof_eqv_refl,
      unfold mm0.formula.subst,
      simp only [false_to_fol_formula],
      unfold fol.formula.subst,
    },
    case mm0.formula.pred_ : name args
    {
      apply fol.proof_eqv_refl,
      unfold mm0.formula.subst,
      simp only [pred_to_fol_formula],
      unfold fol.formula.subst,
    },
    case mm0.formula.not_ : φ φ_ih
    {
      unfold mm0.formula.subst,
      simp only [not_to_fol_formula],
      apply fol.proof_eqv_compat_not,
      exact φ_ih,
    },
    case mm0.formula.imp_ : φ ψ φ_ih ψ_ih
    {
      unfold mm0.formula.subst,
      simp only [imp_to_fol_formula],
      apply fol.proof_eqv_compat_imp,
      {
        exact φ_ih,
      },
      {
        exact ψ_ih,
      }
    },
    case mm0.formula.eq_ : x y
    {
      apply fol.proof_eqv_refl,
      unfold mm0.formula.subst,
      simp only [eq_to_fol_formula],
      unfold fol.formula.subst,
    },
    case mm0.formula.forall_ : x φ φ_ih
    {
      unfold mm0.formula.subst,
      simp only [forall_to_fol_formula],
      apply fol.proof_eqv_compat_forall,
      {
        refl,
      },
      {
        exact φ_ih,
      }
    },
    case mm0.formula.def_ : name args
    {
      apply fol.proof_eqv_refl,
      unfold mm0.formula.subst,
      simp only [nil_def_to_fol_formula],
      unfold fol.formula.subst,
    },
  },
  case list.cons : E_hd E_tl E_ih φ
  {
    induction φ,
    case mm0.formula.meta_var_ : X
    {
      apply fol.proof_eqv_refl,
      unfold mm0.formula.subst,
      simp only [meta_var_to_fol_formula, function.comp_app],
      rewrite fol.subst_inv _ σ_inv σ h_inv_right h_inv_left,
    },
    case mm0.formula.false_
    {
      apply fol.proof_eqv_refl,
      unfold mm0.formula.subst,
      simp only [false_to_fol_formula],
      unfold fol.formula.subst,
    },
    case mm0.formula.pred_ : name args
    {
      apply fol.proof_eqv_refl,
      unfold mm0.formula.subst,
      simp only [pred_to_fol_formula],
      unfold fol.formula.subst,
    },
    case mm0.formula.not_ : φ φ_ih
    {
      unfold mm0.formula.subst,
      simp only [not_to_fol_formula],
      apply fol.proof_eqv_compat_not,
      exact φ_ih,
    },
    case mm0.formula.imp_ : φ ψ φ_ih ψ_ih
    {
      unfold mm0.formula.subst,
      simp only [imp_to_fol_formula],
      apply fol.proof_eqv_compat_imp,
      {
        exact φ_ih,
      },
      {
        exact ψ_ih,
      }
    },
    case mm0.formula.eq_ : x y
    {
      apply fol.proof_eqv_refl,
      unfold mm0.formula.subst,
      simp only [eq_to_fol_formula],
      unfold fol.formula.subst,
    },
    case mm0.formula.forall_ : x φ φ_ih
    {
      unfold mm0.formula.subst,
      simp only [forall_to_fol_formula],
      apply fol.proof_eqv_compat_forall,
      {
        refl,
      },
      {
        exact φ_ih,
      }
    },
    case mm0.formula.def_ : name args
    {
      have s1 : (mm0.formula.def_ name args).meta_var_set = ∅,
      refl,

      rewrite to_fol_formula_no_meta_var (fol.formula.subst σ_inv ∘ mm0.formula.to_fol_formula M (E_hd :: E_tl) ∘ τ) M (E_hd :: E_tl) (mm0.formula.def_ name args) s1,
      rewrite mm0.no_meta_var_subst (mm0.formula.def_ name args) σ τ mm0.formula.meta_var_ s1,

      by_cases c1 : name = E_hd.name
        ∧ ∃ (σ : mm0.instantiation), args = list.map σ.val E_hd.args,
      {
        obtain ⟨σ_1, c_1_1, c_1_2⟩ := not_nil_def_to_fol_formula' M E_hd E_tl name args c1,

        unfold mm0.formula.subst,

        have s2 : (mm0.formula.subst σ_1 mm0.formula.meta_var_ E_hd.q).meta_var_set = ∅,
        apply mm0.subst_no_meta_var,
        apply mm0.no_meta_var_imp_meta_var_set_is_empty E_hd.q E_hd.args E_hd.nf,

        by_cases c2 : name = E_hd.name
          ∧ ∃ (σ_1 : mm0.instantiation), list.map σ.val args = list.map σ_1.val E_hd.args,
        {
          obtain ⟨σ_2, c_2_1, c_2_2⟩ := not_nil_def_to_fol_formula' M E_hd E_tl name (list.map σ.val args) c2,

          clear c2,

          rewrite c_1_2,
          clear c_1_2,

          rewrite c_2_2,
          clear c_2_2,

          rewrite c_1_1 at c_2_1,
          simp only [list.map_map] at c_2_1,

          specialize E_ih (mm0.formula.subst σ_1 mm0.formula.meta_var_ E_hd.q),

          rewrite to_fol_formula_no_meta_var (fol.formula.subst σ_inv ∘ mm0.formula.to_fol_formula M E_tl ∘ τ) M E_tl (mm0.formula.subst σ_1 mm0.formula.meta_var_ E_hd.q) s2 at E_ih,
          rewrite mm0.no_meta_var_subst (mm0.formula.subst σ_1 mm0.formula.meta_var_ E_hd.q) σ τ mm0.formula.meta_var_ s2 at E_ih,

          rewrite mm0.subst_comp at E_ih,

          apply fol.proof_eqv_trans
            -- left goal
            (mm0.formula.to_fol_formula M E_tl (mm0.formula.subst σ_2 mm0.formula.meta_var_ E_hd.q))
            -- right IH
            (fol.formula.subst σ (mm0.formula.to_fol_formula M E_tl (mm0.formula.subst σ_1 mm0.formula.meta_var_ E_hd.q)))
            -- right goal
            (fol.formula.subst σ (mm0.formula.to_fol_formula M E_tl (mm0.formula.subst σ_1 mm0.formula.meta_var_ E_hd.q))),
          {
            apply fol.proof_eqv_trans
              -- left goal
              (mm0.formula.to_fol_formula M E_tl (mm0.formula.subst σ_2 mm0.formula.meta_var_ E_hd.q))
              -- left IH
              (mm0.formula.to_fol_formula M E_tl (mm0.formula.subst (σ.comp σ_1) mm0.formula.meta_var_ E_hd.q))
              -- right IH
              (fol.formula.subst σ (mm0.formula.to_fol_formula M E_tl (mm0.formula.subst σ_1 mm0.formula.meta_var_ E_hd.q))),
            {
              apply proof_eqv_to_fol_formula_subst E_hd.q E_hd.args M E_tl _ _ E_hd.nf,
              rewrite <- list.map_eq_map_iff,
              symmetry,
              exact c_2_1,
            },
            {
              apply E_ih,
            },
          },
          {
            apply fol.proof_eqv_refl,
            refl,
          },
        },
        {
          cases c1,
          rewrite c_1_1 at c2,
          push_neg at c2,
          exfalso,
          apply c2 c1_left (mm0.instantiation.comp σ σ_1),
          simp only [list.map_map],
          refl,
        },
      },
      {
        unfold mm0.formula.subst,

        have s2 : (mm0.formula.subst σ mm0.formula.meta_var_ E_hd.q).meta_var_set = ∅,
        apply mm0.subst_no_meta_var,
        apply mm0.no_meta_var_imp_meta_var_set_is_empty E_hd.q E_hd.args E_hd.nf,

        by_cases c2 : name = E_hd.name
          ∧ ∃ (σ_1 : mm0.instantiation), list.map σ.val args = list.map σ_1.val E_hd.args,
        {
          obtain ⟨σ_2, c_2_1, c_2_2⟩ := not_nil_def_to_fol_formula' M E_hd E_tl name (list.map σ.val args) c2,
          cases c2,

          have s1 : E_hd.args.length = args.length,
          transitivity (list.map σ.val args).length,
          {
            transitivity (list.map σ_2.val E_hd.args).length,
            {
              symmetry,
              apply list.length_map,
            },
            {
              rewrite c_2_1,
            },
          },
          {
            apply list.length_map,
          },

          obtain ⟨σ_inv, σ_inv_prop⟩ := mm0.instantiation.exists_inverse σ,

          have s2 : (list.map σ_inv.val (list.map σ.val args)).nodup,
          apply list.nodup.map (mm0.instantiation_injective σ_inv),
          rewrite c_2_1,
          exact list.nodup.map (mm0.instantiation_injective σ_2) E_hd.nodup,

          have s3 : args.nodup,
          simp only [list.map_map] at s2,
          cases σ_inv_prop,
          rewrite σ_inv_prop_right at s2,
          simp only [list.map_id] at s2,
          exact s2,

          obtain s4 := nodup_eq_len_imp_eqv E_hd.args args s1 E_hd.nodup s3,

          exfalso,
          apply c1,
          split,
          {
            exact c2_left,
          },
          {
            apply exists.elim s4,
            intros f s4_1,
            let blah : mm0.instantiation := ⟨ f.to_fun,
              begin
                apply exists.intro f.inv_fun,
                split,
                {
                  simp only [equiv.to_fun_as_coe, equiv.inv_fun_as_coe, equiv.self_comp_symm],
                },
                {
                  simp only [equiv.inv_fun_as_coe, equiv.to_fun_as_coe, equiv.symm_comp_self],
                }
              end ⟩,
            apply exists.intro blah,
            symmetry,
            exact s4_1,
          }
        },
        {
          rewrite to_fol_formula_env_ext M E_hd E_tl name args c1,
          rewrite to_fol_formula_env_ext M E_hd E_tl name (list.map σ.val args) c2,

          specialize E_ih (mm0.formula.def_ name args),
          rewrite to_fol_formula_no_meta_var (fol.formula.subst σ_inv ∘ mm0.formula.to_fol_formula M E_tl ∘ τ) M E_tl (mm0.formula.def_ name args) s1 at E_ih,
          rewrite mm0.no_meta_var_subst (mm0.formula.def_ name args) σ τ mm0.formula.meta_var_ s1 at E_ih,
          unfold mm0.formula.subst at E_ih,
          exact E_ih,
        },
      },
    },
  },
end


lemma is_conv_imp_is_proof_eqv
  (M : mm0.meta_var_name → fol.formula)
  (E : mm0.env)
  (φ φ' : mm0.formula)
  (h1 : mm0.is_conv E φ φ') :
  fol.proof_eqv (mm0.formula.to_fol_formula M E φ) (mm0.formula.to_fol_formula M E φ') :=
begin
  induction h1,
  case mm0.is_conv.conv_refl : h1
  {
    apply fol.proof_eqv_refl,
    refl,
  },
  case mm0.is_conv.conv_symm : h1_φ h1_φ' h1_1 h1_ih
  {
    apply fol.proof_eqv_symm _ _ h1_ih,
  },
  case mm0.is_conv.conv_trans : h1_φ h1_φ' h1_φ'' h1_1 h1_2 h1_ih_1 h1_ih_2
  {
    apply fol.proof_eqv_trans _ _ _ h1_ih_1 h1_ih_2,
  },
  case mm0.is_conv.conv_not : h1_φ h1_φ' h1_1 h1_ih
  {
    simp only [not_to_fol_formula],
    apply fol.proof_eqv_compat_not _ _ h1_ih,
  },
  case mm0.is_conv.conv_imp : h1_φ h1_φ' h1_ψ h1_ψ' h1_1 h1_2 h1_ih_1 h1_ih_2
  {
    simp only [imp_to_fol_formula],
    apply fol.proof_eqv_compat_imp _ _ _ _ h1_ih_1 h1_ih_2,
  },
  case mm0.is_conv.conv_forall : h1_x h1_φ h1_φ' h1_1 h1_ih
  {
    simp only [forall_to_fol_formula],
    apply fol.proof_eqv_compat_forall,
    refl,
    exact h1_ih,
  },
  case mm0.is_conv.conv_unfold : h1_d h1_σ h1_1
  {
    induction E,
    case list.nil
    {
      simp only [list.not_mem_nil] at h1_1,
      contradiction,
    },
    case list.cons : E_hd E_tl E_ih
    {
      simp only [list.mem_cons_iff] at h1_1,
      cases h1_1,
      {
        by_cases c1 : h1_d.name = E_hd.name
          ∧ ∃ (σ : mm0.instantiation), list.map h1_σ.val h1_d.args = list.map σ.val E_hd.args,
        {
          obtain ⟨σ_1, c_1_1, c_1_2⟩ := not_nil_def_to_fol_formula' M E_hd E_tl h1_d.name (list.map h1_σ.val h1_d.args) c1,
          rewrite c_1_2,
          sorry,
        },
        {
          exfalso,
          apply c1,
          rewrite h1_1,
          split,
          {
            refl,
          },
          {
            apply exists.intro h1_σ,
            refl,
          }
        }
      },
      {
        sorry,
      }
    },
  },
end


theorem conservative
  (E : mm0.env)
  (Γ : list (mm0.var_name × mm0.meta_var_name))
  (Δ : list mm0.formula)
  (φ : mm0.formula)
  (M : mm0.meta_var_name → fol.formula)
  (h1 : mm0.is_proof E Γ Δ φ)
  (h2 : ∀ (x : mm0.var_name) (X : mm0.meta_var_name), (x, X) ∈ Γ → fol.not_free x (M X))
  (h3 : ∀ (ψ : mm0.formula), ψ ∈ Δ → fol.is_proof (mm0.formula.to_fol_formula M E ψ)) :
  fol.is_proof (mm0.formula.to_fol_formula M E φ) :=
begin
  induction h1 generalizing M,
  case is_proof.hyp : h1_Γ h1_Δ h1_φ h1_1 h1_2
  {
    exact h3 h1_φ h1_2,
  },
  case is_proof.mp : h1_Γ h1_Δ h1_φ h1_ψ h1_1 h1_2 h1_ih_1 h1_ih_2
  {
    simp only [imp_to_fol_formula] at h1_ih_2,

    apply fol.is_proof.mp (mm0.formula.to_fol_formula M E h1_φ) (mm0.formula.to_fol_formula M E h1_ψ),
    {
      exact h1_ih_1 M h2 h3,
    },
    {
      exact h1_ih_2 M h2 h3,
    }
  },
  case is_proof.prop_1 : h1_Γ h1_Δ h1_φ h1_ψ h1_1 h1_2
  {
    simp only [imp_to_fol_formula],
    apply fol.is_proof.prop_1,
  },
  case is_proof.prop_2 : h1_Γ h1_Δ h1_φ h1_ψ h1_χ h1_1 h1_2 h1_3
  {
    simp only [imp_to_fol_formula],
    apply fol.is_proof.prop_2,
  },
  case is_proof.prop_3 : h1_Γ h1_Δ h1_φ h1_ψ h1_1 h1_2
  {
    simp only [imp_to_fol_formula, not_to_fol_formula],
    apply fol.is_proof.prop_3,
  },
  case is_proof.gen : h1_Γ h1_Δ h1_φ h1_x h1_1 h1_ih
  {
    simp only [forall_to_fol_formula],
    apply fol.is_proof.gen,
    exact h1_ih M h2 h3,
  },
  case is_proof.pred_1 : h1_Γ h1_Δ h1_φ h1_ψ h1_x h1_1 h1_2
  {
    simp only [imp_to_fol_formula, forall_to_fol_formula],
    apply fol.is_proof.pred_1,
  },
  case is_proof.pred_2 : h1_Γ h1_Δ h1_φ h1_x h1_1 h1_2
  {
    simp only [imp_to_fol_formula, forall_to_fol_formula],
    apply fol.is_proof.pred_2,
    exact mm0_not_free_imp_fol_not_free M h1_Γ E h1_x h1_φ h1_2 h2,
  },
  case is_proof.eq_1 : h1_Γ h1_Δ h1_x h1_y h1_1
  {
    unfold mm0.exists_,
    simp only [not_to_fol_formula, forall_to_fol_formula, eq_to_fol_formula],
    apply fol.is_proof.eq_1,
    exact h1_1,
  },
  case is_proof.eq_2 : h1_Γ h1_Δ h1_x h1_y h1_z
  {
    simp only [imp_to_fol_formula, eq_to_fol_formula],
    apply fol.is_proof.eq_2,
  },
  case is_proof.thm : h1_Γ h1_Γ' h1_Δ h1_Δ' h1_φ h1_σ h1_τ h1_1 h1_2 h1_3 h1_4 h1_ih_1 h1_ih_2
  {
    obtain ⟨h1_σ', a1⟩ := h1_σ.2,
    cases a1,

    let h1_σ_inv : mm0.instantiation :=
      ⟨h1_σ', begin apply exists.intro h1_σ.val, exact and.intro a1_right a1_left, end⟩,

    dsimp at *,

    obtain s1 := proof_eqv_subst_to_fol_formula_subst h1_φ M E h1_σ h1_σ_inv h1_τ a1_left a1_right,
    unfold fol.proof_eqv at s1,
    cases s1,

    apply fol.is_proof.mp _ _ _ s1_right,
    apply fol.is_proof_subst_left,
    apply h1_ih_2,
    {
      intros x X a2,

      have s2 : x = (h1_σ_inv.val ∘ h1_σ.val) x,
      simp only [subtype.val_eq_coe],
      rewrite a1_right,
      simp only [id.def],

      rewrite s2,
      simp only [function.comp_app],
      apply fol.not_free_subst h1_σ_inv,
      exact mm0_not_free_imp_fol_not_free M h1_Γ' E (h1_σ.val x) (h1_τ X) (h1_2 x X a2) h2,
    },
    {
      intros ψ a2,

      obtain s3 := proof_eqv_subst_to_fol_formula_subst ψ M E h1_σ h1_σ_inv h1_τ a1_left a1_right,
      unfold fol.proof_eqv at s3,
      cases s3,
      apply fol.is_proof_subst_right _ h1_σ,
      specialize h1_ih_1 ψ a2 M h2 h3,
      apply fol.is_proof.mp _ _ h1_ih_1 s3_left,
    }
  },
  case is_proof.conv : h1_Γ h1_Δ h1_φ h1_φ' h1_1 h1_2 h1_3 h1_ih
  {
    specialize h1_ih M h2 h3,
    obtain s1 := is_conv_imp_is_proof_eqv M _ _ _ h1_3,
    unfold fol.proof_eqv at s1,
    cases s1,
    apply fol.is_proof.mp _ _ h1_ih s1_left,
  },
end
