import data.finset


namespace fol


abbreviation var_name := string
abbreviation pred_name := string


@[derive decidable_eq]
inductive formula : Type
| false_ : formula
| pred_ : pred_name → list var_name → formula
| not_ : formula → formula
| imp_ : formula → formula → formula
| eq_ : var_name → var_name → formula
| forall_ : var_name → formula → formula

open formula


def formula.free_var_set : formula → finset var_name
| false_ := ∅
| (pred_ name args) := args.to_finset
| (not_ φ) := φ.free_var_set
| (imp_ φ ψ) := φ.free_var_set ∪ ψ.free_var_set
| (eq_ x y) := {x, y}
| (forall_ x φ) := φ.free_var_set \ {x}


def formula.bind_var_set : formula → finset var_name
| false_ := ∅
| (pred_ name args) := ∅
| (not_ φ) := φ.bind_var_set
| (imp_ φ ψ) := φ.bind_var_set ∪ ψ.bind_var_set
| (eq_ x y) := ∅
| (forall_ x φ) := φ.bind_var_set ∪ {x}


/-
α equivalence

Type Theory and Formal Proof
An Introduction
Rob Nederpelt, Herman Geuvers
Section 1.5
-/


def replace_free_var
  (binders : finset var_name)
  (v v' x : var_name) :
  var_name :=
  if x ∉ binders ∧ v = x then v' else x


def replace_free_aux (v v' : var_name) : finset var_name → formula → formula
| _ false_ := false_
| binders (pred_ name args) := pred_ name (args.map (replace_free_var binders v v'))
| binders (not_ φ) := not_ (replace_free_aux binders φ)
| binders (imp_ φ ψ) := imp_ (replace_free_aux binders φ) (replace_free_aux binders ψ)
| binders (eq_ x y) := eq_ (replace_free_var binders v v' x) (replace_free_var binders v v' y)
| binders (forall_ x φ) := forall_ x (replace_free_aux (binders ∪ {x}) φ)

def replace_free (v v' : var_name) (φ : formula) : formula := replace_free_aux v v' ∅ φ


inductive alpha_eqv : formula → formula → Prop

| rename_forall (φ : formula) (x x' : var_name) :
  x' ∉ φ.free_var_set → x' ∉ φ.bind_var_set →
  alpha_eqv (forall_ x φ) (forall_ x' (replace_free x x' φ))

| compat_not (φ φ' : formula) :
  alpha_eqv φ φ' → alpha_eqv (not_ φ) (not_ φ')

| compat_imp (φ φ' ψ ψ' : formula) :
  alpha_eqv φ φ' → alpha_eqv ψ ψ' → alpha_eqv (imp_ φ ψ) (imp_ φ' ψ')

| compat_forall (φ φ' : formula) (z : var_name) :
  alpha_eqv φ φ' → alpha_eqv (forall_ z φ) (forall_ z φ')

| refl (φ : formula) :
  alpha_eqv φ φ

| symm (φ φ' : formula) :
  alpha_eqv φ φ' → alpha_eqv φ' φ

| trans (φ φ' φ'' : formula) :
  alpha_eqv φ φ' → alpha_eqv φ' φ'' → alpha_eqv φ φ''


/-
A substitution mapping.
A mapping of each variable name to another name.
-/
def instantiation :=
  {σ : var_name → var_name // ∃ (σ' : var_name → var_name), σ ∘ σ' = id ∧ σ' ∘ σ = id}


lemma instantiation_injective
  (σ : instantiation):
  function.injective σ.1 :=
begin
  obtain ⟨σ', a1⟩ := σ.2,
  cases a1,

  have s1 : function.left_inverse σ' σ.1,
  exact congr_fun a1_right,

  exact function.left_inverse.injective s1,
end


def instantiation.comp (σ σ' : instantiation) : instantiation :=
⟨
  σ.val ∘ σ'.val,
  begin
    obtain ⟨σ_inv_val, σ_inv_prop⟩ := σ.2,
    obtain ⟨σ'_inv_val, σ'_inv_prop⟩ := σ'.2,
    apply exists.intro (σ'_inv_val ∘ σ_inv_val),
    cases σ_inv_prop,
    cases σ'_inv_prop,
    split,
    {
      change σ.val ∘ (σ'.val ∘ σ'_inv_val) ∘ σ_inv_val = id,
      rewrite σ'_inv_prop_left,
      simp only [function.comp.left_id],
      exact σ_inv_prop_left,
    },
    {
      change (σ'_inv_val ∘ (σ_inv_val ∘ σ.val) ∘ σ'.val) = id,
      rewrite σ_inv_prop_right,
      simp only [function.comp.left_id],
      exact σ'_inv_prop_right,
    }
  end
⟩


def formula.subst (σ : instantiation) : formula → formula
| (false_) := false_
| (pred_ name args) := pred_ name (list.map σ.1 args)
| (not_ φ) := not_ φ.subst
| (imp_ φ ψ) := imp_ φ.subst ψ.subst
| (eq_ x y) := eq_ (σ.1 x) (σ.1 y)
| (forall_ x φ) := forall_ (σ.1 x) φ.subst


lemma subst_comp
  (φ : formula)
  (σ σ' : instantiation) :
  formula.subst σ (formula.subst σ' φ) = formula.subst (σ.comp σ') φ :=
begin
  induction φ,
  case fol.formula.false_
  {
    refl,
  },
  case fol.formula.pred_ : name args
  {
    unfold formula.subst,
    simp only [list.map_map, eq_self_iff_true, true_and],
    refl,
  },
  case fol.formula.not_ : φ φ_ih
  {
    unfold formula.subst,
    congr,
    exact φ_ih,
  },
  case fol.formula.imp_ : φ ψ φ_ih ψ_ih
  {
    unfold formula.subst,
    congr,
    {
      exact φ_ih,
    },
    {
      exact ψ_ih,
    }
  },
  case fol.formula.eq_ : x y
  {
    refl,
  },
  case fol.formula.forall_ : x φ φ_ih
  {
    unfold formula.subst,
    congr,
    exact φ_ih,
  },
end

lemma subst_inv
  (φ : formula)
  (σ σ_inv : instantiation)
  (h_inv_left : σ.val ∘ σ_inv.val = id)
  (h_inv_right : σ_inv.val ∘ σ.val = id) :
  formula.subst σ_inv (formula.subst σ φ) = φ :=
begin
  induction φ,
  case fol.formula.false_
  {
    refl,
  },
  case fol.formula.pred_ : name args
  {
    unfold formula.subst,
    simp only [list.map_map, eq_self_iff_true, true_and],
    rewrite h_inv_right,
    simp only [list.map_id],
  },
  case fol.formula.not_ : φ φ_ih
  {
    unfold formula.subst,
    congr,
    exact φ_ih,
  },
  case fol.formula.imp_ : φ ψ φ_ih ψ_ih
  {
    unfold formula.subst,
    congr,
    {
      exact φ_ih,
    },
    {
      exact ψ_ih,
    }
  },
  case fol.formula.eq_ : x y
  {
    unfold formula.subst,
    congr,
    {
      rewrite <- function.comp_app σ_inv.val σ.val x,
      rewrite h_inv_right,
      simp only [id.def],
    },
    {
      rewrite <- function.comp_app σ_inv.val σ.val y,
      rewrite h_inv_right,
      simp only [id.def],
    }
  },
  case fol.formula.forall_ : x φ φ_ih
  {
    unfold formula.subst,
    congr,
    {
      rewrite <- function.comp_app σ_inv.val σ.val x,
      rewrite h_inv_right,
      simp only [id.def],
    },
    {
      exact φ_ih,
    }
  },
end


def not_free (v : var_name) : formula → Prop
| (false_) := true
| (pred_ name args) := v ∉ args
| (not_ φ) := not_free φ
| (imp_ φ ψ) := not_free φ ∧ not_free ψ
| (eq_ x y) := x ≠ v ∧ y ≠ v
| (forall_ x φ) := x = v ∨ not_free φ


lemma not_free_subst
  (σ : instantiation)
  (φ : formula)
  (v : var_name)
  (h1 : not_free v φ) :
  not_free (σ.val v) (formula.subst σ φ) :=
begin
  obtain ⟨σ', a1⟩ := σ.2,
  cases a1,

  have s1 : function.left_inverse σ' σ.val,
  exact congr_fun a1_right,

  have s2 : function.injective σ.val,
  exact function.left_inverse.injective s1,

  induction φ,
  case fol.formula.false_
  {
    unfold formula.subst,
  },
  case fol.formula.pred_ : name args
  {
    unfold not_free at h1,
    unfold formula.subst,
    unfold not_free,
    intros contra,
    apply h1,
    rewrite <- list.mem_map_of_injective s2,
    exact contra,
  },
  case fol.formula.not_ : φ φ_ih
  {
    unfold not_free at h1,
    unfold formula.subst,
    unfold not_free,
    exact φ_ih h1,
  },
  case fol.formula.imp_ : φ ψ φ_ih ψ_ih
  {
    unfold not_free at h1,
    cases h1,

    unfold formula.subst,
    unfold not_free,
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
    unfold not_free at h1,
    cases h1,

    unfold formula.subst,
    unfold not_free,
    split,
    {
      intros contra,
      apply h1_left,
      apply s2 contra,
    },
    {
      intros contra,
      apply h1_right,
      apply s2 contra,
    }
  },
  case fol.formula.forall_ : x φ φ_ih
  {
    unfold not_free at h1,
    unfold formula.subst,
    unfold not_free,
    cases h1,
    {
      apply or.intro_left,
      rewrite h1,
    },
    {
      apply or.intro_right,
      exact φ_ih h1,
    }
  },
end


lemma subst_not_free
  (σ : instantiation)
  (φ : formula)
  (v : var_name)
  (h1 : not_free (σ.val v) (formula.subst σ φ)) :
  not_free v φ :=
begin
  induction φ,
  case fol.formula.false_
  {
    unfold not_free,
  },
  case fol.formula.pred_ : name args
  {
    unfold formula.subst at h1,
    unfold not_free at *,
    simp only [list.mem_map, not_exists, not_and] at h1,
    intros contra,
    apply h1 v contra,
    refl,
  },
  case fol.formula.not_ : φ φ_ih
  {
    unfold formula.subst at h1,
    unfold not_free at *,
    exact φ_ih h1,
  },
  case fol.formula.imp_ : φ ψ φ_ih ψ_ih
  {
    unfold formula.subst at h1,
    unfold not_free at *,
    cases h1,
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
    unfold formula.subst at h1,
    unfold not_free at *,
    cases h1,
    split,
    {
      intros contra,
      apply h1_left,
      rewrite contra,
    },
    {
      intros contra,
      apply h1_right,
      rewrite contra,
    }
  },
  case fol.formula.forall_ : x φ φ_ih
  {
    unfold formula.subst at h1,
    unfold not_free at *,
    cases h1,
    {
      apply or.intro_left,
      exact instantiation_injective σ h1,
    },
    {
      apply or.intro_right,
      exact φ_ih h1,
    }
  },
end


def exists_ (x : var_name) (φ : formula) : formula :=
  not_ (forall_ x (not_ φ))


inductive is_proof : formula → Prop

| mp (φ ψ : formula) :
  is_proof φ → is_proof (φ.imp_ ψ) → is_proof ψ

| prop_1 (φ ψ : formula) :
  is_proof (φ.imp_ (ψ.imp_ φ))

| prop_2 (φ ψ χ : formula) :
  is_proof ((φ.imp_ (ψ.imp_ χ)).imp_ ((φ.imp_ ψ).imp_ (φ.imp_ χ)))

| prop_3 (φ ψ : formula) :
  is_proof (((not_ φ).imp_ (not_ ψ)).imp_ (ψ.imp_ φ))

| gen (φ : formula) (x : var_name) :
  is_proof φ → is_proof (forall_ x φ)

| pred_1 (φ ψ : formula) (x : var_name) :
  is_proof ((forall_ x (φ.imp_ ψ)).imp_ ((forall_ x φ).imp_ (forall_ x ψ)))

| pred_2 (φ : formula) (x : var_name) :
  not_free x φ → is_proof (φ.imp_ (forall_ x φ))

| eq_1 (x y : var_name) :
  y ≠ x → is_proof (exists_ x (eq_ x y))

| eq_2 (x y z : var_name) :
  is_proof ((eq_ x y).imp_ ((eq_ x z).imp_ (eq_ y z)))


lemma is_proof_subst_left
  (φ : formula)
  (σ : instantiation)
  (h1 : is_proof φ) :
  is_proof (φ.subst σ) :=
begin
  obtain ⟨σ', a1⟩ := σ.2,
  cases a1,

  have s1 : function.left_inverse σ' σ.val,
  exact congr_fun a1_right,

  have s2 : function.injective σ.val,
  exact function.left_inverse.injective s1,

  induction h1,
  case fol.is_proof.mp : h1_φ h1_ψ h1_1 h1_2 h1_ih_1 h1_ih_2
  {
    unfold formula.subst at h1_ih_2,
    apply is_proof.mp (formula.subst σ h1_φ) (formula.subst σ h1_ψ) h1_ih_1 h1_ih_2,
  },
  case fol.is_proof.prop_1 : h1_φ h1_ψ
  {
    apply is_proof.prop_1,
  },
  case fol.is_proof.prop_2 : h1_φ h1_ψ h1_χ
  {
    apply is_proof.prop_2,
  },
  case fol.is_proof.prop_3 : h1_φ h1_ψ
  {
    apply is_proof.prop_3,
  },
  case fol.is_proof.gen : h1_φ h1_x h1_1 h1_ih
  {
    apply is_proof.gen,
    exact h1_ih,
  },
  case fol.is_proof.pred_1 : h1_φ h1_ψ h1_x
  {
    apply is_proof.pred_1,
  },
  case fol.is_proof.pred_2 : h1_φ h1_x h1_1
  {
    unfold formula.subst,
    apply is_proof.pred_2,
    exact not_free_subst σ h1_φ h1_x h1_1,
  },
  case fol.is_proof.eq_1 : h1_x h1_y h1_1
  {
    apply is_proof.eq_1,
    intros contra,
    apply h1_1,
    exact s2 contra,
  },
  case fol.is_proof.eq_2 : h1_x h1_y h1_z
  {
    apply is_proof.eq_2,
  },
end


lemma is_proof_subst_right
  (φ : formula)
  (σ : instantiation)
  (h1 : is_proof (φ.subst σ)) :
  is_proof φ :=
begin
  obtain ⟨σ', a1⟩ := σ.2,
  cases a1,

  let σ_inv : instantiation :=
    ⟨σ', begin apply exists.intro σ.val, exact and.intro a1_right a1_left, end⟩,

  have s1 : formula.subst σ_inv (formula.subst σ φ) = φ,
  apply subst_inv φ σ σ_inv a1_left a1_right,

  rewrite <- s1,
  apply is_proof_subst_left,
  exact h1,
end


lemma is_proof_subst
  (φ : formula)
  (σ : instantiation) :
  is_proof (φ.subst σ) ↔ is_proof φ :=
begin
  split,
  {
    apply is_proof_subst_right,
  },
  {
    apply is_proof_subst_left,
  }
end


lemma is_proof_id
  (φ : formula) :
  is_proof (φ.imp_ φ) :=
begin
  obtain s1 := is_proof.prop_2 φ (φ.imp_ φ) φ,
  obtain s2 := is_proof.prop_1 φ (φ.imp_ φ),
  obtain s3 := is_proof.mp _ _ s2 s1,
  obtain s4 := is_proof.prop_1 φ φ,
  obtain s5 := is_proof.mp _ _ s4 s3,
  exact s5,
end


def proof_eqv
  (φ ψ : formula) :
  Prop :=
  is_proof (imp_ φ ψ) ∧ is_proof (imp_ ψ φ)


lemma proof_eqv_compat_not
  (φ ψ : formula)
  (h1 : proof_eqv φ ψ) :
  proof_eqv (not_ φ) (not_ ψ) :=
begin
  sorry,
end


lemma proof_eqv_compat_imp
  (φ φ' ψ ψ' : formula)
  (h1 : proof_eqv φ φ')
  (h2 : proof_eqv ψ ψ') :
  proof_eqv (imp_ φ ψ) (imp_ φ' ψ') :=
begin
  sorry,
end


lemma proof_eqv_compat_forall
  (φ φ' : formula) (x x' : var_name)
  (h1 : x = x')
  (h1 : proof_eqv φ φ') :
  proof_eqv (forall_ x φ) (forall_ x' φ') :=
begin
  sorry,
end


lemma proof_eqv_refl
  (φ φ' : formula)
  (h1 : φ = φ') :
  proof_eqv φ φ' :=
begin
  rewrite h1,
  unfold proof_eqv,
  split,
  {
    exact is_proof_id φ',
  },
  {
    exact is_proof_id φ',
  }
end


lemma proof_eqv_symm
  (φ φ' : formula)
  (h1 : proof_eqv φ φ') :
  proof_eqv φ' φ :=
begin
  unfold proof_eqv at h1,
  cases h1,

  unfold proof_eqv,
  split,
  {
    exact h1_right,
  },
  {
    exact h1_left,
  }
end


lemma proof_eqv_trans
  (φ φ' φ'' : formula)
  (h1 : proof_eqv φ φ')
  (h2 : proof_eqv φ' φ'') :
  proof_eqv φ φ'' :=
begin
  unfold proof_eqv at h1,
  cases h1,

  unfold proof_eqv at h2,
  cases h2,

  sorry,
end


lemma proof_eqv_subst_left
  (φ φ' : formula)
  (σ : instantiation)
  (h1 : proof_eqv φ φ') :
  proof_eqv (formula.subst σ φ) (formula.subst σ φ') :=
begin
  unfold proof_eqv at h1,
  cases h1,

  have s1 : is_proof (formula.subst σ (φ.imp_ φ')),
  exact is_proof_subst_left (φ.imp_ φ') σ h1_left,

  have s2 : is_proof (formula.subst σ (φ'.imp_ φ)),
  exact is_proof_subst_left (φ'.imp_ φ) σ h1_right,

  unfold proof_eqv,
  split,
  {
    unfold formula.subst at s1,
    exact s1,
  },
  {
    unfold formula.subst at s2,
    exact s2,
  }
end


lemma proof_eqv_subst_right
  (φ φ' : formula)
  (σ : instantiation)
  (h1 : proof_eqv (formula.subst σ φ) (formula.subst σ φ')) :
  proof_eqv φ φ' :=
begin
  unfold proof_eqv at *,
  cases h1,
  split,
  {
    apply is_proof_subst_right _ σ,
    unfold formula.subst,
    exact h1_left,
  },
  {
    apply is_proof_subst_right _ σ,
    unfold formula.subst,
    exact h1_right,
  }
end


end fol
