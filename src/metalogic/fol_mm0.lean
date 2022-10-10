import logic.function.basic
import tactic


set_option pp.parens true


abbreviation var_name := string
abbreviation meta_var_name := string


inductive formula : Type
| meta_var : meta_var_name → formula
| not : formula → formula
| imp : formula → formula → formula
| eq_ : var_name → var_name → formula
| forall_ : var_name → formula → formula

open formula


def valuation (D : Type) : Type := var_name → D
def meta_valuation (D : Type) : Type := meta_var_name → valuation D → Prop

def holds (D : Type) : valuation D → meta_valuation D → formula → Prop
| V M (meta_var X) := M X V
| V M (not φ) := ¬ holds V M φ
| V M (imp φ ψ) := holds V M φ → holds V M ψ
| V M (eq_ x y) := V x = V y
| V M (forall_ x φ) := ∀ (a : D), holds (function.update V x a) M φ


/-
A substitution mapping.
A mapping of each variable name to another name.
-/
def instantiation :=
	{σ : var_name → var_name // ∃ (σ' : var_name → var_name), σ ∘ σ' = id ∧ σ' ∘ σ = id}

/-
A meta substitution mapping.
A mapping of each meta variable name to a formula.
-/
def meta_instantiation : Type := meta_var_name → formula

def formula.subst (σ : instantiation) (τ : meta_instantiation) : formula → formula
| (meta_var X) := τ X
| (not φ) := not φ.subst
| (imp φ ψ) := imp φ.subst ψ.subst
| (eq_ x y) := eq_ (σ.1 x) (σ.1 y)
| (forall_ x φ) := forall_ (σ.1 x) φ.subst


lemma lem_1
	{α β : Type}
	[decidable_eq α]
	(f f' : α → α)
  (x : α)
  (h1 : (f' ∘ f) = id)
  (g : α → β)
  (a : β) :
  (function.update (g ∘ f) x a = function.update g (f x) a ∘ f) :=
begin
		apply funext, intros x',
		unfold function.comp,
		unfold function.update,
		simp only [eq_rec_constant, dite_eq_ite],
		apply if_congr,
		split,
		apply congr_arg,
		apply function.left_inverse.injective,
		exact congr_fun h1,
		refl, refl,
end


lemma lem_2
	(α β : Type)
	[decidable_eq α]
  (f f' : α → α)
	(x : α)
  (h1 : f' ∘ f = id)
  (h2 : f ∘ f' = id)
  (g : α → β)
  (a : β) :
  function.update (g ∘ f) (f' x) a = function.update g x a ∘ f :=
begin
	apply funext, intros x',
	unfold function.comp,
	unfold function.update,
	simp only [eq_rec_constant, dite_eq_ite],
	congr' 1, simp only [eq_iff_iff],
	split,
	intros h3, rewrite h3, rewrite <- function.comp_app f f' x, rewrite h2, simp only [id.def],
	intros h3, rewrite <- h3, rewrite <- function.comp_app f' f x', rewrite h1, simp only [id.def],
end


lemma lem_3
	{D : Type}
	(V : valuation D)
	(M : meta_valuation D)
	(σ : instantiation)
	(σ' : var_name → var_name)
	(τ : meta_instantiation)
	(h1 : σ.1 ∘ σ' = id)
	(h2 : σ' ∘ σ.1 = id)
	(φ : formula) :
	holds D (V ∘ σ.1)
		(fun (X : meta_var_name) (V' : valuation D), holds D (V' ∘ σ') M (τ X)) φ ↔
	holds D V M (φ.subst σ τ) :=
begin
	induction φ generalizing V,
	case formula.meta_var : X
  {
		unfold formula.subst,
		unfold holds,
		rewrite function.comp.assoc V σ.1 σ',
		rewrite h1,
		rewrite function.comp.right_id V,
	},
  case formula.not : φ ih
  {
		unfold formula.subst,
		unfold holds,
		simp only [ih],
	},
  case formula.imp : φ ψ φ_ih ψ_ih
  {
		unfold formula.subst,
		unfold holds,
		simp only [φ_ih, ψ_ih],
	},
  case formula.eq_ : x y
  {
		unfold formula.subst,
		unfold holds,
	},
  case formula.forall_ : x φ φ_ih
  {
		unfold formula.subst,
		unfold holds,
		apply forall_congr, intros a,
		rewrite lem_1 σ.1 σ' x h2 V a,
		apply φ_ih,
	},
end


-- changing v does not cause the value of φ to change

def is_not_free (D : Type) (M : meta_valuation D) (v : var_name) (φ : formula) : Prop :=
	∀ (V : valuation D) (a : D),
	holds D V M φ ↔ holds D (function.update V v a) M φ

lemma lem_4
	{α β : Type}
	[decidable_eq α]
  (f g : α → β)
	(x : α)
  (h1 : ∀ (y : α), y ≠ x → f y = g y) :
  function.update f x (g x) = g :=
begin
  apply funext, intros a,
	unfold function.update,
	simp only [eq_rec_constant, dite_eq_ite],
	split_ifs,
	rewrite h,
	exact h1 a h,
end

theorem is_not_free_equiv
	{D : Type}
	(M : meta_valuation D)
	(v : var_name)
	(φ : formula) :
	is_not_free D M v φ ↔
		∀ (V V' : valuation D),
			(∀ (y : var_name), (y ≠ v → (V y = V' y))) →
				(holds D V M φ ↔ holds D V' M φ) :=
begin
	unfold is_not_free,
	split,
	{
		intros h1 V V' h2,
		rewrite <- lem_4 V V' v h2,
		apply h1,
	},
	{
		intros h1 V a,
		apply h1,
		intros a' h2,
		simp only [function.update_noteq h2],
	}
end


def not_free (Γ : list (var_name × meta_var_name)) (v : var_name) : formula → Prop
| (meta_var X) := (v, X) ∈ Γ
| (not φ) := not_free φ
| (imp φ ψ) := not_free φ ∧ not_free ψ
| (eq_ x y) := x ≠ v ∧ y ≠ v
| (forall_ x φ) := x = v ∨ not_free φ


lemma not_free_imp_is_not_free
	{D : Type}
	(M : meta_valuation D)
	(Γ : list (var_name × meta_var_name))
	(v : var_name)
	(φ : formula)
	(H : not_free Γ v φ)
	(nf : ∀ X, (v, X) ∈ Γ → is_not_free D M v (meta_var X)) :
	is_not_free D M v φ :=
begin
	induction φ,
	case formula.meta_var : X
  {
		unfold not_free at H,
		exact nf X H,
	},
  case formula.not : φ φ_ih
  {
		unfold not_free at *,
		unfold is_not_free at *,
		unfold holds at *,
		intros V a,
		apply not_congr,
		exact φ_ih H V a,
	},
  case formula.imp : φ ψ φ_ih ψ_ih
  {
		unfold not_free at *,
		unfold is_not_free at *,
		unfold holds at *,
		cases H,
		intros V a,
		apply imp_congr,
		exact φ_ih H_left V a,
		exact ψ_ih H_right V a,
	},
  case formula.eq_ : x y
  {
		unfold not_free at H,
		unfold is_not_free at *,
		unfold holds,
		cases H,
		intros V a,
		simp only [function.update_noteq H_left, function.update_noteq H_right],
	},
  case formula.forall_ : x φ φ_ih
  {
		unfold is_not_free at *,
		unfold not_free at *,
		unfold holds at *,
		intros V a,
		apply forall_congr, intros a',
		cases H,
		{
			rewrite H,
			simp only [function.update_idem],
		},
		{
			by_cases v = x,
			{
				rewrite h,
				simp only [function.update_idem],
			},
			{
				simp only [function.update_comm h],
				apply φ_ih H,
			}
		}
	},
end


example
	(D : Type)
	(M : meta_valuation D)
	(Γ Γ' : list (var_name × meta_var_name))
	(σ : instantiation)
	(σ' : var_name → var_name)
  (τ : meta_instantiation)
  (left : ((σ.val ∘ σ') = id))
  (right : ((σ' ∘ σ.val) = id))
  (nf : ∀ (v : var_name) (X : meta_var_name), ((v, X) ∈ Γ') → is_not_free D M v (meta_var X))
  (H : ∀ (v : var_name) (X : meta_var_name), ((v, X) ∈ Γ) → not_free Γ' (σ.val v) (τ X)) :
  ∀ (v : var_name) (X : meta_var_name),
		((v, X) ∈ Γ) →
			is_not_free D (fun (X : meta_var_name) (V' : valuation D), holds D (V' ∘ σ') M (τ X))
				v (meta_var X) :=
begin
	intros v X h1,
	unfold is_not_free,
	unfold holds,
	intros V a,

	have s1 : function.update V v a ∘ σ' = function.update (V ∘ σ') (σ.val v) a,
	apply funext, intros x,
	unfold function.comp,
	by_cases σ' x = v,
	{
		have s2 : x = σ.val v,
		rewrite <- h,
		rewrite <- function.comp_apply σ.val σ' x,
		rewrite left,
		simp only [id.def],

		rewrite h,
		rewrite s2,
		simp only [function.update_same],
	},
	{
		have s2 : ¬ x = σ.val v,
		intro contra,
		apply h,
		rewrite contra,
		symmetry,
		rewrite <- function.comp_apply σ' σ.val v, rewrite right, simp,

		rewrite function.update_noteq h, rewrite function.update_noteq s2,
	},

	rewrite s1,
	apply not_free_imp_is_not_free M Γ',
	exact H v X h1,
	intros X' h2,
	exact nf (σ.val v) X' h2,
end


def exists_ (x : var_name) (φ : formula) : formula := not (forall_ x (not φ))


-- if (v, X) ∈ Γ then v is not free in (meta_var X)
inductive is_proof : list (var_name × meta_var_name) → list formula → formula → Prop
| hyp (Γ : list (var_name × meta_var_name)) (Δ : list formula)
	{φ : formula} :
	φ ∈ Δ → is_proof Γ Δ φ

| mp (Γ : list (var_name × meta_var_name)) (Δ : list formula)
	{φ ψ : formula} :
	is_proof Γ Δ φ → is_proof Γ Δ (φ.imp ψ) → is_proof Γ Δ ψ

| prop_1 (Γ : list (var_name × meta_var_name)) (Δ : list formula)
	{φ ψ : formula} :
	is_proof Γ Δ (φ.imp (ψ.imp φ))

| prop_2 (Γ : list (var_name × meta_var_name)) (Δ : list formula)
	{φ ψ χ : formula} :
	is_proof Γ Δ ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))

| prop_3 (Γ : list (var_name × meta_var_name)) (Δ : list formula)
	{φ ψ : formula} :
	is_proof Γ Δ (((not φ).imp (not ψ)).imp (ψ.imp φ))

| gen (Γ : list (var_name × meta_var_name)) (Δ : list formula)
	{φ : formula} {x : var_name} :
	is_proof Γ Δ φ → is_proof Γ Δ (forall_ x φ)

| pred_1 (Γ : list (var_name × meta_var_name)) (Δ : list formula)
	{φ ψ : formula} {x : var_name} :
	is_proof Γ Δ ((forall_ x (φ.imp ψ)).imp ((forall_ x φ).imp (forall_ x ψ)))

| pred_2 (Γ : list (var_name × meta_var_name)) (Δ : list formula)
	{φ : formula} {x : var_name} :
	not_free Γ x φ → is_proof Γ Δ (φ.imp (forall_ x φ))

| eq_1 (Γ : list (var_name × meta_var_name)) (Δ : list formula)
	{x y : var_name} :
	x ≠ y → is_proof Γ Δ (exists_ x (eq_ x y))

| eq_2 (Γ : list (var_name × meta_var_name)) (Δ : list formula)
	{x y z : var_name} :
	is_proof Γ Δ ((eq_ x y).imp ((eq_ x z).imp (eq_ y z)))

| thm (Γ Γ' : list (var_name × meta_var_name)) (Δ Δ' : list formula)
	{φ : formula} {σ : instantiation} {τ : meta_instantiation} :
	is_proof Γ Δ φ →
	(∀ (x : var_name) (X : meta_var_name), (x, X) ∈ Γ → not_free Γ' (σ.1 x) (τ X)) →
	(∀ (ψ : formula), ψ ∈ Δ → is_proof Γ' Δ' (ψ.subst σ τ)) →
	is_proof Γ' Δ' (φ.subst σ τ)


example
	(D : Type)
	(M : meta_valuation D)
	(Γ : list (var_name × meta_var_name))
	(Δ : list formula)
	(φ : formula)
	(H : is_proof Γ Δ φ)
	(nf : ∀ v X, (v, X) ∈ Γ → is_not_free D M v (meta_var X))
	(hyp : ∀ (φ ∈ Δ) V, holds D V M φ) :
	∀ (V : valuation D), holds D V M φ :=
begin
	induction H generalizing M,
	case is_proof.hyp : Γ Δ φ H
  {
		exact hyp φ H,
	},
	case is_proof.mp : Γ Δ φ ψ minor major minor_ih major_ih
  {
		intros V,
		unfold holds at *,
		apply major_ih M nf hyp,
		apply minor_ih M nf hyp,
	},
  case is_proof.prop_1 : Γ Δ φ ψ
  {
		unfold holds,
		intros V h1 h2, exact h1,
	},
  case is_proof.prop_2 : Γ Δ φ ψ χ
  {
		unfold holds,
		intros V h1 h2 h3,
		apply h1, exact h3, apply h2, exact h3,
	},
  case is_proof.prop_3 : Γ Δ φ ψ
  {
		unfold holds,
		intros V h1 h2,
		by_contradiction,
		exact h1 h h2,
	},
  case is_proof.gen : Γ Δ φ x h1 ih
  {
		unfold holds,
		intros V a,
		apply ih M nf hyp,
	},
  case is_proof.pred_1 : Γ Δ φ ψ x
  {
		unfold holds,
		intros V h1 h2 a,
		apply h1,
		apply h2,
	},
  case is_proof.pred_2 : Γ Δ φ x h1
  {
		have s1 : is_not_free D M x φ,
		apply not_free_imp_is_not_free M Γ x φ h1,
		intros X h2, exact nf x X h2,

		unfold holds,
		intros V h2 a,
		unfold is_not_free at s1,
		rewrite <- s1, exact h2,
	},
  case is_proof.eq_1 : Γ Δ x y H
  {
		unfold exists_,
		unfold holds,
		intros V,
		push_neg,
		simp only [function.update_same],
		apply exists.intro (V y),
		symmetry,
		apply function.update_noteq,
		symmetry, exact H,
	},
  case is_proof.eq_2 : Γ Δ x y z
  {
		unfold holds,
		intros V h1 h2,
		transitivity V x,
		symmetry,
		exact h1,
		exact h2,
	},
  case is_proof.thm : H_Γ H_Γ' H_Δ H_Δ' H_φ H_σ H_τ H_ᾰ H_ᾰ_1 H_ᾰ_2 H_ih_ᾰ H_ih_ᾰ_1
  {
		obtain ⟨σ', left, right⟩ := H_σ.2,
		intros,
		rewrite <- lem_3 V M H_σ σ' H_τ left right,
		apply H_ih_ᾰ, clear H_ih_ᾰ,

		intros,
		unfold is_not_free,
		unfold holds,
		intros,
		specialize H_ᾰ_1 v X ᾰ,
		have := not_free_imp_is_not_free M _ _ _ H_ᾰ_1 _ _ a,
		convert this,
		apply funext, intros,
		unfold function.comp,
		by_cases σ' x = v,
		have s1 : x = H_σ.val v,
		rewrite <- h,
		rewrite <- function.comp_apply H_σ.val σ' x, rewrite left, simp,
		rewrite h,
		rewrite s1, simp only [function.update_same],
		have s1 : ¬ x = H_σ.val v,
		intro contra,
		apply h,
		rewrite contra,
		symmetry,
		rewrite <- function.comp_apply σ' H_σ.val v, rewrite right, simp,
		rewrite function.update_noteq h, rewrite function.update_noteq s1,
		apply nf,

		intros,
		simp at *,
		specialize H_ih_ᾰ_1 φ_1 H M nf hyp (V_1 ∘ σ'),
		rewrite <- lem_3 (V_1 ∘ σ') M H_σ σ' H_τ left right φ_1 at H_ih_ᾰ_1,
		rewrite function.comp.assoc at H_ih_ᾰ_1,
		simp at *,
		rewrite right at H_ih_ᾰ_1, simp at H_ih_ᾰ_1,
		exact H_ih_ᾰ_1,
	},
end
