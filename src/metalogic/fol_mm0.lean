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
def instantiation : Type := var_name → var_name

/-
A meta substitution mapping.
A mapping of each meta variable name to a formula.
-/
def meta_instantiation : Type := meta_var_name → formula

def formula.subst (σ : instantiation) (τ : meta_instantiation) : formula → formula
| (meta_var X) := τ X
| (not φ) := not φ.subst
| (imp φ ψ) := imp φ.subst ψ.subst
| (eq_ x y) := eq_ (σ x) (σ y)
| (forall_ x φ) := forall_ (σ x) φ.subst


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

example
	(φ : formula)
	(D : Type)
	(V : valuation D)
	(M : meta_valuation D)
	(σ σ' : instantiation)
	(τ : meta_instantiation)
	(h1 : σ ∘ σ' = id)
	(h2 : σ' ∘ σ = id) :
	holds D (V ∘ σ)
		(fun (X : meta_var_name) (V' : valuation D), holds D (V' ∘ σ') M (τ X)) φ ↔
	holds D V M (φ.subst σ τ) :=
begin
	induction φ generalizing V,
	case formula.meta_var : X
  {
		unfold formula.subst,
		unfold holds,
		rewrite function.comp.assoc V σ σ',
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
		rewrite lem_1 σ σ' x h2 V a,
		apply φ_ih,
	},
end


-- changing v does not cause the value of φ to change

def is_not_free (D : Type) (M : meta_valuation D) (v : var_name) (φ : formula) : Prop :=
	∀ (V : valuation D) (a : D),
	holds D V M φ ↔ holds D (function.update V v a) M φ

lemma lem_2
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
		rewrite <- lem_2 V V' v h2,
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
	(h1 : ∀ (p : (var_name × meta_var_name)), p ∈ Γ → is_not_free D M p.fst (meta_var p.snd)) :
	not_free Γ v φ → is_not_free D M v φ :=
begin
	induction φ,
	case formula.meta_var : X
  {
		unfold not_free,
		apply h1,
	},
  case formula.not : φ φ_ih
  {
		unfold is_not_free at *,
		unfold not_free at *,
		unfold holds at *,
		intros h2 V a,
		rewrite φ_ih h2 V a,
	},
  case formula.imp : φ ψ φ_ih ψ_ih
  {
		unfold is_not_free at *,
		unfold not_free at *,
		unfold holds at *,
		intros h2 V a,
		cases h2,
		simp only [φ_ih h2_left V a, ψ_ih h2_right V a],
	},
  case formula.eq_ : x y
  {
		unfold is_not_free at *,
		unfold not_free at *,
		unfold holds at *,
		intros h2 V a,
		cases h2,
		simp only [function.update_noteq h2_left, function.update_noteq h2_right],
	},
  case formula.forall_ : x φ φ_ih
  {
		unfold is_not_free at *,
		unfold not_free at *,
		unfold holds at *,
		intros h2 V a,
		apply forall_congr, intros a',
		simp only [prod.forall] at *,
		cases h2,
		{
			rewrite h2,
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
				apply φ_ih h2,
			}
		}
	},
end


inductive is_proof : list (var_name × meta_var_name) → list formula → formula → Prop
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


example
	(D : Type)
	(M : meta_valuation D)
	(Γ : list (var_name × meta_var_name))
	(Δ : list formula)
	(φ : formula)
	(H : is_proof Γ Δ φ)
	(nf : ∀ v X, (v, X) ∈ Γ -> is_not_free D M v (meta_var X))
	(hyp : ∀ (φ ∈ Δ) V, holds D V M φ) :
	∀ (V : valuation D), holds D V M φ :=
begin
	induction H,
	case is_proof.mp : Γ Δ φ ψ minor major minor_ih major_ih
  {
		intros V,
		unfold holds at *,
		apply major_ih nf hyp,
		apply minor_ih nf hyp,
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
		apply ih nf hyp,
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
		have s1 : is_not_free D M x φ, apply not_free_imp_is_not_free M Γ,
		intros p h4, apply nf, simp only [prod.mk.eta], exact h4, exact h1,

		unfold holds,
		intros V h2 a,
		rewrite is_not_free_equiv M x φ at s1,
		rewrite s1 (function.update V x a) V, exact h2,
		intros y h3,
		apply function.update_noteq h3,
	},
end
