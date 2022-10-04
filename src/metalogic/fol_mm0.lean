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


def is_not_free_rec (D : Type) (M : meta_valuation D) : formula → var_name → Prop
| (meta_var X) v := ∀ (V : valuation D) (a : D), M X V ↔ M X (function.update V v a)
| (not φ) v := is_not_free_rec φ v
| (imp φ ψ) v := is_not_free_rec φ v ∧ is_not_free_rec ψ v
| (eq_ x y) v := x ≠ v ∧ y ≠ v
| (forall_ x φ) v := x = v ∨ is_not_free_rec φ v


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
				(holds D V M φ ↔ holds D V' M φ):=
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


example
	(D : Type)
	(M : meta_valuation D)
	(v : var_name)
	(X : meta_var_name) :
	(∀ (V : valuation D) (a : D), M X V ↔ M X (function.update V v a)) →
		is_not_free D M v (meta_var X) :=
begin
	unfold is_not_free,
	unfold holds,
	intros h1 V a,
	apply h1,
end

example
	(D : Type)
	(M : meta_valuation D)
	(v : var_name)
	(φ : formula) :
	is_not_free D M v φ → is_not_free D M v (not φ) :=
begin
	unfold is_not_free,
	unfold holds,
	intros h1 V a,
	rewrite h1,
end

example
	(D : Type)
	(M : meta_valuation D)
	(v : var_name)
	(φ ψ : formula) :
	is_not_free D M v φ ∧ is_not_free D M v ψ → is_not_free D M v (imp φ ψ) :=
begin
	unfold is_not_free,
	unfold holds,
	intros h1 V a,
	cases h1,
	rewrite h1_left V a,
	rewrite h1_right V a,
end

example
	(D : Type)
	(M : meta_valuation D)
	(v : var_name)
	(x y : var_name) :
	x ≠ v ∧ y ≠ v → is_not_free D M v (eq_ x y) :=
begin
	unfold is_not_free,
	unfold holds,
	intros h1 V a,
	cases h1,
	simp only [function.update_noteq h1_left, function.update_noteq h1_right],
end

example
	(D : Type)
	(M : meta_valuation D)
	(v : var_name)
	(x : var_name)
	(φ : formula) :
	v = x → is_not_free D M v (forall_ x φ) :=
begin
	unfold is_not_free,
	unfold holds,
	intros h1 V a,
	apply forall_congr, intros a',
	rewrite h1,
	simp only [function.update_idem],
end

example
	(D : Type)
	(M : meta_valuation D)
	(v : var_name)
	(x : var_name)
	(φ : formula) :
	is_not_free D M v φ → is_not_free D M v (forall_ x φ) :=
begin
	unfold is_not_free,
	unfold holds,
	intros h1 V a,
	apply forall_congr, intros a',
	by_cases v = x,
	{
		rewrite h,
		simp only [function.update_idem],
	},
	{
		simp only [function.update_comm h],
		apply h1,
	}
end


theorem is_valid_pred_3
	(D : Type)
	(V : valuation D)
	(M : meta_valuation D)
	(x : var_name)
	(φ : formula)
	(h1 : is_not_free D M x φ) :
	holds D V M (φ.imp (forall_ x φ)) :=
begin
	unfold is_not_free at h1,
	unfold holds,
	intros h3 a,
	cases h1 V a,
	exact mp h3,
end


def not_free (Γ : list (var_name × meta_var_name)) (v : var_name) : formula → Prop
| (meta_var X) := (v, X) ∈ Γ
| (not φ) := not_free φ
| (imp φ ψ) := not_free φ ∧ not_free ψ
| (eq_ x y) := x ≠ v ∧ y ≠ v
| (forall_ x φ) := x = v ∨ not_free φ


example
	(D : Type)
	(M : meta_valuation D)
	(Γ : list (var_name × meta_var_name))
	(v : var_name)
	(φ : formula)
	(h1 : ∀ (p : (var_name × meta_var_name)), p ∈ Γ → is_not_free D M p.fst (meta_var p.snd)) :
	not_free Γ v φ → is_not_free D M v φ :=
begin
	sorry
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
