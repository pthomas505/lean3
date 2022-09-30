import logic.function.basic
import tactic


set_option pp.parens true


abbreviation var_name := string
abbreviation meta_var_name := string


inductive formula : Type
| meta_var : meta_var_name → formula
| not : formula → formula
| imp : formula → formula → formula
| eq : var_name → var_name → formula
| forall_ : var_name → formula → formula

open formula


def valuation (D : Type) : Type := var_name → D
def meta_valuation (D : Type) : Type := meta_var_name → valuation D → Prop

def holds (D : Type) : valuation D → meta_valuation D → formula → Prop
| V M (meta_var X) := M X V
| V M (not φ) := ¬ holds V M φ
| V M (imp φ ψ) := holds V M φ → holds V M ψ
| V M (eq x y) := V x = V y
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
| (eq x y) := eq (σ x) (σ y)
| (forall_ x φ) := forall_ (σ x) φ.subst


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
  case formula.eq : x y
  {
		unfold formula.subst,
		unfold holds,
	},
  case formula.forall_ : x φ φ_ih
  {
		unfold formula.subst,
		unfold holds,
		apply forall_congr, intros a,
		unfold function.comp at *,

		specialize φ_ih (function.update V (σ x) a),

		have s1 : (fun (x' : var_name), function.update V (σ x) a (σ x')) =
			function.update (fun (x : var_name), V (σ x)) x a,
		apply funext, intros x',
		unfold function.update,
		simp only [eq_rec_constant, dite_eq_ite],

		have s2 : function.injective σ,
		apply function.left_inverse.injective,
		exact congr_fun h2,

		have s3 : σ x' = σ x ↔ x' = x,
		split,
		intros h3, exact s2 h3,
		exact congr_arg (λ (x' : var_name), σ x'),

		simp only [s3],
		rewrite s1 at φ_ih,
		exact φ_ih,
	},
end
