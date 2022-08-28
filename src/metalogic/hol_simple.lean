import data.finset


@[derive decidable_eq]
inductive hol_type : Type
| bool : hol_type
| func : hol_type → hol_type → hol_type

def eval_type : hol_type → Type
| (hol_type.bool) := Prop
| (hol_type.func σ₁ σ₂) := eval_type σ₁ → eval_type σ₂

def eval_type_default :	Π (σ : hol_type), eval_type σ
| (hol_type.bool) := true
| (hol_type.func σ₁ σ₂) := fun (x : eval_type σ₁), eval_type_default σ₂

instance
	(σ : hol_type) :
	inhabited (eval_type σ) :=
	{default := eval_type_default σ}


abbreviation term_var_symbols := ℕ

@[derive decidable_eq]
inductive hol_term : Type
| var : term_var_symbols → hol_type → hol_term
| eq : hol_type → hol_term
| app : hol_term → hol_term → hol_term
| abs : term_var_symbols → hol_type → hol_term → hol_term

-- The hol type of a hol term if the hol term is syntactically valid.
def hol_term.type_of : hol_term → option hol_type
| (hol_term.var x σ) := some σ
| (hol_term.eq σ) := some (hol_type.func σ (hol_type.func σ hol_type.bool))
| (hol_term.app t₁ t₂) := do
		hol_type.func σ₁₁ σ₁₂ <- t₁.type_of | none,
		σ₂ <- t₂.type_of,
		if σ₁₁ = σ₂ then return σ₁₂ else none
| (hol_term.abs x σₓ t) := do
	σₜ <- t.type_of,
	return (hol_type.func σₓ σₜ)

/-
A mapping of each hol term variable symbol and hol type to a Lean term
belonging to the Lean type that the hol type is evaluated to.
-/
def term_var_valuation : Type :=
	term_var_symbols → Π (σ : hol_type), eval_type σ


def term_var_valuation.update
	(f : term_var_valuation)
	(x : term_var_symbols)
	(σ : hol_type)
	(y : eval_type σ) :
	term_var_valuation :=
	function.update f x (function.update (f x) σ y)


instance
	{σ : hol_type} :
	has_coe (eval_type σ) (option Σ σ : hol_type, eval_type σ) :=
	{coe := fun (x : eval_type σ), some {fst := σ, snd := x}}


def as_eval_type
	(σ : hol_type) :
	(option Σ σ : hol_type, eval_type σ) → eval_type σ
| (some {fst := σ', snd := x}) := if h : σ = σ' then by rewrite h; exact x else default
| _ := default

def app :
	(option Σ σ : hol_type, eval_type σ) →
		(option Σ σ : hol_type, eval_type σ) →
			(option Σ σ : hol_type, eval_type σ)
| (some {fst := hol_type.func σ τ, snd := f}) x := some {fst := τ, snd := f (as_eval_type σ x)}
| _ _ := none


def eval_term :
  hol_term → term_var_valuation → option (Σ σ : hol_type, eval_type σ)
| (hol_term.var x σ) v := some {fst := σ, snd := v x σ}
| (hol_term.eq σ) _ := some {fst := hol_type.func σ (hol_type.func σ hol_type.bool),
		snd := fun (x y : eval_type σ), x = y}
| (hol_term.app t₁ t₂) v :=
		app (eval_term t₁ v) (eval_term t₂ v)
| (hol_term.abs x σ t) v := do
  σ₂ ← t.type_of,
  some {fst := hol_type.func σ σ₂,
				snd := fun (a : eval_type σ),
				as_eval_type σ₂ (eval_term t (term_var_valuation.update v x σ a))
			 }


example
  (v : term_var_valuation)
	(t : hol_term)
  (σ : hol_type)
	(h : t.type_of = some σ) :
	(eval_term t v).map sigma.fst = some σ :=
begin
	sorry
end


example
	(v : term_var_valuation)
	(t : hol_term)
  (σ : hol_type)
	(h : t.type_of = some σ) :
	eval_term t v = as_eval_type σ (eval_term t v) :=
begin
	sorry
end


def mk_eq
	(σ : hol_type)
	(s t : hol_term) :
	hol_term :=
	hol_term.app (hol_term.app (hol_term.eq σ) s) t


def hol_term.free_var_set : hol_term → finset (term_var_symbols × hol_type)
| (hol_term.var x σ) := {(x, σ)}
| (hol_term.eq _) := ∅
| (hol_term.app s t) := s.free_var_set ∪ t.free_var_set
| (hol_term.abs x σ t) := t.free_var_set \ {(x, σ)}


inductive proof : list hol_term → hol_term → Prop
| refl_ {t : hol_term} {σ : hol_type} :
	t.type_of = some σ →
	proof [] (mk_eq σ t t)

| trans_ {s t u : hol_term} {σ : hol_type} {Γ Δ : list hol_term} :
/-
	s.type_of = some σ →
	t.type_of = some σ →
	u.type_of = some σ →
-/
	proof Γ (mk_eq σ s t) → proof Δ (mk_eq σ t u) → proof (Γ ∪ Δ) (mk_eq σ s u)

| app_ {s t u v : hol_term} {σ₁ σ₂ : hol_type} {Γ Δ : list hol_term} :
/-
	s.type_of = some (hol_type.func σ₁ σ₂) →
	t.type_of = some (hol_type.func σ₁ σ₂) →
	u.type_of = some σ₁ →
	v.type_of = some σ₁ → 
-/
	proof Γ (mk_eq (hol_type.func σ₁ σ₂) s t) →
	proof Δ (mk_eq σ₁ u v) →
	proof (Γ ∪ Δ) (mk_eq σ₂ (hol_term.app s u) (hol_term.app t v))

| abs_ {s t : hol_term} {x : term_var_symbols} {σₓ σₛₜ : hol_type} {Γ : list hol_term} :
/-
	s.type_of = some σₛₜ →
	t.type_of = some σₛₜ →
-/
	(∀ u ∈ Γ, (x, σₓ) ∉ (u : hol_term).free_var_set) →
	proof Γ (mk_eq σₛₜ s t) →
	proof Γ (mk_eq (hol_type.func σₓ σₛₜ) (hol_term.abs x σₓ s) (hol_term.abs x σₓ t))

| assume_ {p : hol_term} :
	p.type_of = some hol_type.bool →
	proof [p] p

| eq_mp {p q : hol_term} {Γ Δ : list hol_term} :
/-
	p.type_of = some hol_type.bool →
	q.type_of = some hol_type.bool →
-/
	proof Γ (mk_eq hol_type.bool p q) →
	proof Δ p →
	proof (Γ ∪ Δ) q

| deduct_anti_symm {p q : hol_term} {Γ Δ : list hol_term} :
/-
	p.type_of = some hol_type.bool →
	q.type_of = some hol_type.bool →
-/
	proof Γ p →
	proof Δ q →
	proof ((Γ \ [q]) ∪ (Δ \ [p])) (mk_eq hol_type.bool p q)
