/-
References:

http://sourceforge.net/projects/hol/files/hol/kananaskis-14/kananaskis-14-logic.pdf/download

https://www.cl.cam.ac.uk/~jrh13/papers/holhol.pdf
-/


import data.finset


abbreviation type_name_symbols := ℕ -- ν
abbreviation type_var_symbols := ℕ -- α, β, ...

-- σ
inductive hol_type : Type
| var : type_var_symbols → hol_type
| const (n : ℕ) : type_name_symbols → (fin n → hol_type) → hol_type
| func : hol_type → hol_type → hol_type

open hol_type

def hol_type.var_set : hol_type → finset type_var_symbols
| (var α) := {α}
| (const n _ args) := finset.univ.bUnion (fun (i : fin n), (args i).var_set)
| (func σ₁ σ₂) := σ₁.var_set ∪ σ₂.var_set


def model := Π (n : ℕ), type_name_symbols → (fin n → Type) → Type
def valuation := type_var_symbols → Type

def model.type (M : model) (V : valuation) : hol_type → Type
| (var α) := V α
| (const n ν args) := M n ν (fun i : fin n, model.type (args i))
| (func σ₁ σ₂) := model.type σ₁ → model.type σ₂

def hol_type.instance (type_var_symbol_to_type : type_var_symbols → hol_type) : hol_type → hol_type
| (var α) := type_var_symbol_to_type α
| (const n ν args) := const n ν (fun i : fin n, hol_type.instance (args i))
| (func σ₁ σ₂) := func (hol_type.instance σ₁) (hol_type.instance σ₂)

lemma lem_1
	(σ : hol_type)
	(τ₁ τ₂ : type_var_symbols → hol_type)
	(h1 : σ.instance τ₁ = σ.instance τ₂) :
	∀ α ∈ σ.var_set, τ₁ α = τ₂ α :=
begin
	intros α' h2,
	induction σ,
	case hol_type.var : α
  {
		unfold hol_type.instance at h1, unfold hol_type.var_set at h2,
		simp only [finset.mem_singleton] at h2, subst h2, exact h1,
	},
  case hol_type.const : n ν args σ_ih
  {
		unfold hol_type.instance at h1, unfold hol_type.var_set at h2,
		simp only [eq_self_iff_true, heq_iff_eq, true_and] at h1,
		simp only [finset.mem_bUnion, finset.mem_univ, exists_true_left] at h2,
		apply exists.elim h2, intros i h3,
		apply σ_ih i, apply congr_fun h1, exact h3
	},
  case hol_type.func : σ₁ σ₂ σ₁_ih σ₂_ih
  {
		unfold hol_type.instance at h1, unfold hol_type.var_set at h2,
		simp at h1, cases h1,
		simp at h2, cases h2,
		exact σ₁_ih h1_left h2,
		exact σ₂_ih h1_right h2,
	},
end

lemma lem_2
	(σ : hol_type)
	(τ : type_var_symbols → hol_type)
	(M : model)
	(V : valuation) :
  M.type V (σ.instance τ) = M.type (fun i, M.type V (τ i)) σ :=
begin
	induction σ,
	case hol_type.var : α
  {
		unfold hol_type.instance, unfold model.type
	},
  case hol_type.const : n ν args σ_ih
  {
		unfold hol_type.instance at *, unfold model.type at *,
		congr, funext, apply σ_ih
	},
  case hol_type.func : σ₁ σ₂ σ₁_ih σ₂_ih
  {
		unfold hol_type.instance at *, unfold model.type at *,
		rewrite σ₁_ih, rewrite σ₂_ih
	},
end


abbreviation term_name_symbols := ℕ

inductive hol_term : Type
| var : term_name_symbols → hol_term
| const : term_name_symbols → hol_term
| app : hol_term → hol_term → hol_term
| abs : term_name_symbols → hol_term → hol_term

