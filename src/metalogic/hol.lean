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

def pi_decide
  {a b : Prop}
  [decidable a]
  (h : a → decidable b) :
  decidable (a ∧ b) :=
if hp : a then
  by haveI := h hp; exact
  if hq : b then is_true (and.intro hp hq)
  else is_false (assume h : a ∧ b, hq (and.right h))
else is_false (assume h : a ∧ b, hp (and.left h))

instance hol_type.decidable_eq : decidable_eq hol_type
| (hol_type.var α) (hol_type.var α') :=
    decidable_of_decidable_of_iff
      (by apply_instance : decidable (α = α')) (by simp only)
| (hol_type.var α) (hol_type.const n ν t) := is_false (by simp only [not_false_iff])
| (hol_type.var α) (hol_type.func σ₁ σ₂) := is_false (by simp only [not_false_iff])
| (hol_type.const n ν t) (hol_type.var α) := is_false (by simp only [not_false_iff])
| (hol_type.const n ν t) (hol_type.const n' ν' t') := decidable_of_decidable_of_iff
  (begin
    apply' pi_decide,
    intro h,
    apply' and.decidable,
    rewrite fin.heq_fun_iff h,
    apply' fintype.decidable_forall_fintype,
    intro a,
    apply hol_type.decidable_eq,
  end : decidable (n = n' ∧ ν = ν' ∧ t == t')) (by simp only)
| (hol_type.const n ν t) (hol_type.func σ₁ σ₂) := is_false (by simp only [not_false_iff])
| (hol_type.func σ₁ σ₂) (hol_type.var α) := is_false (by simp only [not_false_iff])
| (hol_type.func σ₁ σ₂) (hol_type.const n ν t) := is_false (by simp only [not_false_iff])
| (hol_type.func σ₁ σ₂) (hol_type.func σ₁' σ₂') := decidable_of_decidable_of_iff
	(begin
    apply' pi_decide,
    apply hol_type.decidable_eq,
		intro h,
		apply hol_type.decidable_eq
	end : decidable (σ₁ = σ₁' ∧ σ₂ = σ₂')) (by simp only)

/-
The finite set of all of the type variable symbols occurring in a given hol type.
-/
def hol_type.var_set : hol_type → finset type_var_symbols
| (hol_type.var α) := {α}
| (hol_type.const n _ args) := finset.univ.bUnion (fun (i : fin n), (args i).var_set)
| (hol_type.func σ₁ σ₂) := σ₁.var_set ∪ σ₂.var_set


-- The semantics of hol types.

/-
const : (n : ℕ, ν : const_name_symbols) → (op : (args : fin n → Type) → T : Type)
The type of mappings of n-ary hol type constant symbols to operations on Lean types.
n : The arity of the hol type constant symbol.
ν : The hol type constant symbol.
op : The operation on Lean types that the hol type constant symbol is mapped to.
args : The n arguments of the operation expressed as a finite function.
T : The result of the operation. A Lean type.

default : A Lean term belonging to the Lean type mapped to by const.
(A proof by construction that the Lean type mapped to by const is not empty.)
-/
structure type_const_valuation :=
(const : Π (n : ℕ), type_name_symbols → ((fin n → Type) → Type))
(default : Π (n : ℕ) (ν : type_name_symbols) (args : fin n → Type), const n ν args)

/-
The type of mappings of hol type variable symbols to Lean types.
default : A Lean term belonging to the Lean type mapped to by var.
(A proof by construction that the Lean type mapped to by var is not empty.)
-/
structure type_var_valuation :=
(var : type_var_symbols → Type)
(default : Π (α : type_var_symbols), var α)

/-
The function mapping each hol type to a Lean type for a given
type constant valuation and type variable valuation.
-/
def eval_type
	(C : type_const_valuation)
	(V : type_var_valuation) :
	hol_type → Type
| (hol_type.var α) := V.var α
| (hol_type.const n ν args) := C.const n ν (fun (i : fin n), eval_type (args i))
| (hol_type.func σ₁ σ₂) := eval_type σ₁ → eval_type σ₂

/-
The function mapping each hol type to the default Lean term of the Lean type
that the hol type is evaluated to.
-/
def eval_type_default
	(C : type_const_valuation)
	(V : type_var_valuation) :
	Π (σ : hol_type), eval_type C V σ
| (hol_type.var α) := V.default α
| (hol_type.const n ν args) := C.default n ν (fun (i : fin n), eval_type C V (args i))
| (hol_type.func σ₁ σ₂) := fun (x : eval_type C V σ₁), eval_type_default σ₂

instance
	(C : type_const_valuation)
	(V : type_var_valuation)
	(σ : hol_type) :
	inhabited (eval_type C V σ) :=
	{default := eval_type_default C V σ}


abbreviation term_name_symbols := ℕ
abbreviation term_var_symbols := ℕ

inductive hol_term : Type
| var : term_var_symbols → hol_type → hol_term
| const : term_name_symbols → hol_type → hol_term
| app : hol_term → hol_term → hol_term
| abs : term_var_symbols → hol_type → hol_term → hol_term


/-
hol_term.has_type t σ = t : σ
-/
inductive hol_term.has_type : hol_term → hol_type → Prop
| var {x : term_var_symbols} {σ : hol_type} :
	hol_term.has_type (hol_term.var x σ) σ
| const {c : term_name_symbols} {σ : hol_type} :
	hol_term.has_type (hol_term.const c σ) σ
| app {t₁ t₂ : hol_term} {σ₁ σ₂ : hol_type} :
	hol_term.has_type t₁ (hol_type.func σ₁ σ₂) →
	hol_term.has_type t₂ σ₁ →
	hol_term.has_type (hol_term.app t₁ t₂) σ₂
| abs {x : term_var_symbols} {σₓ σₜ : hol_type} {t : hol_term} :
	hol_term.has_type t σₜ →
	hol_term.has_type (hol_term.abs x σₓ t) (hol_type.func σₓ σₜ)


-- The hol type of a hol term if the hol term is syntactically valid.
def hol_term.type : hol_term → option hol_type
| (hol_term.var x σ) := some σ
| (hol_term.const c σ) := some σ
| (hol_term.app t₁ t₂) := do
	hol_type.func σ₁₁ σ₁₂ <- t₁.type | none,
	σ₂ <- t₂.type,
	if σ₁₁ = σ₂ then return σ₁₂ else none
| (hol_term.abs x σₓ t) := do
	σₜ <- t.type,
	return (hol_type.func σₓ σₜ)


/-
A mapping of each hol term variable symbol and hol type to a Lean term
belonging to the Lean type that the hol type is evaluated to.
-/
def term_var_valuation
	(C : type_const_valuation)
	(V : type_var_valuation) :
	Type :=
	term_var_symbols → Π (σ : hol_type), eval_type C V σ

/-
A mapping of each hol term constant symbol and hol type to a Lean term
belonging to the Lean type that the hol type is evaluated to.
-/
def term_const_valuation
	(C : type_const_valuation)
	(V : type_var_valuation) :
	Type :=
	term_name_symbols → Π σ : hol_type, eval_type C V σ


def term_var_valuation.update
	(C : type_const_valuation)
	(V : type_var_valuation)
	(f : term_var_valuation C V)
  (x : term_var_symbols)
	(σ : hol_type)
	(y : eval_type C V σ) :
	term_var_valuation C V :=
	function.update f x (function.update (f x) σ y)


instance
	(C : type_const_valuation)
	(V : type_var_valuation)
	(σ : hol_type) :
	has_coe (eval_type C V σ) (option (Σ σ : hol_type, eval_type C V σ)) :=
	{coe := fun (x : eval_type C V σ), some {fst := σ, snd := x}}

def as_eval_type
	(C : type_const_valuation)
	(V : type_var_valuation)
	(σ : hol_type) :
	(option Σ σ : hol_type, eval_type C V σ) → eval_type C V σ
| (some {fst := σ', snd := x}) := if h : σ = σ' then by rewrite h; exact x else default
| _ := default


def app
	{C : type_const_valuation}
	{V : type_var_valuation} :
	(option Σ σ : hol_type, eval_type C V σ) →
		(option Σ σ : hol_type, eval_type C V σ) →
			(option Σ σ : hol_type, eval_type C V σ)
| (some {fst := hol_type.func σ τ, snd := f}) x :=
		some {fst := τ, snd := f (as_eval_type C V σ x)}
| _ _ := none


def hol_term.semantics
	(C : type_const_valuation)
  (V : type_var_valuation)
  (m : term_const_valuation C V) :
  hol_term → term_var_valuation C V → option (Σ σ : hol_type, eval_type C V σ)
| (hol_term.var x σ) v := v x σ
| (hol_term.const c σ) _ := m c σ
| (hol_term.app t₁ t₂) v :=
		app (hol_term.semantics t₁ v) (hol_term.semantics t₂ v)
| (hol_term.abs x σ t) v := do
  σ₂ ← t.type,
  some {fst := hol_type.func σ σ₂,
				snd := fun (a : eval_type C V σ),
				as_eval_type C V σ₂ (hol_term.semantics t (term_var_valuation.update C V v x σ a))
			 }


-- Type substitution.

/-
sub_type_var_type τ σ = The replacement of each var symbol α in the
hol type σ by the hol type τ α.
-/
def sub_type_var_type
	(τ : type_var_symbols → hol_type) :
	hol_type → hol_type
| (hol_type.var α) := τ α
| (hol_type.const n ν args) := hol_type.const n ν (fun (i : fin n), sub_type_var_type (args i))
| (hol_type.func σ₁ σ₂) := hol_type.func (sub_type_var_type σ₁) (sub_type_var_type σ₂)

lemma lem_1
	(σ : hol_type)
	(τ₁ τ₂ : type_var_symbols → hol_type)
	(h1 : sub_type_var_type τ₁ σ = sub_type_var_type τ₂ σ) :
	∀ α ∈ σ.var_set, τ₁ α = τ₂ α :=
begin
	intros α' h2,
	induction σ,
	case hol_type.var : α
  {
		unfold sub_type_var_type at h1, unfold hol_type.var_set at h2,
		simp only [finset.mem_singleton] at h2, subst h2, exact h1,
	},
  case hol_type.const : n ν args σ_ih
  {
		unfold sub_type_var_type at h1, unfold hol_type.var_set at h2,
		simp only [eq_self_iff_true, heq_iff_eq, true_and] at h1,
		simp only [finset.mem_bUnion, finset.mem_univ, exists_true_left] at h2,
		apply exists.elim h2, intros i h3,
		apply σ_ih i, apply congr_fun h1, exact h3
	},
  case hol_type.func : σ₁ σ₂ σ₁_ih σ₂_ih
  {
		unfold sub_type_var_type at h1, unfold hol_type.var_set at h2,
		simp at h1, cases h1,
		simp at h2, cases h2,
		exact σ₁_ih h1_left h2,
		exact σ₂_ih h1_right h2,
	},
end

lemma lem_2
	(σ : hol_type)
	(τ : type_var_symbols → hol_type)
	(C : type_const_valuation)
	(V : type_var_valuation) :
  eval_type C V (sub_type_var_type τ σ) =
		eval_type C {var := fun (α : type_var_symbols), eval_type C V (τ α),
								default := fun (α : type_var_symbols), eval_type_default C V (τ α)} σ :=
begin
	induction σ,
	case hol_type.var : α
  {
		unfold sub_type_var_type, unfold eval_type
	},
  case hol_type.const : n ν args σ_ih
  {
		unfold sub_type_var_type at *, unfold eval_type at *,
		congr, funext, apply σ_ih
	},
  case hol_type.func : σ₁ σ₂ σ₁_ih σ₂_ih
  {
		unfold sub_type_var_type at *, unfold eval_type at *,
		rewrite σ₁_ih, rewrite σ₂_ih
	},
end
