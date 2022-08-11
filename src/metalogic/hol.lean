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
