import .replace_free_fun

set_option pp.parens true


namespace fol

open formula



@[derive decidable]
def admits_fun_aux (σ : variable_ → variable_) : finset variable_ → formula → bool
| _ true_ := true
| binders (pred_ X xs) :=
    ∀ (v : variable_), v ∈ xs → v ∉ binders → σ v ∉ binders 
| binders (not_ phi) := admits_fun_aux binders phi
| binders (imp_ phi psi) := admits_fun_aux binders phi ∧ admits_fun_aux binders psi
| binders (forall_ x phi) := admits_fun_aux (binders ∪ {x}) phi

@[derive decidable]
def admits_fun (σ : variable_ → variable_) (phi : formula) : Prop :=
  admits_fun_aux σ ∅ phi


end fol

