import data.hash_map

import metalogic.mm0.mm0


open mm0


-- Proof Checker


def definition_map : Type := hash_map string (fun _, definition_)


def formula.is_meta_var_or_all_def_in_map (m : definition_map) : formula → option unit

| (meta_var_ _) := some ()

| (false_) := some ()

| (pred_ _ _) := some ()

| (not_ φ) := φ.is_meta_var_or_all_def_in_map

| (imp_ φ ψ) := do
  φ.is_meta_var_or_all_def_in_map,
  ψ.is_meta_var_or_all_def_in_map

| (eq_ _ _) := some ()

| (forall_ _ φ) := φ.is_meta_var_or_all_def_in_map

| (def_ name args) := do
  d <- m.find name,
  guard (args.length = d.args.length)


structure theorem_ : Type :=
(Γ : list (var_name × meta_var_name))
(Δ : list formula)
(φ : formula)

def theorem_map : Type := hash_map string (fun _, theorem_)


inductive conv_step
| refl_conv : conv_step
| symm_conv : conv_step → conv_step
| trans_conv : formula → conv_step → conv_step → conv_step
| conv_not : conv_step → conv_step
| conv_imp : conv_step → conv_step → conv_step
| conv_forall : conv_step → conv_step
| conv_unfold : string → instantiation → conv_step

open conv_step


def check_conv_step
  (global_definition_map : definition_map) :
  conv_step → formula → formula → option unit

| refl_conv φ φ' := guard (φ = φ')

| (symm_conv step) φ φ' := check_conv_step step φ' φ

| (trans_conv φ' step_1 step_2) φ φ'' := do
  check_conv_step step_1 φ φ',
  check_conv_step step_2 φ' φ''

| (conv_not step) (not_ φ) (not_ φ') := check_conv_step step φ φ'

| (conv_imp step_1 step_2) (imp_ φ ψ) (imp_ φ' ψ') := do
  check_conv_step step_1 φ φ',
  check_conv_step step_2 ψ ψ'

| (conv_forall step) (forall_ x φ) (forall_ x' φ') := do
  check_conv_step step φ φ',
  guard (x = x')

| (conv_unfold name σ) φ φ' := do
  d <- global_definition_map.find name,
  guard (φ = def_ d.name (d.args.map σ.1)),
  guard (φ' = d.q.subst σ meta_var_)

| _ _ _ := none


inductive proof_step : Type
| hyp : ℕ → proof_step
| thm : string → list ℕ → instantiation → meta_instantiation → proof_step
| conv : ℕ → formula → conv_step → proof_step

open proof_step


instance
  (α : Type)
  [decidable_eq α]
  (f : α → α)
  (l1 l2 : list α) :
  decidable (l1.map f ⊆ l2) :=
begin
  exact list.decidable_ball (fun (x : α), (x ∈ l2)) (list.map f l1),
end


def check_proof_step
  (Γ : list (var_name × meta_var_name))
  (Δ : list formula)
  (global_definition_map : definition_map)
  (global_theorem_map : theorem_map)
  (local_proof_list : list formula) :
  proof_step → option formula

| (hyp index) := Δ.nth index

| (thm name hyp_index_list σ τ) := do
  (theorem_.mk Γ' Δ' φ') <- global_theorem_map.find name,
  Δ <- (hyp_index_list.map (fun (i : ℕ), local_proof_list.nth i)).option_to_option_list,
  if
    (Γ'.all (fun (p : (var_name × meta_var_name)), not_free Γ (σ.1 p.fst) (τ p.snd)))
    ∧ Δ'.map (formula.subst σ τ) = Δ
  then φ'.subst σ τ
  else none

| (conv φ_index φ' step) := do
  φ <- local_proof_list.nth φ_index,
  check_conv_step global_definition_map step φ φ',
  pure φ'


def check_proof_step_list_aux
  (Γ : list (var_name × meta_var_name))
  (Δ : list formula)
  (global_definition_map : definition_map)
  (global_theorem_map : theorem_map) :
  list formula → list proof_step → option formula

| local_proof_list [] := local_proof_list.last'

| local_proof_list (current_proof_step :: remaining_proof_step_list) := do
  local_proof <- check_proof_step Γ Δ global_definition_map global_theorem_map local_proof_list current_proof_step,
  check_proof_step_list_aux (local_proof_list ++ [local_proof]) remaining_proof_step_list


def check_proof_step_list
  (Γ : list (var_name × meta_var_name))
  (Δ : list formula)
  (global_definition_map : definition_map)
  (global_theorem_map : theorem_map)
  (proof_step_list : list proof_step) :
  option formula :=
  check_proof_step_list_aux Γ Δ global_definition_map global_theorem_map [] proof_step_list


structure proof : Type :=
  (Γ : list (var_name × meta_var_name))
  (Δ : list formula)
  (step_list : list proof_step)
  (name : string)


def check_proof
  (global_definition_map : definition_map)
  (global_theorem_map : theorem_map)
  (P : proof) :
  option theorem_ := do
  φ <- check_proof_step_list P.Γ P.Δ global_definition_map global_theorem_map P.step_list,
  some {Γ := P.Γ, Δ := P.Δ, φ := φ}


inductive command_ : Type
| add_definition : definition_ → command_
| add_proof : proof → command_

open command_


def check_command
  (global_definition_map : definition_map)
  (global_theorem_map : theorem_map) :
  command_ → option (definition_map × theorem_map)

| (add_definition d) := do
  d.q.is_meta_var_or_all_def_in_map global_definition_map,
  if ¬ global_definition_map.contains d.name
  then some (global_definition_map.insert d.name d, global_theorem_map)
  else none

| (add_proof P) := do
  (P.Δ.mmap' (formula.is_meta_var_or_all_def_in_map global_definition_map)),
  T <- check_proof global_definition_map global_theorem_map P,
  T.φ.is_meta_var_or_all_def_in_map global_definition_map,
  some (global_definition_map, global_theorem_map.insert P.name T)


def check_command_list_aux :
  definition_map → theorem_map → list command_ → option (definition_map × theorem_map)

| global_definition_map global_theorem_map [] := some (global_definition_map, global_theorem_map)

| global_definition_map global_theorem_map (current_command :: remaining_command_list) := do
  (global_definition_map', global_theorem_map') <- check_command global_definition_map global_theorem_map current_command,
  check_command_list_aux global_definition_map' global_theorem_map' remaining_command_list


def check_command_list
  (axiom_map : theorem_map)
  (command_list : list command_) :
  option (definition_map × theorem_map) :=
  check_command_list_aux (mk_hash_map string.hash) axiom_map command_list


-- First Order Logic


def mp_axiom : theorem_ := {
  Γ := [],
  Δ := [((meta_var_ "φ").imp_ (meta_var_ "ψ")), (meta_var_ "φ")],
  φ := (meta_var_ "ψ")
}

def prop_1_axiom : theorem_ := {
  Γ := [],
  Δ := [],
  φ := ((meta_var_ "φ").imp_ ((meta_var_ "ψ").imp_ (meta_var_ "φ")))
}

def prop_2_axiom : theorem_ := {
  Γ := [],
  Δ := [],
  φ := (((meta_var_ "φ").imp_ ((meta_var_ "ψ").imp_ (meta_var_ "χ"))).imp_ (((meta_var_ "φ").imp_ (meta_var_ "ψ")).imp_ ((meta_var_ "φ").imp_ (meta_var_ "χ"))))
}

def prop_3_axiom : theorem_ := {
  Γ := [],
  Δ := [],
  φ := (((not_ (meta_var_ "φ")).imp_ (not_ (meta_var_ "ψ"))).imp_ ((meta_var_ "ψ").imp_ (meta_var_ "φ")))
}

def gen_axiom : theorem_ := {
  Γ := [],
  Δ := [],
  φ := (forall_ "x" (meta_var_ "φ"))
}

def pred_1_axiom : theorem_ := {
  Γ := [],
  Δ := [],
  φ := ((forall_ "x" ((meta_var_ "φ").imp_ (meta_var_ "ψ"))).imp_ ((forall_ "x" (meta_var_ "φ")).imp_ (forall_ "x" (meta_var_ "ψ"))))
}

def pred_2_axiom : theorem_ := {
  Γ := [("x", "φ")],
  Δ := [],
  φ := ((meta_var_ "φ").imp_ (forall_ "x" (meta_var_ "φ")))
}

def eq_1_axiom : theorem_ := {
  Γ := [],
  Δ := [not_ (eq_ "y" "x")],
  φ := (exists_ "x" (eq_ "x" "y")),
}

def eq_2_axiom : theorem_ := {
  Γ := [],
  Δ := [],
  φ := ((eq_ "x" "y").imp_ ((eq_ "x" "z").imp_ (eq_ "y" "z")))
}

def fol_axiom_map : hash_map string (fun _, theorem_) :=
  hash_map.of_list
  (
    [
    ("mp", mp_axiom),
    ("prop_1", prop_1_axiom),
    ("prop_2", prop_2_axiom),
    ("prop_3", prop_3_axiom),
    ("gen", gen_axiom),
    ("pred_1", pred_1_axiom),
    ("pred_2", pred_2_axiom),
    ("eq_1", eq_1_axiom),
    ("eq_2", eq_2_axiom)
    ].map prod.to_sigma
  )
  string.hash
