import tactic

import metalogic.fol.aux.function_update_ite

set_option pp.parens true


namespace nd


/--
  The type of variable names.
-/
@[derive [inhabited, decidable_eq]]
inductive var_name : Type
| mk : string → var_name


/--
  The string representation of variable names.
-/
def var_name.repr : var_name → string
| (var_name.mk name) := name

instance var_name.has_repr : has_repr var_name := has_repr.mk var_name.repr


/--
  The type of predicate names.
-/
@[derive [inhabited, decidable_eq]]
inductive pred_name : Type
| mk : string → pred_name


/--
  The string representation of predicate names.
-/
def pred_name.repr : pred_name → string
| (pred_name.mk name) := name

instance pred_name.has_repr : has_repr pred_name := has_repr.mk pred_name.repr


/--
  The type of formulas.
-/
@[derive [inhabited, decidable_eq]]
inductive formula : Type
| true_ : formula
| false_ : formula
| pred_ : pred_name → list var_name → formula
| not_ : formula → formula
| imp_ : formula → formula → formula
| and_ : formula → formula → formula
| or_ : formula → formula → formula
| iff_ : formula → formula → formula
| forall_ : var_name → formula → formula
| exists_ : var_name → formula → formula


open formula


/--
  The string representation of formulas.
-/
def formula.repr : formula → string
| true_ := "T"
| false_ := "F"
| (pred_ X xs) := sformat!"({X.repr} {xs.repr})"
| (not_ phi) := sformat!"(¬ {phi.repr})"
| (imp_ phi psi) := sformat!"({phi.repr} → {psi.repr})"
| (and_ phi psi) := sformat!"({phi.repr} ∧ {psi.repr})"
| (or_ phi psi) := sformat!"({phi.repr} ∧ {psi.repr})"
| (iff_ phi psi) := sformat!"({phi.repr} ∧ {psi.repr})"
| (forall_ x phi) := sformat!"(∀ {x.repr}. {phi.repr})"
| (exists_ x phi) := sformat!"(∀ {x.repr}. {phi.repr})"

instance formula.has_repr : has_repr formula :=
  has_repr.mk formula.repr


def formula.eq_ (x y : var_name) : formula :=
  pred_ (pred_name.mk "=") [x, y]


@[derive decidable]
def is_free_in (v : var_name) : formula → bool
| true_ := ff
| false_ := ff
| (pred_ _ xs) := v ∈ xs.to_finset
| (not_ phi) := is_free_in phi
| (imp_ phi psi) := is_free_in phi ∨ is_free_in psi
| (and_ phi psi) := is_free_in phi ∨ is_free_in psi
| (or_ phi psi) := is_free_in phi ∨ is_free_in psi
| (iff_ phi psi) := is_free_in phi ∨ is_free_in psi
| (forall_ x phi) := ¬ v = x ∧ is_free_in phi
| (exists_ x phi) := ¬ v = x ∧ is_free_in phi


@[derive decidable]
def fast_admits_aux (v u : var_name) : finset var_name → formula → bool
| _ true_ := tt
| _ false_ := tt
| binders (pred_ X xs) :=
    v ∈ xs →
    u ∉ binders
| binders (not_ phi) := fast_admits_aux binders phi
| binders (imp_ phi psi) := fast_admits_aux binders phi ∧ fast_admits_aux binders psi
| binders (and_ phi psi) := fast_admits_aux binders phi ∧ fast_admits_aux binders psi
| binders (or_ phi psi) := fast_admits_aux binders phi ∧ fast_admits_aux binders psi
| binders (iff_ phi psi) := fast_admits_aux binders phi ∧ fast_admits_aux binders psi
| binders (forall_ x phi) := v = x ∨ fast_admits_aux (binders ∪ {x}) phi
| binders (exists_ x phi) := v = x ∨ fast_admits_aux (binders ∪ {x}) phi


@[derive decidable]
def fast_admits (v u : var_name) (F : formula) : bool :=
  fast_admits_aux v u ∅ F


def fast_replace_free (v t : var_name) : formula → formula
| true_ := true_
| false_ := false_
| (pred_ X xs) :=
    pred_
    X
    (xs.map (fun (x : var_name), if x = v then t else x))
| (not_ phi) := not_ (fast_replace_free phi)
| (imp_ phi psi) := imp_ (fast_replace_free phi) (fast_replace_free psi)
| (and_ phi psi) := and_ (fast_replace_free phi) (fast_replace_free psi)
| (or_ phi psi) := or_ (fast_replace_free phi) (fast_replace_free psi)
| (iff_ phi psi) := iff_ (fast_replace_free phi) (fast_replace_free psi)
| (forall_ x phi) :=
    if v = x
    then forall_ x phi
    else forall_ x (fast_replace_free phi)
| (exists_ x phi) :=
    if v = x
    then exists_ x phi
    else exists_ x (fast_replace_free phi)


@[derive decidable]
def is_alpha_eqv_var : list (var_name × var_name) → var_name → var_name → bool
| [] x y := x = y
| (hd :: tl) x y :=
  (x = hd.fst ∧ y = hd.snd) ∨
    ((¬ x = hd.fst ∧ ¬ y = hd.snd) ∧ is_alpha_eqv_var tl x y)


@[derive decidable]
def is_alpha_eqv_var_list (binders : list (var_name × var_name)) : list var_name → list var_name → bool
| [] [] := tt
| (x_hd :: x_tl) (y_hd :: y_tl) := is_alpha_eqv_var binders x_hd y_hd ∧ (is_alpha_eqv_var_list x_tl y_tl)
| _ _ := ff


@[derive decidable]
def is_alpha_eqv_aux :
  list (var_name × var_name) → formula → formula → bool
| _ true_ true_ := tt
| _ false_ false_ := tt
| binders (pred_ X xs) (pred_ Y ys) :=
  X = Y ∧ is_alpha_eqv_var_list binders xs ys
| binders (not_ phi) (not_ phi') := is_alpha_eqv_aux binders phi phi'
| binders (imp_ phi psi) (imp_ phi' psi') := is_alpha_eqv_aux binders phi phi' ∧ is_alpha_eqv_aux binders psi psi'
| binders (and_ phi psi) (and_ phi' psi') := is_alpha_eqv_aux binders phi phi' ∧ is_alpha_eqv_aux binders psi psi'
| binders (or_ phi psi) (or_ phi' psi') := is_alpha_eqv_aux binders phi phi' ∧ is_alpha_eqv_aux binders psi psi'
| binders (iff_ phi psi) (iff_ phi' psi') := is_alpha_eqv_aux binders phi phi' ∧ is_alpha_eqv_aux binders psi psi'
| binders (forall_ x phi) (forall_ x' phi') := is_alpha_eqv_aux ((x, x') :: binders) phi phi'
| binders (exists_ x phi) (exists_ x' phi') := is_alpha_eqv_aux ((x, x') :: binders) phi phi'
| _ _ _ := ff

@[derive decidable]
def is_alpha_eqv (phi psi : formula) : bool :=
  is_alpha_eqv_aux [] phi psi


@[derive decidable]
def admits_fun_aux (σ : var_name → var_name) :
  finset var_name → formula → bool
| _ true_ := tt
| _ false_ := tt
| binders (pred_ X xs) :=
    ∀ (v : var_name), v ∈ xs → v ∉ binders → σ v ∉ binders 
| binders (not_ phi) := admits_fun_aux binders phi
| binders (imp_ phi psi) := admits_fun_aux binders phi ∧ admits_fun_aux binders psi
| binders (and_ phi psi) := admits_fun_aux binders phi ∧ admits_fun_aux binders psi
| binders (or_ phi psi) := admits_fun_aux binders phi ∧ admits_fun_aux binders psi
| binders (iff_ phi psi) := admits_fun_aux binders phi ∧ admits_fun_aux binders psi
| binders (forall_ x phi) := admits_fun_aux (binders ∪ {x}) phi
| binders (exists_ x phi) := admits_fun_aux (binders ∪ {x}) phi


@[derive decidable]
def admits_fun (σ : var_name → var_name) (phi : formula) : bool :=
  admits_fun_aux σ ∅ phi

def fast_replace_free_fun : (var_name → var_name) → formula → formula
| _ true_ := true_
| _ false_ := false_
| σ (pred_ X xs) := pred_ X (xs.map σ)
| σ (not_ phi) := not_ (fast_replace_free_fun σ phi)
| σ (imp_ phi psi) := imp_ (fast_replace_free_fun σ phi) (fast_replace_free_fun σ psi)
| σ (and_ phi psi) := and_ (fast_replace_free_fun σ phi) (fast_replace_free_fun σ psi)
| σ (or_ phi psi) := or_ (fast_replace_free_fun σ phi) (fast_replace_free_fun σ psi)
| σ (iff_ phi psi) := iff_ (fast_replace_free_fun σ phi) (fast_replace_free_fun σ psi)
| σ (forall_ x phi) := forall_ x (fast_replace_free_fun (function.update_ite σ x x) phi)
| σ (exists_ x phi) := exists_ x (fast_replace_free_fun (function.update_ite σ x x) phi)


def replace_pred_fun
  (τ : pred_name → ℕ → list var_name × formula) : formula → formula
| true_ := true_
| false_ := false_
| (pred_ P ts) :=
  if ts.length = (τ P ts.length).fst.length
  then
  fast_replace_free_fun
    (function.update_list_ite id (τ P ts.length).fst ts) (τ P ts.length).snd
  else
  pred_ P ts
| (not_ phi) := not_ (replace_pred_fun phi)
| (imp_ phi psi) := imp_ (replace_pred_fun phi) (replace_pred_fun psi)
| (and_ phi psi) := and_ (replace_pred_fun phi) (replace_pred_fun psi)
| (or_ phi psi) := or_ (replace_pred_fun phi) (replace_pred_fun psi)
| (iff_ phi psi) := iff_ (replace_pred_fun phi) (replace_pred_fun psi)
| (forall_ x phi) := forall_ x (replace_pred_fun phi)
| (exists_ x phi) := forall_ x (replace_pred_fun phi)


@[derive decidable]
def admits_pred_fun_aux (τ : pred_name → ℕ → list var_name × formula) :
  finset var_name → formula → bool
| _ true_ := tt
| _ false_ := tt
| binders (pred_ P ts) :=
  (admits_fun (function.update_list_ite id (τ P ts.length).fst ts) (τ P ts.length).snd) ∧
 (∀ (x : var_name), x ∈ binders → ¬ (is_free_in x (τ P ts.length).snd ∧ x ∉ (τ P ts.length).fst)) ∧
  ts.length = (τ P ts.length).fst.length
| binders (not_ phi) := admits_pred_fun_aux binders phi
| binders (imp_ phi psi) := admits_pred_fun_aux binders phi ∧ admits_pred_fun_aux binders psi
| binders (and_ phi psi) := admits_pred_fun_aux binders phi ∧ admits_pred_fun_aux binders psi
| binders (or_ phi psi) := admits_pred_fun_aux binders phi ∧ admits_pred_fun_aux binders psi
| binders (iff_ phi psi) := admits_pred_fun_aux binders phi ∧ admits_pred_fun_aux binders psi
| binders (forall_ x phi) := admits_pred_fun_aux (binders ∪ {x}) phi
| binders (exists_ x phi) := admits_pred_fun_aux (binders ∪ {x}) phi


@[derive decidable]
def admits_pred_fun (τ : pred_name → ℕ → list var_name × formula) (phi : formula) : bool :=
  admits_pred_fun_aux τ ∅ phi


inductive is_deduct : finset formula → formula → Prop

| true_intro_
  (Δ : finset formula) :
  is_deduct Δ true_


| false_elim_
  (Δ : finset formula)
  (phi : formula) :
  is_deduct Δ false_ →
  is_deduct Δ phi


| not_intro_
  (Δ : finset formula)
  (phi : formula) :
  is_deduct (Δ ∪ {phi}) false_ →
  is_deduct Δ (not_ phi)

| not_elim_
  (Δ : finset formula)
  (phi : formula) :
  is_deduct Δ (not_ phi) →
  is_deduct Δ phi →
  is_deduct Δ false_


| imp_intro_
  (Δ : finset formula)
  (phi psi : formula) :
  is_deduct (Δ ∪ {phi}) psi →
  is_deduct Δ (phi.imp_ psi)

| imp_elim_
  (Δ : finset formula)
  (phi psi : formula) :
  is_deduct Δ (phi.imp_ psi) →
  is_deduct Δ phi →
  is_deduct Δ psi


| and_intro_
  (Δ : finset formula)
  (phi psi : formula) :
  is_deduct Δ phi →
  is_deduct Δ psi →
  is_deduct Δ (phi.and_ psi)

| and_elim_left_
  (Δ : finset formula)
  (phi psi : formula) :
  is_deduct Δ (phi.and_ psi) →
  is_deduct Δ phi

| and_elim_right_
  (Δ : finset formula)
  (phi psi : formula) :
  is_deduct Δ (phi.and_ psi) →
  is_deduct Δ psi


| or_intro_left_
  (Δ : finset formula)
  (phi psi : formula) :
  is_deduct Δ phi →
  is_deduct Δ (phi.or_ psi)

| or_intro_right_
  (Δ : finset formula)
  (phi psi : formula) :
  is_deduct Δ psi →
  is_deduct Δ (phi.or_ psi)

| or_elim_
  (Δ : finset formula)
  (phi psi chi : formula) :
  is_deduct Δ (phi.or_ psi) →
  is_deduct (Δ ∪ {phi}) chi →
  is_deduct (Δ ∪ {psi}) chi →
  is_deduct Δ chi


| iff_intro_
  (Δ : finset formula)
  (phi psi : formula) :
  is_deduct (Δ ∪ {phi}) psi →
  is_deduct (Δ ∪ {psi}) phi →
  is_deduct Δ (phi.iff_ psi)

| iff_elim_left_
  (Δ : finset formula)
  (phi psi : formula) :
  is_deduct Δ (phi.iff_ psi) →
  is_deduct Δ phi →
  is_deduct Δ psi

| iff_elim_right_
  (Δ : finset formula)
  (phi psi : formula) :
  is_deduct Δ (phi.iff_ psi) →
  is_deduct Δ psi →
  is_deduct Δ phi


-- classical
| contra_
  (Δ : finset formula)
  (phi : formula) :
  is_deduct (Δ ∪ {not_ phi}) false_ →
  is_deduct Δ phi


| refl_
  (Δ : finset formula)
  (x : var_name) :
  is_deduct Δ (formula.eq_ x x)

| subst_
  (Δ : finset formula)
  (phi : formula)
  (x y : var_name) :
  is_deduct Δ (formula.eq_ x y) →
  is_deduct Δ phi →
  fast_admits x y phi →
  is_deduct Δ (fast_replace_free x y phi)


| forall_intro_
  (Δ : finset formula)
  (phi : formula)
  (x : var_name) :
  is_deduct Δ phi →
  (∀ (H : formula), H ∈ Δ → ¬ is_free_in x H) →
  is_deduct Δ (forall_ x phi)


| forall_elim_
  (Δ : finset formula)
  (phi : formula)
  (x y : var_name) :
  is_deduct Δ (forall_ x phi) → 
  fast_admits x y phi → 
  is_deduct Δ (fast_replace_free x y phi)


| exists_intro_
  (Δ : finset formula)
  (phi : formula)
  (x y : var_name) :
  fast_admits x y phi → 
  is_deduct Δ (fast_replace_free x y phi) →
  is_deduct Δ (exists_ x phi)


| exists_elim_
  (Δ : finset formula)
  (phi psi : formula)
  (x : var_name) :
  is_deduct Δ (exists_ x phi) →
  is_deduct (Δ ∪ {phi}) psi →
  (∀ (H : formula), H ∈ Δ → ¬ is_free_in x H) →
  ¬ is_free_in x psi →
  is_deduct Δ psi


| pred_sub_
  (Δ : finset formula)
  (phi : formula)
  (τ : pred_name → ℕ → list var_name × formula) :
  is_deduct Δ phi →
  admits_pred_fun τ phi →
  (∀ (H : formula), H ∈ Δ → admits_pred_fun τ H) →
  is_deduct (Δ.image (replace_pred_fun τ)) (replace_pred_fun τ phi)


| weaken_
  (Δ Δ' : finset formula)
  (phi : formula) :
  is_deduct Δ phi → 
  is_deduct (Δ ∪ Δ') phi


| hyp_
  (Δ : finset formula)
  (phi : formula) :
  phi ∈ Δ →
  is_deduct Δ phi


| alpha_
  (Δ : finset formula)
  (phi psi : formula) :
  is_deduct Δ phi →
  is_alpha_eqv phi psi →
  is_deduct Δ psi

end nd


#lint
