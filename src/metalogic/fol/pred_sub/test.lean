import metalogic.fol.aux.function_update_ite


@[derive [decidable_eq]]
inductive formula : Type
| pred_ : string → list string → formula
| not_ : formula → formula
| imp_ : formula → formula → formula
| forall_ : string → formula → formula

open formula


@[derive decidable]
def is_free_in (v : string) : formula → bool
| (pred_ _ xs) := v ∈ xs.to_finset
| (not_ phi) := is_free_in phi
| (imp_ phi psi) := is_free_in phi ∨ is_free_in psi
| (forall_ x phi) := ¬ v = x ∧ is_free_in phi

@[derive decidable]
def pred_var.occurs_in (P : string) (n : ℕ) : formula → bool
| (pred_ X xs) := X = P ∧ xs.length = n
| (not_ phi) := pred_var.occurs_in phi
| (imp_ phi psi) := pred_var.occurs_in phi ∨ pred_var.occurs_in psi
| (forall_ _ phi) := pred_var.occurs_in phi


structure interpretation (D : Type) : Type :=
(nonempty : nonempty D)
(pred : string → (list D → Prop))

def valuation (D : Type) := string → D


def holds (D : Type) (I : interpretation D) : valuation D → formula → Prop
| V (pred_ X xs) := I.pred X (xs.map V)
| V (not_ phi) := ¬ holds V phi
| V (imp_ phi psi) := holds V phi → holds V psi
| V (forall_ x phi) := ∀ (d : D), holds (function.update_ite V x d) phi


def formula.is_valid (F : formula) : Prop :=
  ∀ (D : Type) (I : interpretation D) (V : valuation D),
    holds D I V F


def coincide
  {D : Type}
  (I J : interpretation D)
  (V_I V_J : valuation D)
  (phi : formula) :
  Prop :=
  (∀ (P : string) (n : ℕ), pred_var.occurs_in P n phi → I.pred P = J.pred P) ∧
  (∀ (v : string), is_free_in v phi → V_I v = V_J v)


def fast_replace_free_fun : (string → string) → formula → formula
| σ (pred_ X xs) := pred_ X (xs.map σ)
| σ (not_ phi) := not_ (fast_replace_free_fun σ phi)
| σ (imp_ phi psi) :=
  imp_ (fast_replace_free_fun σ phi) (fast_replace_free_fun σ psi)
| σ (forall_ x phi) :=
  forall_ x (fast_replace_free_fun (function.update_ite σ x x) phi)


@[derive decidable]
def admits_fun_aux (σ : string → string) :
  finset string → formula → bool
| binders (pred_ X xs) :=
    ∀ (v : string), v ∈ xs → v ∉ binders → σ v ∉ binders 
| binders (not_ phi) := admits_fun_aux binders phi
| binders (imp_ phi psi) := admits_fun_aux binders phi ∧ admits_fun_aux binders psi
| binders (forall_ x phi) := admits_fun_aux (binders ∪ {x}) phi

@[derive decidable]
def admits_fun (σ : string → string) (phi : formula) : bool :=
  admits_fun_aux σ ∅ phi


theorem substitution_theorem_fun
  {D : Type}
  (I : interpretation D)
  (V : valuation D)
  (σ : string → string)
  (phi : formula)
  (h1 : admits_fun σ phi) :
  holds D I (V ∘ σ) phi ↔
    holds D I V (fast_replace_free_fun σ phi) :=
begin
  sorry,
end


theorem coincidence_theorem
  {D : Type}
  (I I' : interpretation D)
  (V V' : valuation D)
  (F : formula)
  (h1 : coincide I I' V V' F) :
  holds D I V F ↔ holds D I' V' F := sorry


def replace_pred_fun
  (τ : string → list string × formula) : formula → formula
| (pred_ P ts) :=
  fast_replace_free_fun
    (function.update_list_ite id (τ P).fst ts) (τ P).snd
| (not_ phi) := not_ (replace_pred_fun phi)
| (imp_ phi psi) := imp_ (replace_pred_fun phi) (replace_pred_fun psi)
| (forall_ x phi) := forall_ x (replace_pred_fun phi)


def admits_pred_fun_aux (τ : string → list string × formula) :
  finset string → formula → bool
| binders (pred_ P ts) :=
  admits_fun (function.update_list_ite id (τ P).fst ts) (τ P).snd ∧
 ∀ (x : string), x ∈ binders → is_free_in x (τ P).snd → ¬ x ∈ (τ P).fst
| binders (not_ phi) := admits_pred_fun_aux binders phi
| binders (imp_ phi psi) := admits_pred_fun_aux binders phi ∧ admits_pred_fun_aux binders psi
| binders (forall_ x phi) := admits_pred_fun_aux (binders ∪ {x}) phi


lemma holds_congr_ind_var
  {D : Type}
  (I : interpretation D)
  (V V' : valuation D)
  (F : formula)
  (h1 : ∀ (v : string), is_free_in v F → V v = V' v) :
  holds D I V F ↔ holds D I V' F :=
begin
  sorry,
end


lemma pred_sub_aux
  (D : Type)
  (I J : interpretation D)
  (V : valuation D)
  (τ : string → list string × formula)
  (binders : finset string)
  (phi : formula)
  (h1 : admits_pred_fun_aux τ binders phi)
  (h2 : ∀ (P : string) (ds : list D),
    J.pred P ds ↔
      holds D I (function.update_list_ite V (τ P).fst ds) (τ P).snd) :
  holds D J V phi ↔ holds D I V (replace_pred_fun τ phi) :=
begin
  induction phi generalizing V binders,
  case formula.pred_ : P ts V binders h1 h2
  {
    unfold admits_pred_fun_aux at h1,
    simp only [bool.of_to_bool_iff] at h1,
    cases h1,

    obtain s1 := substitution_theorem_fun I V (function.update_list_ite id (τ P).fst ts) (τ P).snd h1_left,

    obtain s2 := function.update_list_ite_comp id V (τ P).fst ts,

    simp only [s2] at s1,
    clear s2,

    unfold replace_pred_fun,
    rewrite <- s1,
    clear s1,

    unfold holds,
    simp only [function.comp.right_id],
    apply h2,
  },
  case formula.not_ : phi phi_ih V binders h1 h2
  {
    unfold admits_pred_fun_aux at h1,

    unfold replace_pred_fun,
    unfold holds,
    apply not_congr,
    apply phi_ih,
    apply h1,
    apply h2,
  },
  case formula.imp_ : phi psi phi_ih psi_ih V binders h1 h2
  {
    unfold admits_pred_fun_aux at h1,
    simp only [bool.to_bool_and, bool.to_bool_coe, band_coe_iff] at h1,
    cases h1,

    unfold replace_pred_fun,
    unfold holds,
    apply imp_congr,
    {
      apply phi_ih,
      apply h1_left,
      apply h2,
    },
    {
      apply psi_ih,
      apply h1_right,
      apply h2,
    }
  },
  case formula.forall_ : x phi phi_ih V binders h1 h2
  {
    unfold admits_pred_fun_aux at h1,

    unfold replace_pred_fun,
    unfold holds,
    apply forall_congr,
    intros d,
    apply phi_ih,
    apply h1,
    intros P ds,

    sorry,
  },
end


example
  (phi : formula)
  (τ : string → list string × formula)
  (h1 : admits_pred_fun_aux τ ∅ phi)
  (h2 : phi.is_valid) :
  (replace_pred_fun τ phi).is_valid :=
begin
  unfold formula.is_valid at h2,

  unfold formula.is_valid,
  intros D I V,

  let J : interpretation D := {
    nonempty := I.nonempty,
    pred := fun (P : string) (ds : list D), holds D I (function.update_list_ite V (τ P).fst ds) (τ P).snd
  },

  obtain s1 := pred_sub_aux D I J V τ ∅ phi h1,
  squeeze_simp at s1,

  rewrite <- s1,
  apply h2,
end