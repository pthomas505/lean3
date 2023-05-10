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
def pred.occurs_in (P : string) (n : ℕ) : formula → bool
| (pred_ X xs) := X = P ∧ xs.length = n
| (not_ phi) := pred.occurs_in phi
| (imp_ phi psi) := pred.occurs_in phi ∨ pred.occurs_in psi
| (forall_ _ phi) := pred.occurs_in phi


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
  (∀ (P : string) (n : ℕ) (ds : list D), ds.length = n → pred.occurs_in P n phi → I.pred P ds = J.pred P ds) ∧
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


lemma holds_congr_var
  {D : Type}
  (I : interpretation D)
  (V V' : valuation D)
  (F : formula)
  (h1 : ∀ (v : string), is_free_in v F → V v = V' v) :
  holds D I V F ↔ holds D I V' F :=
begin
  induction F generalizing V V',
  case formula.pred_ : X xs V V' h1
  {
    unfold is_free_in at h1,
    simp only [list.mem_to_finset, bool.of_to_bool_iff] at h1,

    unfold holds,
    congr' 2,
    simp only [list.map_eq_map_iff],
    apply h1,
  },
  case formula.not_ : phi phi_ih V V' h1
  {
    apply not_congr,
    exact phi_ih V V' h1,
  },
  case formula.imp_ : phi psi phi_ih psi_ih V V' h1
  {
    unfold is_free_in at h1,
    simp only [bool.of_to_bool_iff] at h1,

    apply imp_congr,
    {
      apply phi_ih V V',
      intros x a1,
      apply h1,
      left,
      exact a1,
    },
    {
      apply psi_ih V V',
      intros x a1,
      apply h1,
      right,
      exact a1,
    }
  },
  case formula.forall_ : x phi phi_ih V V' h1
  {
    unfold is_free_in at h1,
    simp only [bool.of_to_bool_iff, and_imp] at h1,

    unfold holds,
    apply forall_congr,
    intros d,
    apply phi_ih,
    intros v a1,
    unfold function.update_ite,
    split_ifs,
    {
      refl,
    },
    {
      exact h1 v h a1,
    }
  },
end


lemma holds_congr_pred
  {D : Type}
  (I I' : interpretation D)
  (V : valuation D)
  (F : formula)
  (h1 : ∀ (P : string) (n : ℕ) (ds : list D), ds.length = n → pred.occurs_in P n F → I.pred P ds = I'.pred P ds) :
  holds D I V F ↔ holds D I' V F :=
begin
  induction F generalizing V,
  case formula.pred_ : X xs V
  {
    unfold pred.occurs_in at h1,
    simp only [bool.of_to_bool_iff, and_imp] at h1,

    unfold holds,
    specialize h1 X xs.length (xs.map V),
    simp only [eq_self_iff_true, list.length_map, eq_iff_iff, forall_true_left] at h1,
    simp only [h1],
  },
  case formula.not_ : phi phi_ih V
  {
    unfold pred.occurs_in at h1,

    unfold holds,
    apply not_congr,
    apply phi_ih h1,
  },
  case formula.imp_ : phi psi phi_ih psi_ih V
  {
    unfold pred.occurs_in at h1,
    simp only [bool.of_to_bool_iff] at h1,

    unfold holds,
    apply imp_congr,
    {
      apply phi_ih,
      intros P n ds a1 a2,
      apply h1 P n ds a1,
      left,
      exact a2,
    },
    {
      apply psi_ih,
      intros P n ds a1 a2,
      apply h1 P n ds a1,
      right,
      exact a2,
    }
  },
  case formula.forall_ : x phi phi_ih V
  {
    unfold pred.occurs_in at h1,

    unfold holds,
    apply forall_congr,
    intros d,
    apply phi_ih h1,
  },
end


theorem coincidence_theorem
  {D : Type}
  (I I' : interpretation D)
  (V V' : valuation D)
  (F : formula)
  (h1 : coincide I I' V V' F) :
  holds D I V F ↔ holds D I' V' F :=
begin
  unfold coincide at h1,
  cases h1,

  transitivity holds D I V' F,
  {
    apply holds_congr_var,
    exact h1_right,
  },
  {
    apply holds_congr_pred,
    intros P n ds a1 a2,
    simp only [h1_left P n ds a1 a2],
  }
end


-- variable substitution

lemma substitution_fun_theorem_aux
  {D : Type}
  (I : interpretation D)
  (V V' : valuation D)
  (σ σ' : string → string)
  (binders : finset string)
  (F : formula)
  (h1 : admits_fun_aux σ binders F)
  (h2 : ∀ (v : string), v ∈ binders ∨ σ' v ∉ binders → (V v = V' (σ' v)))
  (h2' : ∀ (v : string), v ∈ binders → v = σ' v)
  (h3 : ∀ (v : string), v ∉ binders → σ' v = σ v) :
  holds D I V F ↔
    holds D I V' (fast_replace_free_fun σ' F) :=
begin
  induction F generalizing binders V V' σ σ',
  case formula.pred_ : X xs binders V V' σ σ' h1 h2 h2' h3
  {
    unfold admits_fun_aux at h1,
    simp only [bool.of_to_bool_iff] at h1,

    unfold fast_replace_free_fun,
    unfold holds,
    congr' 2,
    simp only [list.map_map],
    simp only [list.map_eq_map_iff],
    intros v a1,
    apply h2,
    by_cases c1 : v ∈ binders,
    {
      left,
      exact c1,
    },
    {
      right,
      simp only [h3 v c1],
      exact h1 v a1 c1,
    }
  },
  case formula.not_ : phi phi_ih binders V V' σ σ' h1 h2 h2' h3
  {
    unfold admits_fun_aux at h1,

    unfold fast_replace_free_fun,
    unfold holds,
    apply not_congr,
    exact phi_ih binders V V' σ σ' h1 h2 h2' h3,
  },
  case formula.imp_ : phi psi phi_ih psi_ih binders V V' σ σ' h1 h2 h2' h3
  {
    unfold admits_fun_aux at h1,
    simp only [bool.of_to_bool_iff] at h1,
    cases h1,

    unfold holds,
    apply imp_congr,
    {
      exact phi_ih binders V V' σ σ' h1_left h2 h2' h3,
    },
    {
      exact psi_ih binders V V' σ σ' h1_right h2 h2' h3,
    }
  },
  case formula.forall_ : x phi phi_ih binders V V' σ σ' h1 h2 h2' h3
  {
    unfold admits_fun_aux at h1,

    unfold fast_replace_free_fun,
    unfold holds,
    apply forall_congr,
    intros d,

    apply phi_ih (binders ∪ {x}) (function.update_ite V x d) (function.update_ite V' x d) σ (function.update_ite σ' x x) h1,
    {
      intros v a1,
      unfold function.update_ite at a1,
      simp only [finset.mem_union, finset.mem_singleton, ite_eq_left_iff] at a1,
      push_neg at a1,

      unfold function.update_ite,
      split_ifs,
      {
        refl,
      },
      {
        subst h_1,
        tauto,
      },
      {
        simp only [if_neg h] at a1,
        apply h2,
        tauto,
      },
    },
    {
      intros v a1,
      simp only [finset.mem_union, finset.mem_singleton] at a1,

      unfold function.update_ite,
      split_ifs,
      {
        exact h,
      },
      {
        tauto,
      },
    },
    {
      intros v a1,
      simp only [finset.mem_union, finset.mem_singleton] at a1,
      push_neg at a1,
      cases a1,
      unfold function.update_ite,
      simp only [if_neg a1_right],
      exact h3 v a1_left,
    },
  },
end


theorem substitution_fun_theorem
  {D : Type}
  (I : interpretation D)
  (V : valuation D)
  (σ : string → string)
  (F : formula)
  (h1 : admits_fun σ F) :
  holds D I (V ∘ σ) F ↔
    holds D I V (fast_replace_free_fun σ F) :=
begin
  apply substitution_fun_theorem_aux I (V ∘ σ) V σ σ ∅ F h1,
  {
    simp only [finset.not_mem_empty, not_false_iff, false_or, eq_self_iff_true, forall_const],
  },
  {
    simp only [finset.not_mem_empty, is_empty.forall_iff, forall_const],
  },
  {
    simp only [finset.not_mem_empty, not_false_iff, eq_self_iff_true, forall_const],
  },
end


theorem substitution_fun_valid
  (σ : string → string)
  (F : formula)
  (h1 : admits_fun σ F)
  (h2 : F.is_valid) :
  (fast_replace_free_fun σ F).is_valid :=
begin
  unfold formula.is_valid at h2,

  unfold formula.is_valid,
  intros D I V,
  rewrite <- substitution_fun_theorem I V σ F h1,
  exact h2 D I (V ∘ σ),
end


-- predicate substitution

/--
  is_pred_sub A P zs H B := The formula A is said to be transformed into the formula B by a substitution of H* for P z₁ ... zₙ, abbreviated: Sub A (P zⁿ / H*) B, iff B is obtained from A upon replacing in A each occurrence of a derivative of the name form P z₁ ... zₙ by the corresponding derivative of the substituend H*, provided that: (i) P does not occur in a component formula (∀ x A₁) of A if x is a parameter of H*, and (ii) the name variable zₖ, k = 1, ..., n, is not free in a component formula (∀ x H) of H* if P t₁ ... tₙ occurs in A with x occurring in tₖ. If conditions (i) and (ii) are not satisfied, then the indicated substitution for predicate variables is left undefined.
-/
inductive is_pred_sub (P : string) (zs : list string) (H : formula) : formula → formula → Prop

/-
  If A is an atomic formula not containing P then Sub A (P zⁿ / H*) A.
-/
| pred_not_occurs_in
  (X : string) (ts : list string) :
  ¬ (X = P ∧ ts.length = zs.length) →
  is_pred_sub (pred_ X ts) (pred_ X ts)

  /-
  If A = P t₁ ... tₙ and Sf H* (zⁿ / tⁿ) B, then Sub A (P zⁿ / H*) B.

  Sf H* (zⁿ / tⁿ) B :=
    admits_fun (function.update_list_ite id zs.to_list ts.to_list) H* ∧ 
    fast_replace_free_fun (function.update_list_ite id zs.to_list ts.to_list) H* = B
  -/
| pred_occurs_in
  (X : string) (ts : list string) :
  X = P ∧ ts.length = zs.length →
  admits_fun (function.update_list_ite id zs ts) H →
  is_pred_sub (pred_ P ts) (fast_replace_free_fun (function.update_list_ite id zs ts) H)

/-
  If A = (¬ A₁) and Sub A₁ (P zⁿ / H*) B₁, then Sub A (P zⁿ / H*) (¬ B₁).
-/
| not_
  (phi : formula)
  (phi' : formula) :
  is_pred_sub phi phi' →
  is_pred_sub phi.not_ phi'.not_

/-
  If A = (A₁ → A₂), Sub A₁ (P zⁿ / H*) B₁, and Sub A₂ (P zⁿ / H*) B₂, then Sub A (P zⁿ / H*) (B₁ → B₁).
-/
| imp_
  (phi psi : formula)
  (phi' psi' : formula) :
  is_pred_sub phi phi' →
  is_pred_sub psi psi' →
  is_pred_sub (phi.imp_ psi) (phi'.imp_ psi')

/-
  If A = (∀ x A₁) and P does not occur in A then Sub A (P zⁿ / H*) A.

  If A = (∀ x A₁), P occurs in A, x is not free in H*, and Sub A₁ (P zⁿ / H*) B₁, then Sub A (P zⁿ / H*) (∀ x B₁).
-/
| forall_
  (x : string)
  (phi : formula)
  (phi' : formula) :
  ¬ is_free_in x H →
  is_pred_sub phi phi' →
  is_pred_sub (forall_ x phi) (forall_ x phi')


lemma pred_sub_aux
  (D : Type)
  (I J : interpretation D)
  (V : valuation D)
  (A : formula)
  (P : string)
  (zs : list string)
  (H : formula)
  (B : formula)
  (h1 : is_pred_sub P zs H A B)
  (h2 : ∀ (ds : list D), ds.length = zs.length → (holds D I (function.update_list_ite V zs ds) H ↔ J.pred P ds))
  (h3 : ∀ (Q : string) (n : ℕ) (ds : list D), ds.length = n → ¬ (Q = P ∧ zs.length = n) → (I.pred Q ds ↔ J.pred Q ds)) :
  holds D I V B ↔ holds D J V A :=
begin
  induction h1 generalizing V,
  case is_pred_sub.pred_not_occurs_in : h1_X h1_ts h1_1 V h2
  {
    simp only [not_and] at h1_1,

    apply coincidence_theorem,
    unfold coincide,
    split,
    {
      unfold pred.occurs_in,
      intros X n ds a1 a2,
      simp only [bool.of_to_bool_iff] at a2,
      cases a2,
      subst a2_left,
      subst a2_right,
      ext xs,
      apply h3 h1_X h1_ts.length ds a1,
      simp only [not_and],
      tauto,      
    },
    {
      simp only [eq_self_iff_true, implies_true_iff],
    }
  },
  case is_pred_sub.pred_occurs_in : h1_X h1_ts h1_1 h1_2 V h2
  {
    obtain s1 := substitution_fun_theorem I V (function.update_list_ite id zs h1_ts) H h1_2,

    obtain s2 := function.update_list_ite_comp id V zs h1_ts,

    simp only [s2] at s1,
    simp only [function.comp.right_id] at s1,

    unfold holds,
    specialize h2 (list.map V h1_ts),
    simp only [s1] at h2,
    cases h1_1,
    apply h2,
    squeeze_simp,
    exact h1_1_right,
  },
  case is_pred_sub.not_ : h1_phi h1_phi' h1_1 h1_ih V h2
  {
    unfold holds,
    apply not_congr,
    exact h1_ih V h2,
  },
  case is_pred_sub.imp_ : h1_phi h1_psi h1_phi' h1_psi' h1_1 h1_2 h1_ih_1 h1_ih_2 V h2
  {
    unfold holds,
    apply imp_congr,
    {
      exact h1_ih_1 V h2,
    },
    {
      exact h1_ih_2 V h2,
    },
  },
  case is_pred_sub.forall_ : h1_x h1_phi h1_phi' h1_1 h1_2 h1_ih V h2
  {
    unfold holds,
    apply forall_congr,
    intros d,
    apply h1_ih,
    intros ds a1,
    specialize h2 ds a1,

    have s1 : holds D I (function.update_list_ite (function.update_ite V h1_x d) zs ds) H ↔ holds D I (function.update_list_ite V zs ds) H,
    {
      apply coincidence_theorem,
      unfold coincide,
      split,
      {
        simp only [eq_iff_iff, iff_self, implies_true_iff, forall_const],
      },
      {
        intros v a1,
        apply function.update_list_ite_update_ite,
        intros contra,
        subst contra,
        contradiction,
      }
    },

    simp only [h2] at s1,
    exact s1,
  },
end


example
  (phi phi' : formula)
  (P : string)
  (zs : list string)
  (H : formula)
  (h1 : is_pred_sub P zs H phi phi')
  (h2 : phi.is_valid) :
  phi'.is_valid :=
begin
  unfold formula.is_valid at h2,

  unfold formula.is_valid,
  intros D I V,

  let J : interpretation D := {
    nonempty := I.nonempty,
    pred := fun (Q : string) (ds : list D), sorry
  },

  obtain s1 := pred_sub_aux D I J V phi P zs H phi' h1,
  squeeze_simp at s1,
  rewrite s1,
  apply h2,
  intros ds,
  sorry,
  intros Q n ds a1 a2,
  rewrite <- a1 at a2,

end


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


example (D : Type) (P : string)
  (H A B : formula)
  (h1_x : string)
  (h1_A₁ h1_B₁ : formula)
  (v : string)
  (I J : interpretation D)
  (zs : list string)
  (h2 : ∀ (Q : string) (ds : list D),
          (¬(P = Q)) → (I.pred Q ds ↔ J.pred Q ds))
--  (h1_1 : (↥(P.occurs_in (forall_ h1_x h1_A₁))))
--  (h1_2 : (¬((h1_x.is_free_in H))))
  (V : valuation D)
  (d : D)
  (ds : list D)
--  (a1 : (↥(v.is_free_in H)))
  (h3 : ¬ h1_x = v) :
  (function.update_list_ite (function.update_ite V h1_x d) zs ds v =
   function.update_list_ite V zs ds v) :=
begin
  sorry,
end



lemma pred_sub_aux
  (D : Type)
  (I J : interpretation D)
  (V V' : valuation D)
  (τ : string → list string × formula)
  (binders : finset string)
  (phi : formula)
  (h1 : admits_pred_fun_aux τ binders phi)
  (h2 : ∀ (P : string) (ds : list D),
    J.pred P ds ↔
      holds D I (function.update_list_ite V (τ P).fst ds) (τ P).snd)
  (h3 : ∀ (P : string) (x : string), x ∉ binders → V x = V' x)
  (h3' : ∀ (P : string) (x : string), x ∉ (τ P).fst → V x = V' x) :
  holds D J V phi ↔ holds D I V' (replace_pred_fun τ phi) :=
begin
  induction phi generalizing V V' binders,
  case formula.pred_ : P ts V V' binders h1 h2
  {
    unfold admits_pred_fun_aux at h1,
    simp only [bool.of_to_bool_iff] at h1,
    cases h1,

    obtain s1 := substitution_fun_theorem I V' (function.update_list_ite id (τ P).fst ts) (τ P).snd h1_left,

    obtain s2 := function.update_list_ite_comp id V' (τ P).fst ts,

    simp only [s2] at s1,
    clear s2,

    squeeze_simp at s1,


    unfold replace_pred_fun,
    rewrite <- s1,
    unfold holds,
    rewrite h2,
    apply holds_congr_var,
    intros v a1,
    clear s1,

    by_cases c1 : v ∈ binders,
    {
      specialize h1_right v c1 a1,
      specialize h3' P v h1_right,
      rewrite function.update_list_ite_not_mem V,
      rewrite function.update_list_ite_not_mem V',
      exact h3',
      exact h1_right,
      exact h1_right,
    },
    {
      specialize h3 P v c1,
      by_cases c2 : v ∈ (τ P).fst,
      {
        sorry,
      },
      {
        rewrite function.update_list_ite_not_mem,
        rewrite function.update_list_ite_not_mem,
        exact h3,
        exact c2,
        exact c2,
      }
    }
  },
  case formula.not_ : phi_ᾰ phi_ih V V' binders h1 h2 h3 h3'
  { admit },
  case formula.imp_ : phi_ᾰ phi_ᾰ_1 phi_ih_ᾰ phi_ih_ᾰ_1 V V' binders h1 h2 h3 h3'
  { admit },
  case formula.forall_ : x phi phi_ih V V' binders h1 h2
  {
    unfold admits_pred_fun_aux at h1,

    unfold replace_pred_fun,
    unfold holds,
    apply forall_congr,
    intros d,
    apply phi_ih,
    {
      apply h1,
    },
    {
      intros P ds,
      specialize h2 P ds,
      rewrite h2,
      sorry,
    },
    {
    intros P v a1,
    unfold function.update_ite,
    split_ifs,
    refl,
    apply h3 P,
    squeeze_simp at a1,
    push_neg at a1,
    cases a1,
    exact a1_left,
    },
    {
      intros P v a1,
      unfold function.update_ite,
      split_ifs,
      refl,
      apply h3' P v a1,
    }
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

  obtain s1 := pred_sub_aux D I J V V τ ∅ phi h1,
  squeeze_simp at s1,

  rewrite <- s1,
  apply h2,
end