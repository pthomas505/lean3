import .binders
import metalogic.fol.aux.function_update_ite


set_option pp.parens true


namespace fol

open formula


/-
  D is a domain
-/
structure interpretation (D : Type) : Type :=

/-
  The domain is not empty.
-/
(nonempty : nonempty D)

(pred_const_valuation : string → (list D → Prop))

(eq (x y : D) : pred_const_valuation "=" [x, y] ↔ x = y)


structure interpretation' (D : Type) :=
(i : interpretation D)

/-
  The assignment of predicate variable names to predicate functions on the domain.
  Predicate functions map lists of elements of the domain to {T, F}.
  (list D → Prop) is a predicate function.

  Predicate variables of arity 0 are propositional variables (not propositional constants like T or F).
-/
(var : string → (list D → Prop))

def interpretation'.pred {D : Type} (I : interpretation' D) : pred_name → list D → Prop
| (pred_name.const X) := I.i.pred_const_valuation X
| (pred_name.var X) := I.var X


def default_valuation {D : Type} : string → list D → Prop
| ("=") [x, y] := x = y
| _ _ := prop.inhabited.default

instance (D : Type) [nonempty D] : inhabited (interpretation D) :=
inhabited.mk
⟨
  by apply_instance,
  default_valuation,
  by { intros x y, unfold default_valuation }
⟩


-- The assignment of variables to elements of the domain.
def valuation (D : Type) := var_name → D

instance (D : Type) [inhabited D] : inhabited (valuation D) := by unfold valuation; apply_instance


def holds (D : Type) (I : interpretation' D) : valuation D → formula → Prop
| _ true_ := true
| V (pred_ X xs) := I.pred X (xs.map V)
| V (not_ phi) := ¬ holds V phi
| V (imp_ phi psi) := holds V phi → holds V psi
| V (forall_ x phi) := ∀ (d : D), holds (function.update_ite V x d) phi


def formula.is_valid (F : formula) : Prop :=
  ∀ (D : Type) (I : interpretation' D) (V : valuation D),
    holds D I V F


def coincide
  {D : Type}
  (I J : interpretation' D)
  (V_I V_J : valuation D)
  (phi : formula) :
  Prop :=
  (∀ (P : pred_name) (ds : list D), pred.occurs_in P ds.length phi → (I.pred P ds ↔ J.pred P ds)) ∧
  (∀ (v : var_name), is_free_in v phi → V_I v = V_J v)


lemma holds_congr_var
  {D : Type}
  (I : interpretation' D)
  (V V' : valuation D)
  (F : formula)
  (h1 : ∀ (v : var_name), is_free_in v F → V v = V' v) :
  holds D I V F ↔ holds D I V' F :=
begin
  induction F generalizing V V',
  case formula.true_ : V V' h1
  {
    unfold holds,
  },
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
  (I I' : interpretation' D)
  (V : valuation D)
  (F : formula)
  (h1 : ∀ (P : pred_name) (ds : list D), pred.occurs_in P ds.length F → (I.pred P ds ↔ I'.pred P ds)) :
  holds D I V F ↔ holds D I' V F :=
begin
  induction F generalizing V,
  case formula.true_ : V
  {
    unfold holds,
  },
  case formula.pred_ : X xs V
  {
    unfold pred.occurs_in at h1,
    simp only [bool.of_to_bool_iff, and_imp] at h1,

    unfold holds,
    specialize h1 X (xs.map V),
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
      intros P ds a1,
      apply h1 P ds,
      left,
      exact a1,
    },
    {
      apply psi_ih,
      intros P ds a1,
      apply h1 P ds,
      right,
      exact a1,
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
  (I I' : interpretation' D)
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
    intros P ds a1,
    simp only [h1_left P ds a1],
  }
end


#lint

end fol
