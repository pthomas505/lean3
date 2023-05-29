import .deduct
import metalogic.fol.aux.function_update_ite


set_option pp.parens true


namespace fol

open formula


/-
  Used for the soundness and completeness proofs of classical propositional logic.
-/


def formula.is_prime : formula → Prop
| true_ := false
| (pred_ X xs) := true
| (not_ phi) := false
| (imp_ phi psi) := false
| (forall_ x phi) := true


def formula.prime_set : formula → finset formula
| true_ := ∅
| (pred_ X xs) := {pred_ X xs}
| (not_ phi) := phi.prime_set
| (imp_ phi psi) := phi.prime_set ∪ psi.prime_set
| (forall_ x phi) := {forall_ x phi}


def formula.subst_prime (σ : formula → formula) : formula → formula
| true_ := true_
| (pred_ X xs) := σ (pred_ X xs)
| (not_ phi) := not_ phi.subst_prime
| (imp_ phi psi) := imp_ phi.subst_prime psi.subst_prime
| (forall_ x phi) := σ (forall_ x phi)


@[derive inhabited]
def prop_valuation : Type := formula → bool

def formula.eval_prime (V : prop_valuation) : formula → bool
| true_ := bool.tt
| (pred_ X xs) := V (pred_ X xs)
| (not_ phi) := ! phi.eval_prime
| (imp_ phi psi) := (! phi.eval_prime) || psi.eval_prime
| (forall_ x phi) := V (forall_ x phi)

def formula.is_tauto_prime (P : formula) : Prop :=
  ∀ (V : prop_valuation), P.eval_prime V = bool.tt

def eval_prime_ff_to_not (V : prop_valuation) (P : formula) : formula :=
if formula.eval_prime V P = bool.tt then P else P.not_


lemma eval_prime_prime
  (F : formula)
  (V : prop_valuation)
  (h1 : F.is_prime) :
  F.eval_prime V = V F :=
begin
  induction F,
  case [formula.true_, formula.not_, formula.imp_]
  {
    all_goals
    {
      unfold formula.is_prime at h1,

      contradiction,
    }
  },
  case [formula.pred_, formula.forall_]
  {
    all_goals
    {
      refl,
    }
  },
end


example
  (F : formula)
  (V V' : prop_valuation)
  (h1 : ∀ (H : formula), H ∈ F.prime_set → V H = V' H) :
  F.eval_prime V = F.eval_prime V' :=
begin
  induction F,
  case formula.true_
  {
    unfold formula.eval_prime,
  },
  case [formula.pred_, formula.forall_]
  {
    all_goals
    {
      unfold formula.prime_set at h1,

      unfold formula.eval_prime,
      apply h1,
      simp only [finset.mem_singleton, eq_self_iff_true, and_self],
    },
  },
  case formula.not_ : phi phi_ih
  {
    unfold formula.prime_set at h1,

    unfold formula.eval_prime,
    congr' 1,
    exact phi_ih h1,
  },
  case formula.imp_ : phi psi phi_ih psi_ih
  {
    unfold formula.prime_set at h1,
    simp only [finset.mem_union] at h1,

    unfold formula.eval_prime,
    congr' 1,
    {
      congr' 1,
      apply phi_ih,
      intros H' a1,
      apply h1,
      left,
      exact a1,
    },
    {
      apply psi_ih,
      intros H' a1,
      apply h1,
      right,
      exact a1,
    }
  },
end


lemma eval_prime_subst_prime_eq_eval_prime_eval_prime
  (F : formula)
  (σ : formula → formula)
  (V : prop_valuation) :
  (F.subst_prime σ).eval_prime V =
    F.eval_prime (fun (H : formula), (σ H).eval_prime V) :=
begin
  induction F,
  case [formula.true_, formula.pred_, formula.forall_]
  {
    all_goals
    {
      refl,
    }
  },
  case formula.not_ : phi phi_ih
  {
    unfold formula.subst_prime,
    unfold formula.eval_prime,
    congr,
    exact phi_ih,
  },
  case formula.imp_ : phi psi phi_ih psi_ih
  {
    unfold formula.subst_prime,
    unfold formula.eval_prime,
    congr,
    {
      exact phi_ih,
    },
    {
      exact psi_ih,
    }
  },
end


theorem is_tauto_prime_imp_is_tauto_prime_subst_prime
  (P : formula)
  (h1 : P.is_tauto_prime)
  (σ : formula → formula) :
  (formula.subst_prime σ P).is_tauto_prime :=
begin
  unfold formula.is_tauto_prime at h1,

  unfold formula.is_tauto_prime,
  intros V,
  simp only [eval_prime_subst_prime_eq_eval_prime_eval_prime P σ V],
  apply h1,
end


example
  (P Q R S : formula)
  (V : prop_valuation)
  (σ : formula → formula)
  (h1 : P.eval_prime V = Q.eval_prime V) :
  (S.subst_prime (function.update_ite σ R P)).eval_prime V =
    (S.subst_prime (function.update_ite σ R Q)).eval_prime V :=
begin
  simp only [eval_prime_subst_prime_eq_eval_prime_eval_prime],
  congr' 1,
  funext Q',
  unfold function.update_ite,
  split_ifs,
  {
    exact h1,
  },
  {
    refl,
  }
end


theorem T_13_5
  (P : formula) :
  is_proof (P.imp_ P) :=
begin
  unfold is_proof,

  apply is_deduct.mp_ (P.imp_ (P.imp_ P)),
  {
    apply is_deduct.mp_ (P.imp_ ((P.imp_ P).imp_ P)),
    {
      apply is_deduct.axiom_,
      exact is_axiom.prop_2_ P (P.imp_ P) P,
    },
    {
      apply is_deduct.axiom_,
      exact is_axiom.prop_1_ P (P.imp_ P),
    }
  },
  {
    apply is_deduct.axiom_,
    exact is_axiom.prop_1_ P P,
  },
end

alias T_13_5 <- prop_id


theorem T_13_6_no_deduct
  (P Q : formula) :
  is_proof (P.not_.imp_ (P.imp_ Q)) :=
begin
  apply is_deduct.mp_ (P.not_.imp_ (Q.not_.imp_ P.not_)),
  {
    apply is_deduct.mp_ (P.not_.imp_ ((Q.not_.imp_ P.not_).imp_ (P.imp_ Q))),
    {
      apply is_deduct.axiom_,
      apply is_axiom.prop_2_,
    },
    {
      apply is_deduct.mp_ ((Q.not_.imp_ P.not_).imp_ (P.imp_ Q)),
      {
        apply is_deduct.axiom_,
        apply is_axiom.prop_1_,
      },
      {
        apply is_deduct.axiom_,
        apply is_axiom.prop_3_,
      }
    }
  },
  {
    apply is_deduct.axiom_,
    apply is_axiom.prop_1_,
  }
end


theorem T_14_10
  (F : formula)
  (Δ : set formula)
  (h1 : is_deduct Δ F) :
  ∀ (Γ : set formula), is_deduct (Δ ∪ Γ) F :=
begin
  intros Γ,
  induction h1,
  case is_deduct.axiom_ : h1_phi h1_1
  {
    apply is_deduct.axiom_,
    exact h1_1,
  },
  case is_deduct.assume_ : h1_phi h1_1
  {
    apply is_deduct.assume_,
    squeeze_simp,
    left,
    exact h1_1,
  },
  case is_deduct.mp_ : h1_phi h1_psi h1_1 h1_2 h1_ih_1 h1_ih_2
  {
    apply is_deduct.mp_ h1_phi,
    {
      exact h1_ih_1,
    },
    {
      exact h1_ih_2,
    }
  },
end


theorem T_14_10_comm
  (Q : formula)
  (Δ : set formula)
  (h1 : is_deduct Δ Q) :
  ∀ (Γ : set formula), is_deduct (Γ ∪ Δ) Q :=
begin
  simp only [set.union_comm],
  exact T_14_10 Q Δ h1,
end


theorem C_14_11
  (P : formula)
  (h1 : is_proof P) :
  ∀ (Δ : set formula), is_deduct Δ P :=
begin
  intros Δ,
  obtain s1 := T_14_10 P ∅ h1 Δ,
  simp only [set.empty_union] at s1,
  exact s1,
end

alias C_14_11 <- proof_imp_deduct


-- Deduction Theorem

theorem T_14_3
  (P Q : formula)
  (Δ : set formula)
  (h1 : is_deduct (Δ ∪ {P}) Q) :
  is_deduct Δ (P.imp_ Q) :=
begin
  induction h1,
  case is_deduct.axiom_ : h1_phi h1_1
  {
    apply is_deduct.mp_ h1_phi,
    {
      apply is_deduct.axiom_,
      exact is_axiom.prop_1_ h1_phi P,
    },
    {
      apply is_deduct.axiom_,
      exact h1_1,
    },
  },
  case is_deduct.assume_ : h1_phi h1_1
  {
    simp only [set.union_singleton, set.mem_insert_iff] at h1_1,

    cases h1_1,
    {
      subst h1_1,
      apply proof_imp_deduct,
      exact prop_id h1_phi,
    },
    {
      apply is_deduct.mp_ h1_phi,
      {
        apply is_deduct.axiom_,
        exact is_axiom.prop_1_ h1_phi P,
      },
      {
        apply is_deduct.assume_,
        exact h1_1,
      },
    }
  },
  case is_deduct.mp_ : h1_phi h1_psi h1_1 h1_2 h1_ih_1 h1_ih_2
  {
    apply is_deduct.mp_ (P.imp_ h1_phi),
    {
      apply is_deduct.mp_ (P.imp_ (h1_phi.imp_ h1_psi)),
      {
        apply is_deduct.axiom_,
        exact is_axiom.prop_2_ P h1_phi h1_psi,
      },
      {
        exact h1_ih_1,
      }
    },
    {
      exact h1_ih_2,
    },
  },
end

alias T_14_3 <- deduction_theorem


theorem T_13_6
  (P Q : formula) :
  is_proof (P.not_.imp_ (P.imp_ Q)) :=
begin
  unfold is_proof,

  apply deduction_theorem,
  apply is_deduct.mp_ (Q.not_.imp_ P.not_),
  {
    apply is_deduct.axiom_,
    exact is_axiom.prop_3_ Q P,
  },
  {
    apply is_deduct.mp_ P.not_,
    {
      apply is_deduct.axiom_,
      exact is_axiom.prop_1_ P.not_ Q.not_,
    },
    {
      apply is_deduct.assume_,
      simp only [set.union_singleton, insert_emptyc_eq, set.mem_singleton],
    },
  },
end


theorem T_14_5
  (P : formula) :
  is_proof (P.not_.not_.imp_ P) :=
begin
  unfold is_proof,

  apply deduction_theorem,
  apply is_deduct.mp_ P.not_.not_,
  {
    apply is_deduct.mp_ (P.not_.imp_ P.not_.not_.not_),
    {
      apply is_deduct.axiom_,
      apply is_axiom.prop_3_,
    },
    {
      apply is_deduct.mp_ P.not_.not_,
      {
        apply proof_imp_deduct,
        apply T_13_6,
      },
      {
        apply is_deduct.assume_,
        simp only [set.union_singleton, insert_emptyc_eq, set.mem_singleton],
      }
    }
  },
  {
    apply is_deduct.assume_,
    simp only [set.union_singleton, insert_emptyc_eq, set.mem_singleton_iff],
  }
end


theorem T_14_6
  (P : formula) :
  is_proof (P.imp_ P.not_.not_) :=
begin
  unfold is_proof,

  apply is_deduct.mp_ (P.not_.not_.not_.imp_ P.not_),
  {
    apply is_deduct.axiom_,
    exact is_axiom.prop_3_ P.not_.not_ P,
  },
  {
    apply proof_imp_deduct,
    exact T_14_5 P.not_,
  }
end


theorem T_14_7
  (P Q : formula) :
  is_proof ((P.imp_ Q).imp_ (Q.not_.imp_ P.not_)) :=
begin
  unfold is_proof,

  apply deduction_theorem,
  apply is_deduct.mp_ (P.not_.not_.imp_ Q.not_.not_),
  {
    apply is_deduct.axiom_,
    apply is_axiom.prop_3_,
  },
  {
    apply deduction_theorem,
    apply is_deduct.mp_ Q,
    {
      apply proof_imp_deduct,
      apply T_14_6,
    },
    {
      apply is_deduct.mp_ P,
      {
        apply is_deduct.assume_,
        simp only [set.union_singleton, insert_emptyc_eq, set.mem_insert_iff, set.mem_singleton_iff, eq_self_iff_true, and_true,
  false_or],
      },
      {
        apply is_deduct.mp_ P.not_.not_,
        {
          apply proof_imp_deduct,
          apply T_14_5,
        },
        {
          apply is_deduct.assume_,
          simp only [set.union_singleton, insert_emptyc_eq, set.mem_insert_iff, set.mem_singleton_iff, or_false],
        }
      }
    }
  }
end


theorem T_14_8
  (Q R : formula) :
  is_proof (Q.imp_ (R.not_.imp_ ((Q.imp_ R).not_))) :=
begin
  unfold is_proof,

  apply deduction_theorem,
  apply is_deduct.mp_ ((Q.imp_ R).imp_ R),
  {
    apply proof_imp_deduct,
    apply T_14_7,
  },
  {
    apply deduction_theorem,
    apply is_deduct.mp_ Q,
    {
      apply is_deduct.assume_,
      simp only [set.union_singleton, set.mem_insert_iff, eq_self_iff_true, and_self, true_or],
    },
    {
      apply is_deduct.assume_,
      simp only [set.union_singleton, insert_emptyc_eq, set.mem_insert_iff, set.mem_singleton, or_true],
    }
  }
end


theorem T_14_9
  (P S : formula) :
  is_proof ((S.imp_ P).imp_ ((S.not_.imp_ P).imp_ P)) :=
begin
  unfold is_proof,

  apply deduction_theorem,
  apply is_deduct.mp_ (P.not_.imp_ (S.not_.imp_ P).not_),
  {
    apply is_deduct.axiom_,
    apply is_axiom.prop_3_,
  },
  {
    apply deduction_theorem,
    apply is_deduct.mp_ P.not_,
    {
      apply is_deduct.mp_ S.not_,
      {
        apply proof_imp_deduct,
        apply T_14_8,
      },
      {
        apply is_deduct.mp_ P.not_,
        {
          apply is_deduct.mp_ (S.imp_ P),
          {
            apply proof_imp_deduct,
            apply T_14_7,
          },
          {
            apply is_deduct.assume_,
            simp only [set.union_singleton, insert_emptyc_eq, set.mem_insert_iff, set.mem_singleton, false_or],
          }
        },
        {
          apply is_deduct.assume_,
          simp only [set.union_singleton, insert_emptyc_eq, set.mem_insert_iff, set.mem_singleton_iff, or_false],
        }
      }
    },
    {
      apply is_deduct.assume_,
      simp only [set.union_singleton, insert_emptyc_eq, set.mem_insert_iff, set.mem_singleton_iff, or_false],
    }
  }
end


theorem deduction_theorem_converse
  (P Q : formula)
  (Δ : set formula)
  (h1 : is_deduct Δ (P.imp_ Q)) :
  is_deduct (Δ ∪ {P}) Q :=
begin
  apply is_deduct.mp_ P,
  {
    exact T_14_10 (P.imp_ Q) Δ h1 {P},
  },
  {
    apply is_deduct.assume_,
    simp only [set.union_singleton, set.mem_insert_iff, eq_self_iff_true, true_or],
  },
end


theorem T_14_12
  (P Q : formula)
  (Δ Γ : set formula)
  (h1 : is_deduct Δ P)
  (h2 : is_deduct Γ (P.imp_ Q)) :
  is_deduct (Δ ∪ Γ) Q :=
begin
  apply is_deduct.mp_ P,
  {
    apply T_14_10_comm,
    exact h2,
  },
  {
    apply T_14_10,
    exact h1,
  },
end


theorem C_14_14
  (P Q : formula)
  (Γ : set formula)
  (h1 : is_proof P)
  (h2 : is_deduct Γ (P.imp_ Q)) :
  is_deduct Γ Q :=
begin
  apply is_deduct.mp_ P,
  {
    exact h2,
  },
  {
    apply proof_imp_deduct,
    exact h1,
  },
end

alias C_14_14 <- mp_proof_deduct


theorem C_14_15
  (P Q : formula)
  (Δ : set formula)
  (h1 : is_deduct Δ P)
  (h2 : is_proof (P.imp_ Q)) :
  is_deduct Δ Q :=
begin
  apply is_deduct.mp_ P,
  {
    apply proof_imp_deduct,
    exact h2,
  },
  {
    exact h1,
  },
end

alias C_14_15 <- mp_deduct_proof


theorem T_14_16
  (F : formula)
  (Δ Γ : set formula)
  (h1 : is_deduct Γ F)
  (h2 : ∀ (H : formula), H ∈ Γ → is_deduct Δ H) :
  is_deduct Δ F :=
begin
  induction h1,
  case is_deduct.axiom_ : h1_phi h1_1
  {
    apply is_deduct.axiom_,
    exact h1_1,
  },
  case is_deduct.assume_ : h1_phi h1_1
  {
    exact h2 h1_phi h1_1,
  },
  case is_deduct.mp_ : h1_phi h1_psi h1_1 h1_2 h1_ih_1 h1_ih_2
  {
    exact is_deduct.mp_ h1_phi h1_psi h1_ih_1 h1_ih_2,
  },
end


theorem C_14_17
  (Q : formula)
  (Γ : set formula)
  (h1 : is_deduct Γ Q)
  (h2 : ∀ (P : formula), P ∈ Γ → is_proof P) :
  is_proof Q :=
begin
  unfold is_proof at h2,

  unfold is_proof,
  exact T_14_16 Q ∅ Γ h1 h2,
end


theorem eval_not
  (P : formula)
  (V : prop_valuation) :
  formula.eval_prime V (not_ P) = bool.tt ↔
    ¬ (formula.eval_prime V P = bool.tt) :=
begin
  unfold formula.eval_prime,
  cases formula.eval_prime V P;
  exact dec_trivial,
end


theorem eval_imp
  (P Q : formula)
  (V : prop_valuation) :
  formula.eval_prime V (imp_ P Q) = bool.tt ↔
    ((formula.eval_prime V P = bool.tt) → (formula.eval_prime V Q = bool.tt)) :=
begin
  unfold formula.eval_prime,
  cases formula.eval_prime V P;
  cases formula.eval_prime V Q;
  exact dec_trivial,
end


theorem is_tauto_prop_true :
  true_.is_tauto_prime :=
begin
  unfold formula.is_tauto_prime,
  intro V,
  unfold formula.eval_prime,
end


theorem is_tauto_prop_1
  (P Q : formula) :
  (P.imp_ (Q.imp_ P)).is_tauto_prime :=
begin
  unfold formula.is_tauto_prime,
  intro V,
  simp only [eval_imp],
  tauto,
end


theorem is_tauto_prop_2
  (P Q R : formula) :
  ((P.imp_ (Q.imp_ R)).imp_ ((P.imp_ Q).imp_ (P.imp_ R))).is_tauto_prime :=
begin
  unfold formula.is_tauto_prime,
  intro V,
  simp only [eval_imp],
  tauto,
end


theorem is_tauto_prop_3
  (P Q : formula) :
  (((not_ P).imp_ (not_ Q)).imp_ (Q.imp_ P)).is_tauto_prime :=
begin
  unfold formula.is_tauto_prime,
  intro V,
  simp only [eval_not, eval_imp],
  tauto,
end


theorem is_tauto_mp
  (P Q : formula)
  (h1 : (P.imp_ Q).is_tauto_prime)
  (h2 : P.is_tauto_prime) :
  Q.is_tauto_prime :=
begin
  unfold formula.is_tauto_prime at h1,
  unfold formula.is_tauto_prime at h2,

  unfold formula.is_tauto_prime,
  intro V,
  simp only [eval_imp] at h1,
  apply h1,
  exact h2 V,
end


/-
  Proof of the soundness of classical propositional logic.
-/
example
  (F : formula)
  (h1 : is_prop_proof F) :
  F.is_tauto_prime :=
begin
  induction h1,
  case is_prop_deduct.axiom_ : h1_phi h1_1
  {
    induction h1_1,
    case is_prop_axiom.prop_true_ :
    {
      exact is_tauto_prop_true,
    },
    case is_prop_axiom.prop_1_ : h1_1_phi h1_1_psi
    {
      exact is_tauto_prop_1 h1_1_phi h1_1_psi,
    },
    case is_prop_axiom.prop_2_ : h1_1_phi h1_1_psi h1_1_chi
    {
      exact is_tauto_prop_2 h1_1_phi h1_1_psi h1_1_chi,
    },
    case is_prop_axiom.prop_3_ : h1_1_phi h1_1_psi
    {
      exact is_tauto_prop_3 h1_1_phi h1_1_psi,
    },
  },
  case is_prop_deduct.assume_ : h1_phi h1_1
  {
    squeeze_simp at h1_1,
    contradiction,
  },
  case is_prop_deduct.mp_ : h1_phi h1_psi h1_1 h1_2 h1_ih_1 h1_ih_2
  {
    exact is_tauto_mp h1_phi h1_psi h1_ih_1 h1_ih_2,
  },
end


lemma mem_prime_set_is_prime
  (F F' : formula)
  (h1 : F' ∈ F.prime_set) :
  F'.is_prime :=
begin
  induction F,
  case formula.true_
  {
    unfold formula.prime_set at h1,
    simp only [finset.not_mem_empty] at h1,

    contradiction,
  },
  case [formula.pred_, formula.forall_]
  {
    all_goals
    {
      unfold formula.prime_set at h1,
      simp only [finset.mem_singleton] at h1,

      subst h1,
      unfold formula.is_prime,
    }
  },
  case formula.not_ : phi phi_ih
  {
    unfold formula.prime_set at h1,

    exact phi_ih h1,
  },
  case formula.imp_ : phi psi phi_ih psi_ih
  {
    unfold formula.prime_set at h1,
    simp only [finset.mem_union] at h1,

    tauto,
  },
end


lemma bnot_eq_tt_iff_not_eq_tt
  (b : bool) :
  !b = bool.tt ↔ ¬ b = bool.tt :=
begin
  simp only [bnot_eq_true_eq_eq_ff, eq_ff_eq_not_eq_tt],
end


lemma L_15_7
  (F F' : formula)
  (Δ_U : set formula)
  (V : prop_valuation)
  (Δ_U' : set formula)
  (h1 : coe F.prime_set ⊆ Δ_U)
  (h2 : Δ_U' = Δ_U.image (eval_prime_ff_to_not V))
  (h3 : F' = eval_prime_ff_to_not V F) :
  is_deduct Δ_U' F' :=
begin
  subst h2,
  subst h3,
  induction F,
  case formula.true_
  {
    apply is_deduct.axiom_,
    apply is_axiom.prop_true_,
  },
  case formula.pred_ : X xs
  {
    let F := pred_ X xs,

    unfold formula.prime_set at h1,
    simp only [finset.coe_singleton, set.singleton_subset_iff] at h1,

    unfold eval_prime_ff_to_not,
    unfold formula.eval_prime,
    apply is_deduct.assume_,
    simp only [finset.coe_image, set.mem_image, finset.mem_coe],
    apply exists.intro F,
    tauto,
  },
  case formula.not_ : phi phi_ih
  {
    unfold formula.prime_set at h1,

    unfold eval_prime_ff_to_not at phi_ih,

    unfold eval_prime_ff_to_not,
    unfold formula.eval_prime,

    simp only [bnot_eq_tt_iff_not_eq_tt],
    split_ifs,
    {
      simp only [if_pos h] at phi_ih,
      apply is_deduct.mp_ phi,
      {
        apply proof_imp_deduct,
        apply T_14_6,
      },
      {
        exact phi_ih h1,
      },
    },
    {
      simp only [if_neg h] at phi_ih,
      exact phi_ih h1,
    },
  },
  case formula.imp_ : phi psi phi_ih psi_ih
  {
    unfold formula.prime_set at h1,
    simp only [finset.coe_union, set.union_subset_iff] at h1,
    cases h1,

    unfold eval_prime_ff_to_not at phi_ih,
    unfold eval_prime_ff_to_not at psi_ih,

    unfold eval_prime_ff_to_not,
    unfold formula.eval_prime,
    simp only [bor_eq_true_eq_eq_tt_or_eq_tt],
    simp only [bnot_eq_tt_iff_not_eq_tt],
    split_ifs,
    {
      cases h,
      {
        simp only [if_neg h] at phi_ih,
        apply is_deduct.mp_ phi.not_,
        {
          apply proof_imp_deduct,
          apply T_13_6,
        },
        {
          exact phi_ih h1_left,
        },
      },
      {
        simp only [if_pos h] at psi_ih,

        apply is_deduct.mp_ psi,
        {
          apply is_deduct.axiom_,
          apply is_axiom.prop_1_,
        },
        {
          exact psi_ih h1_right,
        },
      }
    },
    {
      push_neg at h,
      dsimp at h,
      cases h,
      simp only [if_pos h_left] at phi_ih,
      simp only [if_neg h_right] at psi_ih,
      apply is_deduct.mp_ psi.not_,
      {
        apply is_deduct.mp_ phi,
        {
          apply proof_imp_deduct,
          apply T_14_8,
        },
        {
          exact phi_ih h1_left,
        }
      },
      {
        exact psi_ih h1_right,
      },
    }
  },
  case formula.forall_ : x phi phi_ih
  {
    let F := forall_ x phi,

    unfold formula.prime_set at h1,
    simp only [finset.coe_singleton, set.singleton_subset_iff] at h1,

    unfold eval_prime_ff_to_not,
    unfold formula.eval_prime,
    apply is_deduct.assume_,
    simp only [finset.coe_image, set.mem_image, finset.mem_coe],
    apply exists.intro F,
    tauto,
  },
end


lemma T_14_9_deduct
  (P U : formula)
  (Δ : set formula)
  (h1 : is_deduct (Δ ∪ {U}) P)
  (h2 : is_deduct (Δ ∪ {U.not_}) P) :
  is_deduct Δ P :=
begin
  apply is_deduct.mp_ (U.not_.imp_ P),
  {
    apply is_deduct.mp_ (U.imp_ P),
    {
      apply proof_imp_deduct,
      apply T_14_9,
    },
    {
      apply deduction_theorem,
      exact h1,
    },
  },
  {
    apply deduction_theorem,
    exact h2,
  }
end


lemma eval_prime_ff_to_not_of_function_update_ite_tt
  (F F' : formula)
  (V : prop_valuation)
  (h1 : F.is_prime) :
  eval_prime_ff_to_not (function.update_ite V F' bool.tt) F =
    function.update_ite (eval_prime_ff_to_not V) F' F F :=
begin
  induction F,
  case formula.true_
  {
    unfold function.update_ite,
    unfold eval_prime_ff_to_not,
    tauto,
  },
  case [formula.pred_, formula.forall_]
  {
    all_goals
    {
      unfold function.update_ite,
      unfold eval_prime_ff_to_not,
      unfold formula.eval_prime,
      unfold function.update_ite,
      split_ifs; tauto,
    }
  },
  case [formula.not_, formula.imp_]
  {
    all_goals
    {
      unfold formula.is_prime at h1,

      contradiction,
    }
  },
end


lemma eval_prime_ff_to_not_of_function_update_ite_ff
  (F F' : formula)
  (V : prop_valuation)
  (h1 : F.is_prime) :
  eval_prime_ff_to_not (function.update_ite V F' bool.ff) F =
    function.update_ite (eval_prime_ff_to_not V) F' F.not_ F :=
begin
  induction F,
  case formula.true_
  {
    unfold function.update_ite,
    unfold eval_prime_ff_to_not,
    tauto,
  },
  case [formula.pred_, formula.forall_]
  {
    all_goals
    {
      unfold function.update_ite,
      unfold eval_prime_ff_to_not,
      unfold formula.eval_prime,
      unfold function.update_ite,
      split_ifs; tauto,
    }
  },
  case [formula.not_, formula.imp_]
  {
    all_goals
    {
      unfold formula.is_prime at h1,

      contradiction,
    }
  },
end


lemma image_of_eval_prime_ff_to_not_of_function_update_ite
  (U : formula)
  (Δ : set formula)
  (V : prop_valuation)
  (b : bool)
  (h1_Δ: ∀ (U' : formula), (U' ∈ Δ) → U'.is_prime)
  (h1_U: U.is_prime)
  (h2: U ∉ Δ) :
  Δ.image (eval_prime_ff_to_not (function.update_ite V U b)) =
    Δ.image (eval_prime_ff_to_not V) :=
begin
  apply set.image_congr,
  intros U' a1,
  specialize h1_Δ U' a1,
  cases b,
  {
    simp only [eval_prime_ff_to_not_of_function_update_ite_ff U' U V h1_Δ],
    unfold function.update_ite,
    simp only [ite_eq_right_iff],
    intros a2,
    subst a2,
    contradiction,
  },
  {
    simp only [eval_prime_ff_to_not_of_function_update_ite_tt U' U V h1_Δ],
    unfold function.update_ite,
    simp only [ite_eq_right_iff],
    intros a2,
    subst a2,
    contradiction,
  }
end


lemma prop_complete_aux_aux
  (P U : formula)
  (Δ : set formula)
  (h1_Δ : ∀ (U' : formula), U' ∈ Δ → U'.is_prime)
  (h1_U : U.is_prime)
  (h2 : U ∉ Δ)
  (h3 : ∀ (V : prop_valuation), is_deduct ((Δ.image (eval_prime_ff_to_not V)) ∪ {eval_prime_ff_to_not V U}) P) :
  ∀ (V : prop_valuation), is_deduct (Δ.image (eval_prime_ff_to_not V)) P :=
begin
  intros V,
  apply T_14_9_deduct P U (Δ.image (eval_prime_ff_to_not V)),
  {
    specialize h3 (function.update_ite V U bool.tt),
    simp only [image_of_eval_prime_ff_to_not_of_function_update_ite U Δ V bool.tt h1_Δ h1_U h2] at h3,
    simp only [eval_prime_ff_to_not_of_function_update_ite_tt U U V h1_U] at h3,
    unfold function.update_ite at h3,
    simp only [eq_self_iff_true, if_true] at h3,
    exact h3,
  },
  {
    specialize h3 (function.update_ite V U bool.ff),
    simp only [image_of_eval_prime_ff_to_not_of_function_update_ite U Δ V bool.ff h1_Δ h1_U h2] at h3,
    simp only [eval_prime_ff_to_not_of_function_update_ite_ff U U V h1_U] at h3,
    unfold function.update_ite at h3,
    simp only [eq_self_iff_true, if_true] at h3,
    exact h3,
  }
end


theorem prop_complete_aux
  (P : formula)
  (Δ_U : finset formula)
  (h1 : Δ_U ⊆ P.prime_set)
  (h2 : ∀ (V : prop_valuation), is_deduct (Δ_U.image (eval_prime_ff_to_not V)) P) :
  is_deduct ∅ P :=
begin
  induction Δ_U using finset.induction_on,
  case h₁
  {
    simp only [finset.image_empty, finset.coe_empty, forall_const] at h2,

    exact h2,
  },
  case h₂ : U Δ_U Δ_U_1 Δ_U_2
  {
    apply Δ_U_2,
    {
      simp only [finset.insert_subset] at h1,
      cases h1,

      exact h1_right,
    },
    {
      simp only [finset.insert_subset] at h1,
      cases h1,

      simp only [finset.image_insert, finset.coe_insert, finset.coe_image] at h2,

      simp only [finset.coe_image],
      apply prop_complete_aux_aux P U Δ_U,
      {
        intros U' a1,
        apply mem_prime_set_is_prime P U',
        apply h1_right,
        exact a1,
      },
      {
        apply mem_prime_set_is_prime P U,
        exact h1_left,
      },
      {
        exact Δ_U_1,
      },
      {
        simp only [set.union_singleton],
        exact h2,
      }
    }
  },
end


/-
  Proof of the completeness of classical propositional logic.
-/
theorem prop_complete
  (P : formula)
  (h1 : P.is_tauto_prime) :
  is_proof P :=
begin
  unfold is_proof,

  apply prop_complete_aux P P.prime_set,
  {
    refl,
  },
  {
    intros V,
    apply L_15_7 P P P.prime_set V (P.prime_set.image (eval_prime_ff_to_not V)),
    {
      refl,
    },
    {
      simp only [finset.coe_image],
    },
    {
      unfold formula.is_tauto_prime at h1,

      unfold eval_prime_ff_to_not,
      specialize h1 V,
      simp only [if_pos h1],
    }
  }
end


meta def SC : tactic unit :=
`[apply proof_imp_deduct,
  apply prop_complete,
  unfold formula.is_tauto_prime,
  simp only [eval_not, eval_imp],
  tauto]


#lint

end fol
