import .deduct
import metalogic.fol.aux.function_update_ite


set_option pp.parens true


namespace fol

open formula


/-
  Used for the soundness and completeness proofs of classical propositional logic.
-/


def formula.is_prime : formula → Prop
| (true_) := false
| (pred_ name args) := true
| (not_ phi) := false
| (imp_ phi psi) := false
| (forall_ x phi) := true


def formula.prime_set : formula → finset formula
| (true_) := ∅
| (pred_ name args) := {pred_ name args}
| (not_ phi) := phi.prime_set
| (imp_ phi psi) := phi.prime_set ∪ psi.prime_set
| (forall_ x phi) := {forall_ x phi}


def formula.subst_prime (σ : formula → formula) : formula → formula
| (true_) := true_
| (pred_ name args) := σ (pred_ name args)
| (not_ phi) := not_ phi.subst_prime
| (imp_ phi psi) := imp_ phi.subst_prime psi.subst_prime
| (forall_ x phi) := σ (forall_ x phi)


@[derive inhabited]
def prop_valuation : Type := formula → bool

def formula.eval_prime (val : prop_valuation) : formula → bool
| (true_) := bool.tt
| (pred_ name args) := val (pred_ name args)
| (not_ phi) := ! phi.eval_prime
| (imp_ phi psi) := (! phi.eval_prime) || psi.eval_prime
| (forall_ x phi) := val (forall_ x phi)

def formula.is_tauto_prime (phi : formula) : Prop :=
  ∀ (val : prop_valuation), phi.eval_prime val = bool.tt

def eval_prime_ff_to_not (val : prop_valuation) (phi : formula) : formula :=
if formula.eval_prime val phi = bool.tt then phi else phi.not_


lemma eval_prime_prime
  (phi : formula)
  (val : prop_valuation)
  (h1 : phi.is_prime) :
  phi.eval_prime val = val phi :=
begin
  induction phi,
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
  (phi : formula)
  (val val' : prop_valuation)
  (h1 : ∀ (psi : formula), psi ∈ phi.prime_set → val psi = val' psi) :
  phi.eval_prime val = phi.eval_prime val' :=
begin
  induction phi,
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
  case formula.not_ : phi P_ih
  {
    unfold formula.prime_set at h1,

    unfold formula.eval_prime,
    congr' 1,
    exact P_ih h1,
  },
  case formula.imp_ : phi psi P_ih Q_ih
  {
    unfold formula.prime_set at h1,
    simp only [finset.mem_union] at h1,

    unfold formula.eval_prime,
    congr' 1,
    {
      congr' 1,
      apply P_ih,
      intros psi' a1,
      apply h1,
      left,
      exact a1,
    },
    {
      apply Q_ih,
      intros psi' a1,
      apply h1,
      right,
      exact a1,
    }
  },
end


lemma eval_prime_subst_prime_eq_eval_prime_eval_prime
  (phi : formula)
  (σ : formula → formula)
  (val : prop_valuation) :
  (phi.subst_prime σ).eval_prime val =
    phi.eval_prime (fun (psi : formula), (σ psi).eval_prime val) :=
begin
  induction phi,
  case [formula.true_, formula.pred_, formula.forall_]
  {
    all_goals
    {
      refl,
    }
  },
  case formula.not_ : phi P_ih
  {
    unfold formula.subst_prime,
    unfold formula.eval_prime,
    congr,
    exact P_ih,
  },
  case formula.imp_ : phi psi P_ih Q_ih
  {
    unfold formula.subst_prime,
    unfold formula.eval_prime,
    congr,
    {
      exact P_ih,
    },
    {
      exact Q_ih,
    }
  },
end


theorem is_tauto_prime_imp_is_tauto_prime_subst_prime
  (phi : formula)
  (h1 : phi.is_tauto_prime)
  (σ : formula → formula) :
  (formula.subst_prime σ phi).is_tauto_prime :=
begin
  unfold formula.is_tauto_prime at h1,

  unfold formula.is_tauto_prime,
  intros val,
  simp only [eval_prime_subst_prime_eq_eval_prime_eval_prime phi σ val],
  apply h1,
end


example
  (phi psi chi theta : formula)
  (val : prop_valuation)
  (σ : formula → formula)
  (h1 : phi.eval_prime val = psi.eval_prime val) :
  (theta.subst_prime (function.update_ite σ chi phi)).eval_prime val =
    (theta.subst_prime (function.update_ite σ chi psi)).eval_prime val :=
begin
  simp only [eval_prime_subst_prime_eq_eval_prime_eval_prime],
  congr' 1,
  funext psi',
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
  (phi : formula) :
  is_proof (phi.imp_ phi) :=
begin
  unfold is_proof,

  apply is_deduct.mp_ (phi.imp_ (phi.imp_ phi)),
  {
    apply is_deduct.mp_ (phi.imp_ ((phi.imp_ phi).imp_ phi)),
    {
      apply is_deduct.axiom_,
      exact is_axiom.prop_2_ phi (phi.imp_ phi) phi,
    },
    {
      apply is_deduct.axiom_,
      exact is_axiom.prop_1_ phi (phi.imp_ phi),
    }
  },
  {
    apply is_deduct.axiom_,
    exact is_axiom.prop_1_ phi phi,
  },
end

alias T_13_5 <- prop_id


theorem T_13_6_no_deduct
  (phi psi : formula) :
  is_proof (phi.not_.imp_ (phi.imp_ psi)) :=
begin
  apply is_deduct.mp_ (phi.not_.imp_ (psi.not_.imp_ phi.not_)),
  {
    apply is_deduct.mp_ (phi.not_.imp_ ((psi.not_.imp_ phi.not_).imp_ (phi.imp_ psi))),
    {
      apply is_deduct.axiom_,
      apply is_axiom.prop_2_,
    },
    {
      apply is_deduct.mp_ ((psi.not_.imp_ phi.not_).imp_ (phi.imp_ psi)),
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
  (psi : formula)
  (Δ : set formula)
  (h1 : is_deduct Δ psi) :
  ∀ (Γ : set formula), is_deduct (Δ ∪ Γ) psi :=
begin
  intros Γ,
  induction h1,
  case is_deduct.axiom_ : h1_P h1_1
  {
    apply is_deduct.axiom_,
    exact h1_1,
  },
  case is_deduct.assume_ : h1_P h1_1
  {
    apply is_deduct.assume_,
    simp only [set.mem_union_eq],
    left,
    exact h1_1,
  },
  case is_deduct.mp_ : h1_P h1_Q h1_1 h1_2 h1_ih_1 h1_ih_2
  {
    apply is_deduct.mp_ h1_P,
    {
      exact h1_ih_1,
    },
    {
      exact h1_ih_2,
    }
  },
end


theorem T_14_10_comm
  (psi : formula)
  (Δ : set formula)
  (h1 : is_deduct Δ psi) :
  ∀ (Γ : set formula), is_deduct (Γ ∪ Δ) psi :=
begin
  simp only [set.union_comm],
  exact T_14_10 psi Δ h1,
end


theorem C_14_11
  (phi : formula)
  (h1 : is_proof phi) :
  ∀ (Δ : set formula), is_deduct Δ phi :=
begin
  intros Δ,
  obtain s1 := T_14_10 phi ∅ h1 Δ,
  simp only [set.empty_union] at s1,
  exact s1,
end

alias C_14_11 <- proof_imp_deduct


-- Deduction Theorem

theorem T_14_3
  (phi psi : formula)
  (Δ : set formula)
  (h1 : is_deduct (Δ ∪ {phi}) psi) :
  is_deduct Δ (phi.imp_ psi) :=
begin
  induction h1,
  case is_deduct.axiom_ : h1_P h1_1
  {
    apply is_deduct.mp_ h1_P,
    {
      apply is_deduct.axiom_,
      exact is_axiom.prop_1_ h1_P phi,
    },
    {
      apply is_deduct.axiom_,
      exact h1_1,
    },
  },
  case is_deduct.assume_ : h1_P h1_1
  {
    simp only [set.union_singleton, set.mem_insert_iff] at h1_1,

    cases h1_1,
    {
      subst h1_1,
      apply proof_imp_deduct,
      exact prop_id h1_P,
    },
    {
      apply is_deduct.mp_ h1_P,
      {
        apply is_deduct.axiom_,
        exact is_axiom.prop_1_ h1_P phi,
      },
      {
        apply is_deduct.assume_,
        exact h1_1,
      },
    }
  },
  case is_deduct.mp_ : h1_P h1_Q h1_1 h1_2 h1_ih_1 h1_ih_2
  {
    apply is_deduct.mp_ (phi.imp_ h1_P),
    {
      apply is_deduct.mp_ (phi.imp_ (h1_P.imp_ h1_Q)),
      {
        apply is_deduct.axiom_,
        exact is_axiom.prop_2_ phi h1_P h1_Q,
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
  (phi psi : formula) :
  is_proof (phi.not_.imp_ (phi.imp_ psi)) :=
begin
  unfold is_proof,

  apply deduction_theorem,
  apply is_deduct.mp_ (psi.not_.imp_ phi.not_),
  {
    apply is_deduct.axiom_,
    exact is_axiom.prop_3_ psi phi,
  },
  {
    apply is_deduct.mp_ phi.not_,
    {
      apply is_deduct.axiom_,
      exact is_axiom.prop_1_ phi.not_ psi.not_,
    },
    {
      apply is_deduct.assume_,
      simp only [set.union_singleton, insert_emptyc_eq, set.mem_singleton],
    },
  },
end


theorem T_14_5
  (phi : formula) :
  is_proof (phi.not_.not_.imp_ phi) :=
begin
  unfold is_proof,

  apply deduction_theorem,
  apply is_deduct.mp_ phi.not_.not_,
  {
    apply is_deduct.mp_ (phi.not_.imp_ phi.not_.not_.not_),
    {
      apply is_deduct.axiom_,
      apply is_axiom.prop_3_,
    },
    {
      apply is_deduct.mp_ phi.not_.not_,
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
  (phi : formula) :
  is_proof (phi.imp_ phi.not_.not_) :=
begin
  unfold is_proof,

  apply is_deduct.mp_ (phi.not_.not_.not_.imp_ phi.not_),
  {
    apply is_deduct.axiom_,
    exact is_axiom.prop_3_ phi.not_.not_ phi,
  },
  {
    apply proof_imp_deduct,
    exact T_14_5 phi.not_,
  }
end


theorem T_14_7
  (phi psi : formula) :
  is_proof ((phi.imp_ psi).imp_ (psi.not_.imp_ phi.not_)) :=
begin
  unfold is_proof,

  apply deduction_theorem,
  apply is_deduct.mp_ (phi.not_.not_.imp_ psi.not_.not_),
  {
    apply is_deduct.axiom_,
    apply is_axiom.prop_3_,
  },
  {
    apply deduction_theorem,
    apply is_deduct.mp_ psi,
    {
      apply proof_imp_deduct,
      apply T_14_6,
    },
    {
      apply is_deduct.mp_ phi,
      {
        apply is_deduct.assume_,
        simp only [set.union_singleton, insert_emptyc_eq, set.mem_insert_iff, set.mem_singleton_iff, eq_self_iff_true, and_true,
  false_or],
      },
      {
        apply is_deduct.mp_ phi.not_.not_,
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
  (psi chi : formula) :
  is_proof (psi.imp_ (chi.not_.imp_ ((psi.imp_ chi).not_))) :=
begin
  unfold is_proof,

  apply deduction_theorem,
  apply is_deduct.mp_ ((psi.imp_ chi).imp_ chi),
  {
    apply proof_imp_deduct,
    apply T_14_7,
  },
  {
    apply deduction_theorem,
    apply is_deduct.mp_ psi,
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
  (phi theta : formula) :
  is_proof ((theta.imp_ phi).imp_ ((theta.not_.imp_ phi).imp_ phi)) :=
begin
  unfold is_proof,

  apply deduction_theorem,
  apply is_deduct.mp_ (phi.not_.imp_ (theta.not_.imp_ phi).not_),
  {
    apply is_deduct.axiom_,
    apply is_axiom.prop_3_,
  },
  {
    apply deduction_theorem,
    apply is_deduct.mp_ phi.not_,
    {
      apply is_deduct.mp_ theta.not_,
      {
        apply proof_imp_deduct,
        apply T_14_8,
      },
      {
        apply is_deduct.mp_ phi.not_,
        {
          apply is_deduct.mp_ (theta.imp_ phi),
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
  (phi psi : formula)
  (Δ : set formula)
  (h1 : is_deduct Δ (phi.imp_ psi)) :
  is_deduct (Δ ∪ {phi}) psi :=
begin
  apply is_deduct.mp_ phi,
  {
    exact T_14_10 (phi.imp_ psi) Δ h1 {phi},
  },
  {
    apply is_deduct.assume_,
    simp only [set.union_singleton, set.mem_insert_iff, eq_self_iff_true, true_or],
  },
end


theorem T_14_12
  (phi psi : formula)
  (Δ Γ : set formula)
  (h1 : is_deduct Δ phi)
  (h2 : is_deduct Γ (phi.imp_ psi)) :
  is_deduct (Δ ∪ Γ) psi :=
begin
  apply is_deduct.mp_ phi,
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
  (phi psi : formula)
  (Γ : set formula)
  (h1 : is_proof phi)
  (h2 : is_deduct Γ (phi.imp_ psi)) :
  is_deduct Γ psi :=
begin
  apply is_deduct.mp_ phi,
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
  (phi psi : formula)
  (Δ : set formula)
  (h1 : is_deduct Δ phi)
  (h2 : is_proof (phi.imp_ psi)) :
  is_deduct Δ psi :=
begin
  apply is_deduct.mp_ phi,
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
  (psi : formula)
  (Δ Γ : set formula)
  (h1 : is_deduct Γ psi)
  (h2 : ∀ (phi : formula), phi ∈ Γ → is_deduct Δ phi) :
  is_deduct Δ psi :=
begin
  induction h1,
  case is_deduct.axiom_ : h1_P h1_1
  {
    apply is_deduct.axiom_,
    exact h1_1,
  },
  case is_deduct.assume_ : h1_P h1_1
  {
    exact h2 h1_P h1_1,
  },
  case is_deduct.mp_ : h1_P h1_Q h1_1 h1_2 h1_ih_1 h1_ih_2
  {
    exact is_deduct.mp_ h1_P h1_Q h1_ih_1 h1_ih_2,
  },
end


theorem C_14_17
  (psi : formula)
  (Γ : set formula)
  (h1 : is_deduct Γ psi)
  (h2 : ∀ (phi : formula), phi ∈ Γ → is_proof phi) :
  is_proof psi :=
begin
  unfold is_proof at h2,

  unfold is_proof,
  exact T_14_16 psi ∅ Γ h1 h2,
end


theorem eval_not
  (phi : formula)
  (val : prop_valuation) :
  formula.eval_prime val (not_ phi) = bool.tt ↔
    ¬ (formula.eval_prime val phi = bool.tt) :=
begin
  unfold formula.eval_prime,
  cases formula.eval_prime val phi;
  exact dec_trivial,
end


theorem eval_imp
  (phi psi : formula)
  (val : prop_valuation) :
  formula.eval_prime val (imp_ phi psi) = bool.tt ↔
    ((formula.eval_prime val phi = bool.tt) → (formula.eval_prime val psi = bool.tt)) :=
begin
  unfold formula.eval_prime,
  cases formula.eval_prime val phi;
  cases formula.eval_prime val psi;
  exact dec_trivial,
end


theorem is_tauto_prop_true :
  true_.is_tauto_prime :=
begin
  unfold formula.is_tauto_prime,
  intro val,
  unfold formula.eval_prime,
end


theorem is_tauto_prop_1
  (phi psi : formula) :
  (phi.imp_ (psi.imp_ phi)).is_tauto_prime :=
begin
  unfold formula.is_tauto_prime,
  intro val,
  simp only [eval_imp],
  tauto,
end


theorem is_tauto_prop_2
  (phi psi chi : formula) :
  ((phi.imp_ (psi.imp_ chi)).imp_ ((phi.imp_ psi).imp_ (phi.imp_ chi))).is_tauto_prime :=
begin
  unfold formula.is_tauto_prime,
  intro val,
  simp only [eval_imp],
  tauto,
end


theorem is_tauto_prop_3
  (phi psi : formula) :
  (((not_ phi).imp_ (not_ psi)).imp_ (psi.imp_ phi)).is_tauto_prime :=
begin
  unfold formula.is_tauto_prime,
  intro val,
  simp only [eval_not, eval_imp],
  tauto,
end


theorem is_tauto_mp
  (phi psi : formula)
  (h1 : (phi.imp_ psi).is_tauto_prime)
  (h2 : phi.is_tauto_prime) :
  psi.is_tauto_prime :=
begin
  unfold formula.is_tauto_prime at h1,
  unfold formula.is_tauto_prime at h2,

  unfold formula.is_tauto_prime,
  intro val,
  simp only [eval_imp] at h1,
  apply h1,
  exact h2 val,
end


/-
  Proof of the soundness of classical propositional logic.
-/
example
  (phi : formula)
  (h1 : is_prop_proof phi) :
  phi.is_tauto_prime :=
begin
  induction h1,
  case is_prop_deduct.axiom_ : h1_P h1_1
  {
    induction h1_1,
    case is_prop_axiom.prop_true_ :
    {
      exact is_tauto_prop_true,
    },
    case is_prop_axiom.prop_1_ : h1_1_P h1_1_Q
    {
      exact is_tauto_prop_1 h1_1_P h1_1_Q,
    },
    case is_prop_axiom.prop_2_ : h1_1_P h1_1_Q h1_1_R
    {
      exact is_tauto_prop_2 h1_1_P h1_1_Q h1_1_R,
    },
    case is_prop_axiom.prop_3_ : h1_1_P h1_1_Q
    {
      exact is_tauto_prop_3 h1_1_P h1_1_Q,
    },
  },
  case is_prop_deduct.assume_ : h1_P h1_1
  {
    simp only [set.mem_empty_eq] at h1_1,
    contradiction,
  },
  case is_prop_deduct.mp_ : h1_P h1_Q h1_1 h1_2 h1_ih_1 h1_ih_2
  {
    exact is_tauto_mp h1_P h1_Q h1_ih_1 h1_ih_2,
  },
end


lemma mem_prime_set_is_prime
  (phi phi' : formula)
  (h1 : phi' ∈ phi.prime_set) :
  phi'.is_prime :=
begin
  induction phi,
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
  case formula.not_ : phi P_ih
  {
    unfold formula.prime_set at h1,

    exact P_ih h1,
  },
  case formula.imp_ : phi psi P_ih Q_ih
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
  (phi phi' : formula)
  (Δ_U : set formula)
  (val : prop_valuation)
  (Δ_U' : set formula)
  (h1 : coe phi.prime_set ⊆ Δ_U)
  (h2 : Δ_U' = Δ_U.image (eval_prime_ff_to_not val))
  (h3 : phi' = eval_prime_ff_to_not val phi) :
  is_deduct Δ_U' phi' :=
begin
  subst h2,
  subst h3,
  induction phi,
  case formula.true_
  {
    apply is_deduct.axiom_,
    apply is_axiom.prop_true_,
  },
  case formula.pred_ : name args
  {
    let phi := pred_ name args,

    unfold formula.prime_set at h1,
    simp only [finset.coe_singleton, set.singleton_subset_iff] at h1,

    unfold eval_prime_ff_to_not,
    unfold formula.eval_prime,
    apply is_deduct.assume_,
    simp only [finset.coe_image, set.mem_image, finset.mem_coe],
    apply exists.intro phi,
    tauto,
  },
  case formula.not_ : phi P_ih
  {
    unfold formula.prime_set at h1,

    unfold eval_prime_ff_to_not at P_ih,

    unfold eval_prime_ff_to_not,
    unfold formula.eval_prime,

    simp only [bnot_eq_tt_iff_not_eq_tt],
    split_ifs,
    {
      simp only [if_pos h] at P_ih,
      apply is_deduct.mp_ phi,
      {
        apply proof_imp_deduct,
        apply T_14_6,
      },
      {
        exact P_ih h1,
      },
    },
    {
      simp only [if_neg h] at P_ih,
      exact P_ih h1,
    },
  },
  case formula.imp_ : phi psi P_ih Q_ih
  {
    unfold formula.prime_set at h1,
    simp only [finset.coe_union, set.union_subset_iff] at h1,
    cases h1,

    unfold eval_prime_ff_to_not at P_ih,
    unfold eval_prime_ff_to_not at Q_ih,

    unfold eval_prime_ff_to_not,
    unfold formula.eval_prime,
    simp only [bor_eq_true_eq_eq_tt_or_eq_tt],
    simp only [bnot_eq_tt_iff_not_eq_tt],
    split_ifs,
    {
      cases h,
      {
        simp only [if_neg h] at P_ih,
        apply is_deduct.mp_ phi.not_,
        {
          apply proof_imp_deduct,
          apply T_13_6,
        },
        {
          exact P_ih h1_left,
        },
      },
      {
        simp only [if_pos h] at Q_ih,

        apply is_deduct.mp_ psi,
        {
          apply is_deduct.axiom_,
          apply is_axiom.prop_1_,
        },
        {
          exact Q_ih h1_right,
        },
      }
    },
    {
      push_neg at h,
      dsimp at h,
      cases h,
      simp only [if_pos h_left] at P_ih,
      simp only [if_neg h_right] at Q_ih,
      apply is_deduct.mp_ psi.not_,
      {
        apply is_deduct.mp_ phi,
        {
          apply proof_imp_deduct,
          apply T_14_8,
        },
        {
          exact P_ih h1_left,
        }
      },
      {
        exact Q_ih h1_right,
      },
    }
  },
  case formula.forall_ : x phi P_ih
  {
    let phi := forall_ x phi,

    unfold formula.prime_set at h1,
    simp only [finset.coe_singleton, set.singleton_subset_iff] at h1,

    unfold eval_prime_ff_to_not,
    unfold formula.eval_prime,
    apply is_deduct.assume_,
    simp only [finset.coe_image, set.mem_image, finset.mem_coe],
    apply exists.intro phi,
    tauto,
  },
end


lemma T_14_9_deduct
  (phi U : formula)
  (Δ : set formula)
  (h1 : is_deduct (Δ ∪ {U}) phi)
  (h2 : is_deduct (Δ ∪ {U.not_}) phi) :
  is_deduct Δ phi :=
begin
  apply is_deduct.mp_ (U.not_.imp_ phi),
  {
    apply is_deduct.mp_ (U.imp_ phi),
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
  (phi phi' : formula)
  (val : prop_valuation)
  (h1 : phi.is_prime) :
  eval_prime_ff_to_not (function.update_ite val phi' bool.tt) phi =
    function.update_ite (eval_prime_ff_to_not val) phi' phi phi :=
begin
  induction phi,
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
  (phi phi' : formula)
  (val : prop_valuation)
  (h1 : phi.is_prime) :
  eval_prime_ff_to_not (function.update_ite val phi' bool.ff) phi =
    function.update_ite (eval_prime_ff_to_not val) phi' phi.not_ phi :=
begin
  induction phi,
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
  (val : prop_valuation)
  (b : bool)
  (h1_Δ: ∀ (U' : formula), (U' ∈ Δ) → U'.is_prime)
  (h1_U: U.is_prime)
  (h2: U ∉ Δ) :
  Δ.image (eval_prime_ff_to_not (function.update_ite val U b)) =
    Δ.image (eval_prime_ff_to_not val) :=
begin
  apply set.image_congr,
  intros U' a1,
  specialize h1_Δ U' a1,
  cases b,
  {
    simp only [eval_prime_ff_to_not_of_function_update_ite_ff U' U val h1_Δ],
    unfold function.update_ite,
    simp only [ite_eq_right_iff],
    intros a2,
    subst a2,
    contradiction,
  },
  {
    simp only [eval_prime_ff_to_not_of_function_update_ite_tt U' U val h1_Δ],
    unfold function.update_ite,
    simp only [ite_eq_right_iff],
    intros a2,
    subst a2,
    contradiction,
  }
end


lemma prop_complete_aux_aux
  (phi U : formula)
  (Δ : set formula)
  (h1_Δ : ∀ (U' : formula), U' ∈ Δ → U'.is_prime)
  (h1_U : U.is_prime)
  (h2 : U ∉ Δ)
  (h3 : ∀ (val : prop_valuation), is_deduct ((Δ.image (eval_prime_ff_to_not val)) ∪ {eval_prime_ff_to_not val U}) phi) :
  ∀ (val : prop_valuation), is_deduct (Δ.image (eval_prime_ff_to_not val)) phi :=
begin
  intros val,
  apply T_14_9_deduct phi U (Δ.image (eval_prime_ff_to_not val)),
  {
    specialize h3 (function.update_ite val U bool.tt),
    simp only [image_of_eval_prime_ff_to_not_of_function_update_ite U Δ val bool.tt h1_Δ h1_U h2] at h3,
    simp only [eval_prime_ff_to_not_of_function_update_ite_tt U U val h1_U] at h3,
    unfold function.update_ite at h3,
    simp only [eq_self_iff_true, if_true] at h3,
    exact h3,
  },
  {
    specialize h3 (function.update_ite val U bool.ff),
    simp only [image_of_eval_prime_ff_to_not_of_function_update_ite U Δ val bool.ff h1_Δ h1_U h2] at h3,
    simp only [eval_prime_ff_to_not_of_function_update_ite_ff U U val h1_U] at h3,
    unfold function.update_ite at h3,
    simp only [eq_self_iff_true, if_true] at h3,
    exact h3,
  }
end


theorem prop_complete_aux
  (phi : formula)
  (Δ_U : finset formula)
  (h1 : Δ_U ⊆ phi.prime_set)
  (h2 : ∀ (val : prop_valuation), is_deduct (Δ_U.image (eval_prime_ff_to_not val)) phi) :
  is_deduct ∅ phi :=
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
      apply prop_complete_aux_aux phi U Δ_U,
      {
        intros U' a1,
        apply mem_prime_set_is_prime phi U',
        apply h1_right,
        exact a1,
      },
      {
        apply mem_prime_set_is_prime phi U,
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
  (phi : formula)
  (h1 : phi.is_tauto_prime) :
  is_proof phi :=
begin
  unfold is_proof,

  apply prop_complete_aux phi phi.prime_set,
  {
    refl,
  },
  {
    intros val,
    apply L_15_7 phi phi phi.prime_set val (phi.prime_set.image (eval_prime_ff_to_not val)),
    {
      refl,
    },
    {
      simp only [finset.coe_image],
    },
    {
      unfold formula.is_tauto_prime at h1,

      unfold eval_prime_ff_to_not,
      specialize h1 val,
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
