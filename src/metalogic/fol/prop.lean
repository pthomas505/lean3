import .deduct
import .function_update_ite


set_option pp.parens true


open formula


def formula.is_prime : formula → Prop
| (true_) := false
| (pred_ name args) := true
| (eq_ x y) := true
| (not_ P) := false
| (imp_ P Q) := false
| (forall_ x P) := true


def formula.prime_set : formula → finset formula
| (true_) := ∅ 
| (pred_ name args) := {pred_ name args}
| (eq_ x y) := {eq_ x y}
| (not_ P) := P.prime_set
| (imp_ P Q) := P.prime_set ∪ Q.prime_set
| (forall_ x P) := {forall_ x P}


def formula.subst_prime (σ : formula → formula) : formula → formula
| (true_) := true_
| (pred_ name args) := σ (pred_ name args)
| (eq_ x y) := σ (eq_ x y)
| (not_ P) := not_ P.subst_prime
| (imp_ P Q) := imp_ P.subst_prime Q.subst_prime
| (forall_ x P) := σ (forall_ x P)


@[derive inhabited]
def valuation : Type := formula → bool

def formula.eval_prime (val : valuation) : formula → bool
| (true_) := bool.tt
| (pred_ name args) := val (pred_ name args)
| (eq_ x y) := val (eq_ x y)
| (not_ P) := ! P.eval_prime
| (imp_ P Q) := (! P.eval_prime) || Q.eval_prime
| (forall_ x P) := val (forall_ x P)

def formula.is_tauto_prime (P : formula) : Prop :=
  ∀ (val : valuation), P.eval_prime val = bool.tt

def eval_prime_ff_to_not (val : valuation) (P : formula) : formula :=
if formula.eval_prime val P = bool.tt then P else P.not_


lemma eval_prime_prime
  (P : formula)
  (val : valuation)
  (h1 : P.is_prime) :
  P.eval_prime val = val P :=
begin
  induction P,
  case [formula.true_, formula.not_, formula.imp_]
  {
    all_goals
    {
      unfold formula.is_prime at h1,

      contradiction,
    }
  },
  case [formula.pred_, formula.eq_, formula.forall_]
  {
    all_goals
    {
      refl,
    }
  },
end


example
  (P : formula)
  (val val' : valuation)
  (h1 : ∀ (Q : formula), Q ∈ P.prime_set → val Q = val' Q) :
  P.eval_prime val = P.eval_prime val' :=
begin
  induction P,
  case formula.true_
  {
    unfold formula.eval_prime,
  },
  case [formula.pred_, formula.eq_, formula.forall_]
  {
    all_goals
    {
      unfold formula.prime_set at h1,

      unfold formula.eval_prime,
      apply h1,
      simp only [finset.mem_singleton, eq_self_iff_true, and_self],
    },
  },
  case formula.not_ : P P_ih
  {
    unfold formula.prime_set at h1,

    unfold formula.eval_prime,
    congr' 1,
    exact P_ih h1,
  },
  case formula.imp_ : P Q P_ih Q_ih
  {
    unfold formula.prime_set at h1,
    simp only [finset.mem_union] at h1,

    unfold formula.eval_prime,
    congr' 1,
    {
      congr' 1,
      apply P_ih,
      intros Q' a1,
      apply h1,
      left,
      exact a1,
    },
    {
      apply Q_ih,
      intros Q' a1,
      apply h1,
      right,
      exact a1,
    }
  },
end


lemma eval_prime_subst_prime_eq_eval_prime_eval_prime
  (P : formula)
  (σ : formula → formula)
  (val : valuation) :
  (P.subst_prime σ).eval_prime val =
    P.eval_prime (fun (Q : formula), (σ Q).eval_prime val) :=
begin
  induction P,
  case [formula.true_, formula.pred_, formula.eq_, formula.forall_]
  {
    all_goals
    {
      refl,
    }
  },
  case formula.not_ : P P_ih
  {
    unfold formula.subst_prime,
    unfold formula.eval_prime,
    congr,
    exact P_ih,
  },
  case formula.imp_ : P Q P_ih Q_ih
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
  (P : formula)
  (h1 : P.is_tauto_prime)
  (σ : formula → formula) :
  (formula.subst_prime σ P).is_tauto_prime :=
begin
  unfold formula.is_tauto_prime at h1,

  unfold formula.is_tauto_prime,
  intros val,
  simp only [eval_prime_subst_prime_eq_eval_prime_eval_prime P σ val],
  apply h1,
end


example
  (P Q R S : formula)
  (val : valuation)
  (σ : formula → formula)
  (h1 : P.eval_prime val = Q.eval_prime val) :
  (S.subst_prime (function.update_ite σ R P)).eval_prime val =
    (S.subst_prime (function.update_ite σ R Q)).eval_prime val :=
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


theorem T_14_10
  (Q : formula)
  (Δ : set formula)
  (h1 : is_deduct Δ Q) :
  ∀ (Γ : set formula), is_deduct (Δ ∪ Γ) Q :=
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
  case is_deduct.axiom_ : h1_P h1_1
  {
    apply is_deduct.mp_ h1_P,
    {
      apply is_deduct.axiom_,
      exact is_axiom.prop_1_ h1_P P,
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
        exact is_axiom.prop_1_ h1_P P,
      },
      {
        apply is_deduct.assume_,
        exact h1_1,
      },
    }
  },
  case is_deduct.mp_ : h1_P h1_Q h1_1 h1_2 h1_ih_1 h1_ih_2
  {
    apply is_deduct.mp_ (P.imp_ h1_P),
    {
      apply is_deduct.mp_ (P.imp_ (h1_P.imp_ h1_Q)),
      {
        apply is_deduct.axiom_,
        exact is_axiom.prop_2_ P h1_P h1_Q,
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
  (Q : formula)
  (Δ Γ : set formula)
  (h1 : is_deduct Γ Q)
  (h2 : ∀ (P : formula), P ∈ Γ → is_deduct Δ P) :
  is_deduct Δ Q :=
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
  (val : valuation) :
  formula.eval_prime val (not_ P) = bool.tt ↔
    ¬ (formula.eval_prime val P = bool.tt) :=
begin
  unfold formula.eval_prime,
  cases formula.eval_prime val P;
  exact dec_trivial,
end


theorem eval_imp
  (P Q : formula)
  (val : valuation) :
  formula.eval_prime val (imp_ P Q) = bool.tt ↔
    ((formula.eval_prime val P = bool.tt) → (formula.eval_prime val Q = bool.tt)) :=
begin
  unfold formula.eval_prime,
  cases formula.eval_prime val P;
  cases formula.eval_prime val Q;
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
  (P Q : formula) :
  (P.imp_ (Q.imp_ P)).is_tauto_prime :=
begin
  unfold formula.is_tauto_prime,
  intro val,
  simp only [eval_imp],
  tauto,
end


theorem is_tauto_prop_2
  (P Q R : formula) :
  ((P.imp_ (Q.imp_ R)).imp_ ((P.imp_ Q).imp_ (P.imp_ R))).is_tauto_prime :=
begin
  unfold formula.is_tauto_prime,
  intro val,
  simp only [eval_imp],
  tauto,
end


theorem is_tauto_prop_3
  (P Q : formula) :
  (((not_ P).imp_ (not_ Q)).imp_ (Q.imp_ P)).is_tauto_prime :=
begin
  unfold formula.is_tauto_prime,
  intro val,
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
  intro val,
  simp only [eval_imp] at h1,
  apply h1,
  exact h2 val,
end


example
  (P : formula)
  (h1 : is_prop_proof P) :
  P.is_tauto_prime :=
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
  (P P' : formula)
  (h1 : P' ∈ P.prime_set) :
  P'.is_prime :=
begin
  induction P,
  case formula.true_
  {
    unfold formula.prime_set at h1,
    simp only [finset.not_mem_empty] at h1,

    contradiction,
  },
  case [formula.pred_, formula.eq_, formula.forall_]
  {
    all_goals
    {
      unfold formula.prime_set at h1,
      simp only [finset.mem_singleton] at h1,

      subst h1,
      unfold formula.is_prime,
    }
  },
  case formula.not_ : P P_ih
  {
    unfold formula.prime_set at h1,

    exact P_ih h1,
  },
  case formula.imp_ : P Q P_ih Q_ih
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
  (P P' : formula)
  (Δ_U : set formula)
  (val : valuation)
  (Δ_U' : set formula)
  (h1 : coe P.prime_set ⊆ Δ_U)
  (h2 : Δ_U' = Δ_U.image (eval_prime_ff_to_not val))
  (h3 : P' = eval_prime_ff_to_not val P) :
  is_deduct Δ_U' P' :=
begin
  subst h2,
  subst h3,
  induction P,
  case formula.true_
  {
    apply is_deduct.axiom_,
    apply is_axiom.prop_true_,
  },
  case formula.pred_ : name args
  {
    let P := pred_ name args,

    unfold formula.prime_set at h1,
    simp only [finset.coe_singleton, set.singleton_subset_iff] at h1,

    unfold eval_prime_ff_to_not,
    unfold formula.eval_prime,
    apply is_deduct.assume_,
    simp only [finset.coe_image, set.mem_image, finset.mem_coe],
    apply exists.intro P,
    tauto,
  },
  case formula.eq_ : x y
  {
    let P := eq_ x y,

    unfold formula.prime_set at h1,
    simp only [finset.coe_singleton, set.singleton_subset_iff] at h1,

    unfold eval_prime_ff_to_not,
    unfold formula.eval_prime,
    apply is_deduct.assume_,
    simp only [finset.coe_image, set.mem_image, finset.mem_coe],
    apply exists.intro P,
    tauto,
  },
  case formula.not_ : P P_ih
  {
    unfold formula.prime_set at h1,

    unfold eval_prime_ff_to_not at P_ih,

    unfold eval_prime_ff_to_not,
    unfold formula.eval_prime,

    simp only [bnot_eq_tt_iff_not_eq_tt],
    split_ifs,
    {
      simp only [if_pos h] at P_ih,
      apply is_deduct.mp_ P,
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
  case formula.imp_ : P Q P_ih Q_ih
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
        apply is_deduct.mp_ P.not_,
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

        apply is_deduct.mp_ Q,
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
      apply is_deduct.mp_ Q.not_,
      {
        apply is_deduct.mp_ P,
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
  case formula.forall_ : x P P_ih
  {
    let P := forall_ x P,

    unfold formula.prime_set at h1,
    simp only [finset.coe_singleton, set.singleton_subset_iff] at h1,

    unfold eval_prime_ff_to_not,
    unfold formula.eval_prime,
    apply is_deduct.assume_,
    simp only [finset.coe_image, set.mem_image, finset.mem_coe],
    apply exists.intro P,
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
  (P P' : formula)
  (val : valuation)
  (h1 : P.is_prime) :
  eval_prime_ff_to_not (function.update_ite val P' bool.tt) P =
    function.update_ite (eval_prime_ff_to_not val) P' P P :=
begin
  induction P,
  case formula.true_
  {
    unfold function.update_ite,
    unfold eval_prime_ff_to_not,
    tauto,
  },
  case [formula.pred_, formula.eq_, formula.forall_]
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
  (P P' : formula)
  (val : valuation)
  (h1 : P.is_prime) :
  eval_prime_ff_to_not (function.update_ite val P' bool.ff) P =
    function.update_ite (eval_prime_ff_to_not val) P' P.not_ P :=
begin
  induction P,
  case formula.true_
  {
    unfold function.update_ite,
    unfold eval_prime_ff_to_not,
    tauto,
  },
  case [formula.pred_, formula.eq_, formula.forall_]
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
  (val : valuation)
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
  (P U : formula)
  (Δ : set formula)
  (h1_Δ : ∀ (U' : formula), U' ∈ Δ → U'.is_prime)
  (h1_U : U.is_prime)
  (h2 : U ∉ Δ)
  (h3 : ∀ (val : valuation), is_deduct ((Δ.image (eval_prime_ff_to_not val)) ∪ {eval_prime_ff_to_not val U}) P) :
  ∀ (val : valuation), is_deduct (Δ.image (eval_prime_ff_to_not val)) P :=
begin
  intros val,
  apply T_14_9_deduct P U (Δ.image (eval_prime_ff_to_not val)),
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
  (P : formula)
  (Δ_U : finset formula)
  (h1 : Δ_U ⊆ P.prime_set)
  (h2 : ∀ (val : valuation), is_deduct (Δ_U.image (eval_prime_ff_to_not val)) P) :
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
    intros val,
    apply L_15_7 P P P.prime_set val (P.prime_set.image (eval_prime_ff_to_not val)),
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


#lint
