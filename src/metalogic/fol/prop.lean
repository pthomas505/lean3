import .deduct
import .function_update_ite


set_option pp.parens true


open formula


def formula.is_atomic : formula → Prop
| (true_) := false
| (pred_ name args) := true
| (eq_ x y) := true
| (not_ P) := false
| (imp_ P Q) := false
| (forall_ x P) := true


def formula.atomic_set : formula → finset formula
| (true_) := ∅ 
| (pred_ name args) := {pred_ name args}
| (eq_ x y) := {eq_ x y}
| (not_ P) := P.atomic_set
| (imp_ P Q) := P.atomic_set ∪ Q.atomic_set
| (forall_ x P) := {forall_ x P}


def formula.subst_atomic (σ : formula → formula) : formula → formula
| (true_) := true_
| (pred_ name args) := σ (pred_ name args)
| (eq_ x y) := σ (eq_ x y)
| (not_ P) := not_ P.subst_atomic
| (imp_ P Q) := imp_ P.subst_atomic Q.subst_atomic
| (forall_ x P) := σ (forall_ x P)


@[derive inhabited]
def valuation : Type := formula → bool

def formula.eval_atomic (val : valuation) : formula → bool
| (true_) := bool.tt
| (pred_ name args) := val (pred_ name args)
| (eq_ x y) := val (eq_ x y)
| (not_ P) := ! P.eval_atomic
| (imp_ P Q) := (! P.eval_atomic) || Q.eval_atomic
| (forall_ x P) := val (forall_ x P)

def formula.is_tauto_atomic (P : formula) : Prop :=
  ∀ (val : valuation), P.eval_atomic val = bool.tt

def eval_atomic_ff_to_not (val : valuation) (P : formula) : formula :=
if formula.eval_atomic val P = bool.tt then P else P.not_


lemma eval_atomic_atomic
  (P : formula)
  (val : valuation)
  (h1 : P.is_atomic) :
  P.eval_atomic val = val P :=
begin
  induction P,
  case [formula.true_, formula.not_, formula.imp_]
  {
    all_goals
    {
      unfold formula.is_atomic at h1,

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
  (h1 : ∀ (Q : formula), Q ∈ P.atomic_set → val Q = val' Q) :
  P.eval_atomic val = P.eval_atomic val' :=
begin
  induction P,
  case formula.true_
  {
    unfold formula.eval_atomic,
  },
  case [formula.pred_, formula.eq_, formula.forall_]
  {
    all_goals
    {
      unfold formula.atomic_set at h1,

      unfold formula.eval_atomic,
      apply h1,
      simp only [finset.mem_singleton, eq_self_iff_true, and_self],
    },
  },
  case formula.not_ : P P_ih
  {
    unfold formula.atomic_set at h1,

    unfold formula.eval_atomic,
    congr' 1,
    exact P_ih h1,
  },
  case formula.imp_ : P Q P_ih Q_ih
  {
    unfold formula.atomic_set at h1,
    simp only [finset.mem_union] at h1,

    unfold formula.eval_atomic,
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


lemma eval_atomic_subst_atomic_eq_eval_atomic_eval_atomic
  (P : formula)
  (σ : formula → formula)
  (val : valuation) :
  (P.subst_atomic σ).eval_atomic val =
    P.eval_atomic (fun (Q : formula), (σ Q).eval_atomic val) :=
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
    unfold formula.subst_atomic,
    unfold formula.eval_atomic,
    congr,
    exact P_ih,
  },
  case formula.imp_ : P Q P_ih Q_ih
  {
    unfold formula.subst_atomic,
    unfold formula.eval_atomic,
    congr,
    {
      exact P_ih,
    },
    {
      exact Q_ih,
    }
  },
end


theorem is_tauto_atomic_imp_is_tauto_atomic_subst_atomic
  (P : formula)
  (h1 : P.is_tauto_atomic)
  (σ : formula → formula) :
  (formula.subst_atomic σ P).is_tauto_atomic :=
begin
  unfold formula.is_tauto_atomic at h1,

  unfold formula.is_tauto_atomic,
  intros val,
  simp only [eval_atomic_subst_atomic_eq_eval_atomic_eval_atomic P σ val],
  apply h1,
end


example
  (P Q R S : formula)
  (val : valuation)
  (σ : formula → formula)
  (h1 : P.eval_atomic val = Q.eval_atomic val) :
  (S.subst_atomic (function.update_ite σ R P)).eval_atomic val =
    (S.subst_atomic (function.update_ite σ R Q)).eval_atomic val :=
begin
  simp only [eval_atomic_subst_atomic_eq_eval_atomic_eval_atomic],
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

  apply is_deduct.mp_,
  {
    apply is_deduct.mp_,
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


theorem T_13_6
  (P Q : formula) :
  is_proof (P.not_.imp_ (P.imp_ Q)) :=
begin
  unfold is_proof,

  apply is_deduct.mp_,
  {
    apply is_deduct.mp_,
    {
      apply is_deduct.axiom_,
      exact is_axiom.prop_2_ P.not_ (Q.not_.imp_ P.not_) (P.imp_ Q),
    },
    {
      apply is_deduct.mp_,
      {
        apply is_deduct.axiom_,
        exact is_axiom.prop_1_ ((Q.not_.imp_ P.not_).imp_ (P.imp_ Q)) P.not_,
      },
      {
        apply is_deduct.axiom_,
        exact is_axiom.prop_3_ Q P,
      }
    }
  },
  {
    apply is_deduct.axiom_,
    exact is_axiom.prop_1_ P.not_ Q.not_,
  },
end


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
    apply is_deduct.mp_,
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
      apply is_deduct.mp_,
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
    apply is_deduct.mp_,
    {
      apply is_deduct.mp_,
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


example
  (P Q : formula) :
  is_proof (P.not_.imp_ (P.imp_ Q)) :=
begin
  unfold is_proof,

  apply deduction_theorem,
  apply is_deduct.mp_,
  {
    apply is_deduct.axiom_,
    exact is_axiom.prop_3_ Q P,
  },
  {
    apply is_deduct.mp_,
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
  apply is_deduct.mp_,
  {
    apply is_deduct.axiom_,
    apply is_axiom.prop_3_,
  },
  {
    apply deduction_theorem,
    apply is_deduct.mp_,
    {
      apply proof_imp_deduct,
      apply T_14_6,
    },
    {
      apply is_deduct.mp_,
      {
        apply is_deduct.assume_,
        simp only [set.union_singleton, insert_emptyc_eq, set.mem_insert_iff, set.mem_singleton_iff, eq_self_iff_true, and_true,
  false_or],
      },
      {
        apply is_deduct.mp_,
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
  apply is_deduct.mp_,
  {
    apply proof_imp_deduct,
    apply T_14_7,
  },
  {
    apply deduction_theorem,
    apply is_deduct.mp_ Q R,
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
  apply is_deduct.mp_,
  {
    apply is_deduct.axiom_,
    apply is_axiom.prop_3_,
  },
  {
    apply deduction_theorem,
    apply is_deduct.mp_,
    {
      apply is_deduct.mp_,
      {
        apply proof_imp_deduct,
        apply T_14_8,
      },
      {
        apply is_deduct.mp_,
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
    apply or.intro_left,
    exact h1_1,
  },
  case is_deduct.mp_ : h1_P h1_Q h1_1 h1_2 h1_ih_1 h1_ih_2
  {
    apply is_deduct.mp_ h1_P h1_Q,
    {
      exact h1_ih_1,
    },
    {
      exact h1_ih_2,
    }
  },
end


theorem deduction_theorem_converse
  (P Q : formula)
  (Δ : set formula)
  (h1 : is_deduct Δ (P.imp_ Q)) :
  is_deduct (Δ ∪ {P}) Q :=
begin
  have s1 : is_deduct (Δ ∪ {P}) (P.imp_ Q),
  exact T_14_10 (P.imp_ Q) Δ h1 {P},

  have s2 : is_deduct (Δ ∪ {P}) P,
  apply is_deduct.assume_,
  simp only [set.union_singleton, set.mem_insert_iff, eq_self_iff_true, true_or],

  exact is_deduct.mp_ P Q s1 s2,
end


theorem C_14_11
  (Q : formula)
  (h1 : is_proof Q) :
  ∀ (Γ : set formula), is_deduct Γ Q :=
begin
  unfold is_proof at h1,

  intros Γ,
  rewrite <- set.union_empty Γ,
  rewrite set.union_comm,
  exact T_14_10 Q ∅ h1 Γ,
end


example :
  C_14_11 = proof_imp_deduct :=
begin
  refl,
end


theorem T_14_12
  (P Q : formula)
  (Δ Γ : set formula)
  (h1 : is_deduct Δ P)
  (h2 : is_deduct Γ (P.imp_ Q)) :
  is_deduct (Δ ∪ Γ) Q :=
begin
  have s1 : is_deduct (Δ ∪ Γ) P,
  apply T_14_10,
  exact h1,

  have s2 : is_deduct (Δ ∪ Γ) (P.imp_ Q),
  rewrite set.union_comm,
  apply T_14_10,
  exact h2,

  exact is_deduct.mp_ P Q s2 s1,
end


theorem C_14_13
  (P Q : formula)
  (Δ : set formula)
  (h1 : is_deduct Δ P)
  (h2 : is_deduct Δ (P.imp_ Q)) :
  is_deduct Δ Q :=
begin
  have s1 : is_deduct (Δ ∪ Δ) Q, 
  exact T_14_12 P Q Δ Δ h1 h2,

  simp only [set.union_self] at s1,
  exact s1,
end


theorem C_14_13'
  (P Q : formula)
  (Δ : set formula)
  (h1 : is_deduct Δ P)
  (h2 : is_deduct Δ (P.imp_ Q)) :
  is_deduct Δ Q :=
begin
  exact is_deduct.mp_ P Q h2 h1,
end


theorem C_14_14
  (P Q : formula)
  (Γ : set formula)
  (h1 : is_proof P)
  (h2 : is_deduct Γ (P.imp_ Q)) :
  is_deduct Γ Q :=
begin
  have s1 : is_deduct Γ P,
  exact C_14_11 P h1 Γ,

  exact is_deduct.mp_ P Q h2 s1,
end

alias C_14_14 <- mp_proof_deduct


theorem C_14_15
  (P Q : formula)
  (Δ : set formula)
  (h1 : is_deduct Δ P)
  (h2 : is_proof (P.imp_ Q)) :
  is_deduct Δ Q :=
begin
  have s1 : is_deduct Δ (P.imp_ Q),
  exact C_14_11 (P.imp_ Q) h2 Δ,

  exact is_deduct.mp_ P Q s1 h1,
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
  formula.eval_atomic val (not_ P) = bool.tt ↔
    ¬ (formula.eval_atomic val P = bool.tt) :=
begin
  unfold formula.eval_atomic,
  cases formula.eval_atomic val P;
  exact dec_trivial,
end


theorem eval_imp
  (P Q : formula)
  (val : valuation) :
  formula.eval_atomic val (imp_ P Q) = bool.tt ↔
    ((formula.eval_atomic val P = bool.tt) → (formula.eval_atomic val Q = bool.tt)) :=
begin
  unfold formula.eval_atomic,
  cases formula.eval_atomic val P;
  cases formula.eval_atomic val Q;
  exact dec_trivial,
end


theorem is_tauto_prop_true :
  true_.is_tauto_atomic :=
begin
  unfold formula.is_tauto_atomic,
  intro val,
  unfold formula.eval_atomic,
end


theorem is_tauto_prop_1
  (P Q : formula) :
  (P.imp_ (Q.imp_ P)).is_tauto_atomic :=
begin
  unfold formula.is_tauto_atomic,
  intro val,
  simp only [eval_imp],
  tauto,
end


theorem is_tauto_prop_2
  (P Q R : formula) :
  ((P.imp_ (Q.imp_ R)).imp_ ((P.imp_ Q).imp_ (P.imp_ R))).is_tauto_atomic :=
begin
  unfold formula.is_tauto_atomic,
  intro val,
  simp only [eval_imp],
  tauto,
end


theorem is_tauto_prop_3
  (P Q : formula) :
  (((not_ P).imp_ (not_ Q)).imp_ (Q.imp_ P)).is_tauto_atomic :=
begin
  unfold formula.is_tauto_atomic,
  intro val,
  simp only [eval_not, eval_imp],
  tauto,
end


theorem is_tauto_mp
  (P Q : formula)
  (h1 : (P.imp_ Q).is_tauto_atomic)
  (h2 : P.is_tauto_atomic) :
  Q.is_tauto_atomic :=
begin
  unfold formula.is_tauto_atomic at h1,
  unfold formula.is_tauto_atomic at h2,

  unfold formula.is_tauto_atomic,
  intro val,
  simp only [eval_imp] at h1,
  apply h1,
  exact h2 val,
end


example
  (P : formula)
  (h1 : is_prop_proof P) :
  P.is_tauto_atomic :=
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


lemma mem_atomic_set_is_atomic
  (P P' : formula)
  (h1 : P' ∈ P.atomic_set) :
  P'.is_atomic :=
begin
  induction P,
  case formula.true_
  {
    unfold formula.atomic_set at h1,
    simp only [finset.not_mem_empty] at h1,

    contradiction,
  },
  case [formula.pred_, formula.eq_, formula.forall_]
  {
    all_goals
    {
      unfold formula.atomic_set at h1,
      simp only [finset.mem_singleton] at h1,

      subst h1,
      unfold formula.is_atomic,
    }
  },
  case formula.not_ : P P_ih
  {
    unfold formula.atomic_set at h1,

    exact P_ih h1,
  },
  case formula.imp_ : P Q P_ih Q_ih
  {
    unfold formula.atomic_set at h1,
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
  (h1 : coe P.atomic_set ⊆ Δ_U)
  (h2 : Δ_U' = Δ_U.image (eval_atomic_ff_to_not val))
  (h3 : P' = eval_atomic_ff_to_not val P) :
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

    unfold formula.atomic_set at h1,
    simp only [finset.coe_singleton, set.singleton_subset_iff] at h1,

    unfold eval_atomic_ff_to_not,
    unfold formula.eval_atomic,
    apply is_deduct.assume_,
    simp only [finset.coe_image, set.mem_image, finset.mem_coe],
    apply exists.intro P,
    tauto,
  },
  case formula.eq_ : x y
  {
    let P := eq_ x y,

    unfold formula.atomic_set at h1,
    simp only [finset.coe_singleton, set.singleton_subset_iff] at h1,

    unfold eval_atomic_ff_to_not,
    unfold formula.eval_atomic,
    apply is_deduct.assume_,
    simp only [finset.coe_image, set.mem_image, finset.mem_coe],
    apply exists.intro P,
    tauto,
  },
  case formula.not_ : P P_ih
  {
    unfold formula.atomic_set at h1,

    unfold eval_atomic_ff_to_not at P_ih,

    unfold eval_atomic_ff_to_not,
    unfold formula.eval_atomic,

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
    unfold formula.atomic_set at h1,
    simp only [finset.coe_union, set.union_subset_iff] at h1,
    cases h1,

    unfold eval_atomic_ff_to_not at P_ih,
    unfold eval_atomic_ff_to_not at Q_ih,

    unfold eval_atomic_ff_to_not,
    unfold formula.eval_atomic,
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

    unfold formula.atomic_set at h1,
    simp only [finset.coe_singleton, set.singleton_subset_iff] at h1,

    unfold eval_atomic_ff_to_not,
    unfold formula.eval_atomic,
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


lemma eval_atomic_ff_to_not_of_function_update_ite_tt
  (P P' : formula)
  (val : valuation)
  (h1 : P.is_atomic) :
  eval_atomic_ff_to_not (function.update_ite val P' bool.tt) P =
    function.update_ite (eval_atomic_ff_to_not val) P' P P :=
begin
  induction P,
  case formula.true_
  {
    unfold function.update_ite,
    unfold eval_atomic_ff_to_not,
    tauto,
  },
  case [formula.pred_, formula.eq_, formula.forall_]
  {
    all_goals
    {
      unfold function.update_ite,
      unfold eval_atomic_ff_to_not,
      unfold formula.eval_atomic,
      unfold function.update_ite,
      split_ifs; tauto,
    }
  },
  case [formula.not_, formula.imp_]
  {
    all_goals
    {
      unfold formula.is_atomic at h1,

      contradiction,
    }
  },
end


lemma eval_atomic_ff_to_not_of_function_update_ite_ff
  (P P' : formula)
  (val : valuation)
  (h1 : P.is_atomic) :
  eval_atomic_ff_to_not (function.update_ite val P' bool.ff) P =
    function.update_ite (eval_atomic_ff_to_not val) P' P.not_ P :=
begin
  induction P,
  case formula.true_
  {
    unfold function.update_ite,
    unfold eval_atomic_ff_to_not,
    tauto,
  },
  case [formula.pred_, formula.eq_, formula.forall_]
  {
    all_goals
    {
      unfold function.update_ite,
      unfold eval_atomic_ff_to_not,
      unfold formula.eval_atomic,
      unfold function.update_ite,
      split_ifs; tauto,
    }
  },
  case [formula.not_, formula.imp_]
  {
    all_goals
    {
      unfold formula.is_atomic at h1,

      contradiction,
    }
  },
end


lemma image_of_eval_atomic_ff_to_not_of_function_update_ite
  (U : formula)
  (Δ : set formula)
  (val : valuation)
  (b : bool)
  (h1_Δ: ∀ (U' : formula), (U' ∈ Δ) → U'.is_atomic)
  (h1_U: U.is_atomic)
  (h2: U ∉ Δ) :
  Δ.image (eval_atomic_ff_to_not (function.update_ite val U b)) =
    Δ.image (eval_atomic_ff_to_not val) :=
begin
  apply set.image_congr,
  intros U' a1,
  specialize h1_Δ U' a1,
  cases b,
  {
    simp only [eval_atomic_ff_to_not_of_function_update_ite_ff U' U val h1_Δ],
    unfold function.update_ite,
    simp only [ite_eq_right_iff],
    intros a2,
    subst a2,
    contradiction,
  },
  {
    simp only [eval_atomic_ff_to_not_of_function_update_ite_tt U' U val h1_Δ],
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
  (h1_Δ : ∀ (U' : formula), U' ∈ Δ → U'.is_atomic)
  (h1_U : U.is_atomic)
  (h2 : U ∉ Δ)
  (h3 : ∀ (val : valuation), is_deduct ((Δ.image (eval_atomic_ff_to_not val)) ∪ {eval_atomic_ff_to_not val U}) P) :
  ∀ (val : valuation), is_deduct (Δ.image (eval_atomic_ff_to_not val)) P :=
begin
  intros val,
  apply T_14_9_deduct P U (Δ.image (eval_atomic_ff_to_not val)),
  {
    specialize h3 (function.update_ite val U bool.tt),
    simp only [image_of_eval_atomic_ff_to_not_of_function_update_ite U Δ val bool.tt h1_Δ h1_U h2] at h3,
    simp only [eval_atomic_ff_to_not_of_function_update_ite_tt U U val h1_U] at h3,
    unfold function.update_ite at h3,
    simp only [eq_self_iff_true, if_true] at h3,
    exact h3,
  },
  {
    specialize h3 (function.update_ite val U bool.ff),
    simp only [image_of_eval_atomic_ff_to_not_of_function_update_ite U Δ val bool.ff h1_Δ h1_U h2] at h3,
    simp only [eval_atomic_ff_to_not_of_function_update_ite_ff U U val h1_U] at h3,
    unfold function.update_ite at h3,
    simp only [eq_self_iff_true, if_true] at h3,
    exact h3,
  }
end


theorem prop_complete_aux
  (P : formula)
  (Δ_U : finset formula)
  (h1 : P.is_tauto_atomic)
  (h2 : Δ_U ⊆ P.atomic_set)
  (h3 : ∀ (val : valuation), is_deduct (Δ_U.image (eval_atomic_ff_to_not val)) P) :
  is_deduct ∅ P :=
begin
  induction Δ_U using finset.induction_on,
  case h₁
  {
    simp only [finset.image_empty, finset.coe_empty, forall_const] at h3,

    exact h3,
  },
  case h₂ : U Δ_U Δ_U_1 Δ_U_2
  {
    apply Δ_U_2,
    {
      simp only [finset.insert_subset] at h2,
      cases h2,

      exact h2_right,
    },
    {
      simp only [finset.insert_subset] at h2,
      cases h2,

      simp only [finset.image_insert, finset.coe_insert, finset.coe_image] at h3,

      simp only [finset.coe_image],
      apply prop_complete_aux_aux P U Δ_U,
      {
        intros U' a1,
        apply mem_atomic_set_is_atomic P U',
        apply h2_right,
        exact a1,
      },
      {
        apply mem_atomic_set_is_atomic P U,
        exact h2_left,
      },
      {
        exact Δ_U_1,
      },
      {
        simp only [set.union_singleton],
        exact h3,
      }
    }
  },
end


theorem prop_complete
  (P : formula)
  (h1 : P.is_tauto_atomic) :
  is_proof P :=
begin
  unfold is_proof,

  apply prop_complete_aux P P.atomic_set h1,
  {
    refl,
  },
  {
    intros val,
    apply L_15_7 P P P.atomic_set val (P.atomic_set.image (eval_atomic_ff_to_not val)),
    {
      refl,
    },
    {
      simp only [finset.coe_image],
    },
    {
      unfold formula.is_tauto_atomic at h1,

      unfold eval_atomic_ff_to_not,
      specialize h1 val,
      simp only [if_pos h1],
    }
  }
end