import metalogic.fol.common.semantics


set_option pp.parens true


namespace fol

open formula


-- proposition substitution

/--
  The recursive simultaneous uniform substitution of all of the propositional variables in a formula.
-/
def replace_prop_fun
  (τ : pred_name → pred_name) : formula → formula
| true_ := true_
| (pred_ P ts) := ite (ts = list.nil) (pred_ (τ P) list.nil) (pred_ P ts)
| (not_ phi) := not_ (replace_prop_fun phi)
| (imp_ phi psi) := imp_ (replace_prop_fun phi) (replace_prop_fun psi)
| (forall_ x phi) := forall_ x (replace_prop_fun phi)


lemma prop_sub_aux
  (D : Type)
  (I : interpretation D)
  (V : valuation D)
  (τ : pred_name → pred_name)
  (F : formula) :
  holds D I V (replace_prop_fun τ F) ↔
    holds D
    ⟨
      I.nonempty,
      fun (P : pred_name) (xs : list D),
        if (xs = list.nil) = tt
        then holds D I V (pred_ (τ P) list.nil)
        else I.pred P xs
    ⟩
    V F :=
begin
  induction F generalizing V,
  case formula.true_ : V
  {
    unfold replace_prop_fun,
    unfold holds,
  },
  case formula.pred_ : X xs V
  {
    unfold replace_prop_fun,
    split_ifs,
    {
      unfold holds,
      simp only [list.map_nil, list.map_eq_nil],
      simp only [coe_sort_tt, eq_iff_iff, iff_true],
      simp only [if_pos h],
    },
    {
      unfold holds,
      simp only [list.map_eq_nil, list.map_nil],
      simp only [coe_sort_tt, eq_iff_iff, iff_true],
      simp only [if_neg h],
    }
  },
  case formula.not_ : phi phi_ih V
  {
    unfold replace_prop_fun,
    unfold holds,
    apply not_congr,
    apply phi_ih,
  },
  case formula.imp_ : phi psi phi_ih psi_ih V
  {
    unfold replace_prop_fun,
    unfold holds,
    apply imp_congr,
    {
      apply phi_ih,
    },
    {
      apply psi_ih,
    }
  },
  case formula.forall_ : x phi phi_ih V
  {
    unfold replace_prop_fun,
    unfold holds,
    apply forall_congr,
    intros d,
    apply phi_ih,
  },
end


theorem prop_sub_is_valid
  (phi : formula)
  (h1 : phi.is_valid)
  (τ : pred_name → pred_name) :
  (replace_prop_fun τ phi).is_valid :=
begin
  unfold formula.is_valid at h1,

  unfold formula.is_valid,
  intros D I V,
  simp only [prop_sub_aux D I V τ phi],
  apply h1,
end


#lint

end fol
