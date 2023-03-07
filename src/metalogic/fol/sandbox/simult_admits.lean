import .simult_replace_free
import .admits

import .misc_list

import data.finset


set_option pp.parens true


open formula



def simult_admits_aux (σ : variable_ → variable_) : finset variable_ → formula → Prop
| _ true_ := true
| binders (pred_ name args) :=
    ∀ (v : variable_), (v ∈ args ∧ v ∉ binders) → σ v ∉ binders
| binders (eq_ x y) :=
    (x ∉ binders → σ x ∉ binders) ∧ (y ∉ binders → σ y ∉ binders)
| binders (not_ P) := simult_admits_aux binders P
| binders (imp_ P Q) := simult_admits_aux binders P ∧ simult_admits_aux binders Q
| binders (forall_ x P) := simult_admits_aux (binders ∪ {x}) P

def simult_admits (σ : variable_ → variable_) (P : formula) : Prop :=
  simult_admits_aux σ ∅ P



def simult_to_is_bound_aux : (variable_ → bool) → formula → bool_formula
| _ true_ := bool_formula.true_
| σ (pred_ name args) := bool_formula.pred_ name (args.map σ)
| σ (eq_ x y) := bool_formula.eq_ (σ x) (σ y)
| σ (not_ P) := bool_formula.not_ (simult_to_is_bound_aux σ P)
| σ (imp_ P Q) := bool_formula.imp_ (simult_to_is_bound_aux σ P) (simult_to_is_bound_aux σ Q)
| σ (forall_ x P) := bool_formula.forall_ true (simult_to_is_bound_aux (function.update_ite σ x bool.tt) P)

def simult_to_is_bound (P : formula) : bool_formula :=
  simult_to_is_bound_aux (fun _, bool.ff) P


example
  (P : formula)
  (binders : finset variable_)
  (σ : variable_ → bool)
  (h1 : ∀ (v : variable_), v ∈ binders ↔ σ v = bool.tt) :
  to_is_bound_aux binders P = simult_to_is_bound_aux σ P :=
begin
  induction P generalizing binders σ,
  case formula.true_ : binders σ
  { admit },
  case formula.pred_ : name args binders σ
  {
    unfold simult_to_is_bound_aux,
    unfold to_is_bound_aux,
    congr' 1,
    simp only [list.map_eq_map_iff],
    intros v a1,
    specialize h1 v,
    simp only [h1],
    simp only [bool.to_bool_coe],
  },
  case formula.eq_ : P_ᾰ P_ᾰ_1 binders σ
  { admit },
  case formula.not_ : P_ᾰ P_ih binders σ
  { admit },
  case formula.imp_ : P_ᾰ P_ᾰ_1 P_ih_ᾰ P_ih_ᾰ_1 binders σ
  { admit },
  case formula.forall_ : x P P_ih binders σ
  {
    unfold simult_to_is_bound_aux,
    unfold to_is_bound_aux,
    squeeze_simp,
    apply P_ih,
    intros v,
    split,
    intros a1,
    squeeze_simp at a1,
    cases a1,
    unfold function.update_ite,
    split_ifs,
    refl,
    specialize h1 v,
    cases h1,
    exact h1_mp a1,
    unfold function.update_ite,
    split_ifs,
    refl,
    unfold function.update_ite,
    split_ifs,
    squeeze_simp,
    right,
    exact h,
    intros a1,
    specialize h1 v,
    cases h1,
    squeeze_simp,
    left,
    exact h1_mpr a1,
  },
end



example
  (P : formula)
  (v u : variable_)
  (binders : finset variable_)
  (h1 : v ∉ binders) :
  simult_admits_aux (function.update_ite id v u) binders P →
    fast_admits_aux v u binders P :=
begin
  induction P generalizing binders,
  case formula.true_ : binders h1
  {
    dunfold fast_admits_aux,
    dunfold simult_admits_aux,
    exact dec_trivial,
  },
  case formula.pred_ : name args binders h1
  {
    dunfold fast_admits_aux,
    dunfold simult_admits_aux,
    dunfold function.update_ite,
    intros a1 a2,
    specialize a1 v,
    simp only [eq_self_iff_true, if_true, and_imp] at a1,
    exact a1 a2 h1,
  },
  case formula.eq_ : x y binders h1
  {
    dunfold fast_admits_aux,
    dunfold simult_admits_aux,
    dunfold function.update_ite,
    intros a1 a2,
    cases a1,
    cases a2,
    {
      subst a2,
      simp only [eq_self_iff_true, if_true] at a1_left,
      exact a1_left h1,
    },
    {
      subst a2,
      simp only [eq_self_iff_true, if_true] at a1_right,
      exact a1_right h1,
    }
  },
  case formula.not_ : P P_ih binders h1
  {
    dunfold fast_admits_aux,
    dunfold simult_admits_aux,
    exact P_ih binders h1,
  },
  case formula.imp_ : P Q P_ih Q_ih binders h1
  {
    dunfold fast_admits_aux,
    dunfold simult_admits_aux,
    tauto,
  },
  case formula.forall_ : x P P_ih binders h1
  {
    dunfold fast_admits_aux,
    dunfold simult_admits_aux,
    intros a1,
    by_cases c1 : v = x,
    {
      apply or.intro_left,
      exact c1,
    },
    {
      apply or.intro_right,
      apply P_ih,
      {
        simp only [finset.mem_union, finset.mem_singleton],
        push_neg,
        split,
        {
          exact h1,
        },
        {
          exact c1,
        }
      },
      {
        exact a1,
      }
    }
  },
end



example
  (P : formula)
  (v u : variable_)
  (binders : finset variable_) :
  simult_admits_aux (function.update_ite id v u) binders P →
    admits_aux v u binders P :=
begin
  induction P generalizing binders,
  case formula.true_ : binders
  { admit },
  case formula.pred_ : name args binders
  {
    unfold admits_aux,
    unfold simult_admits_aux,
    unfold function.update_ite,
    intros a1 a2 contra,
    cases a2,
    specialize a1 v,
    apply a1,
    split,
    exact a2_left,
    exact a2_right,
    squeeze_simp,
    exact contra,
  },
  case formula.eq_ : P_ᾰ P_ᾰ_1 binders
  { admit },
  case formula.not_ : P_ᾰ P_ih binders
  { admit },
  case formula.imp_ : P_ᾰ P_ᾰ_1 P_ih_ᾰ P_ih_ᾰ_1 binders
  { admit },
  case formula.forall_ : x P P_ih binders
  {
    unfold admits_aux,
    unfold simult_admits_aux,
    apply P_ih,
  },
end


example
  (P : formula)
  (v u : variable_)
  (binders : finset variable_) :
  admits_aux v u binders P →
    simult_admits_aux (function.update_ite id v u) binders P :=
begin
  induction P generalizing binders,
  case formula.true_ : binders
  { admit },
  case formula.pred_ : name args binders
  {
    unfold simult_admits_aux,
    unfold function.update_ite,
    unfold admits_aux,
    intros a1 x a2,
    split_ifs,
    {
      subst h,
      exact a1 a2,
    },
    {
      simp only [id.def],
      cases a2,
      exact a2_right,
    }
  },
  case formula.eq_ : P_ᾰ P_ᾰ_1 binders
  { admit },
  case formula.not_ : P_ᾰ P_ih binders
  { admit },
  case formula.imp_ : P_ᾰ P_ᾰ_1 P_ih_ᾰ P_ih_ᾰ_1 binders
  { admit },
  case formula.forall_ : x P P_ih binders
  {
    unfold simult_admits_aux,
    unfold admits_aux,
    apply P_ih,
  },
end


example
  (P : formula)
  (σ : variable_ → variable_)
  (binders : finset variable_)
  (h1 : simult_admits_aux σ binders P) :
  to_is_bound_aux binders P =
    to_is_bound_aux binders (simult_replace_free_aux σ binders P) :=
begin
  induction P generalizing binders,
  case formula.true_ : binders h1
  { admit },
  case formula.pred_ : name args binders h1
  {
    unfold simult_admits_aux at h1,

    unfold simult_replace_free_aux,
    unfold to_is_bound_aux,
    congr' 1,
    simp only [list.map_map],
    unfold function.comp,
    apply list.map_congr,
    simp only [bool.to_bool_eq],
    intros x a1,
    specialize h1 x,
    split_ifs; tauto,
  },
  case formula.eq_ : P_ᾰ P_ᾰ_1 binders h1
  { admit },
  case formula.not_ : P_ᾰ P_ih binders h1
  { admit },
  case formula.imp_ : P_ᾰ P_ᾰ_1 P_ih_ᾰ P_ih_ᾰ_1 binders h1
  { admit },
  case formula.forall_ : x P P_ih binders h1
  {
    unfold simult_admits_aux at h1,

    unfold simult_replace_free_aux,
    unfold to_is_bound_aux,
    simp only [eq_self_iff_true, true_and],
    apply P_ih,
    exact h1,
  },
end


example
  (P : formula)
  (σ : variable_ → variable_)
  (binders : finset variable_)
  (h1 : to_is_bound_aux binders P =
    to_is_bound_aux binders (simult_replace_free_aux σ binders P)) :
  simult_admits_aux σ binders P :=
begin
  induction P generalizing binders,
  case formula.true_ : binders h1
  { admit },
  case formula.pred_ : name args binders h1
  {
    unfold simult_replace_free_aux at h1,
    unfold to_is_bound_aux at h1,
    simp only [list.map_map, eq_self_iff_true, true_and] at h1,
    unfold function.comp at h1,

    unfold simult_admits_aux,
    intros v a1,
    cases a1,
    dsimp at *,
    simp only [list.map_eq_map_iff] at h1,
    simp only [bool.to_bool_eq] at h1,
    specialize h1 v a1_left,
    cases h1,
    split_ifs at h1_mpr,
    tauto,
  },
  case formula.eq_ : P_ᾰ P_ᾰ_1 binders h1
  { admit },
  case formula.not_ : P_ᾰ P_ih binders h1
  { admit },
  case formula.imp_ : P_ᾰ P_ᾰ_1 P_ih_ᾰ P_ih_ᾰ_1 binders h1
  { admit },
  case formula.forall_ : x P P_ih binders h1
  {
    unfold simult_replace_free_aux at h1,
    unfold to_is_bound_aux at h1,
    simp only [eq_self_iff_true, true_and] at h1,

    unfold simult_admits_aux,
    apply P_ih,
    exact h1,
  },
end
