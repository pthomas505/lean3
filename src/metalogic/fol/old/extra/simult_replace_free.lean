import .replace_free
import .misc_list

import data.finset


set_option pp.parens true


open formula


def simult_replace_free_aux (σ : variable_ → variable_) : finset variable_ → formula → formula
| _ true_ := true_
| binders (pred_ name args) :=
    pred_
    name
    (args.map (fun (x : variable_), if x ∈ binders then x else σ x))
| binders (eq_ x y) :=
    eq_
    (if x ∈ binders then x else σ x)
    (if y ∈ binders then y else σ y)
| binders (not_ P) := not_ (simult_replace_free_aux binders P)
| binders (imp_ P Q) :=
    imp_
    (simult_replace_free_aux binders P)
    (simult_replace_free_aux binders Q)
| binders (forall_ x P) :=
    forall_ x (simult_replace_free_aux (binders ∪ {x}) P)


def simult_replace_free (σ : variable_ → variable_) (P : formula) : formula := simult_replace_free_aux σ ∅ P


/--
  Specialized version of function.update.
-/
def function.update_ite
  {α β : Type}
  [decidable_eq α]
  (f : α → β)
  (a' : α) (b : β) (a : α) :=
  if a = a' then b else f a

/--
  fast_simult_replace_free σ P := The simultaneous replacement of each free occurence of any variable v in the formula P by σ v.
-/
def fast_simult_replace_free : (variable_ → variable_) → formula → formula
| _ true_ := true_
| σ (pred_ name args) := pred_ name (args.map σ)
| σ (eq_ x y) := eq_ (σ x) (σ y)
| σ (not_ P) := not_ (fast_simult_replace_free σ P)
| σ (imp_ P Q) := imp_ (fast_simult_replace_free σ P) (fast_simult_replace_free σ Q)
| σ (forall_ x P) := forall_ x (fast_simult_replace_free (function.update_ite σ x x) P)


@[simp]
lemma function.update_ite_idem
  {α β : Type}
  [decidable_eq α]
  (f : α → β)
  (a : α)
  (x y : β)  :
  function.update_ite (function.update_ite f a x) a y =
    function.update_ite f a y :=
begin
  funext,
  unfold function.update_ite,
  split_ifs,
  {
    refl,
  },
  {
    refl,
  }
end


lemma function.update_ite_id
  {α : Type}
  [decidable_eq α]
  (x : α) :
  function.update_ite (id : α → α) x x = id :=
begin
  funext,
  unfold function.update_ite,
  split_ifs,
  {
    subst h,
    simp only [id.def],
  },
  {
    refl,
  }
end


lemma fast_simult_replace_free_id
  (P : formula) :
  fast_simult_replace_free id P = P :=
begin
  induction P,
  case formula.true_
  {
    refl,
  },
  case formula.pred_ : name args
  {
    unfold fast_simult_replace_free,
    simp only [list.map_id, eq_self_iff_true, and_self],
  },
  case formula.eq_ : x y
  {
    refl,
  },
  case formula.not_ : P P_ih
  {
    solve_by_elim,
  },
  case formula.imp_ : P Q P_ih Q_ih
  {
    unfold fast_simult_replace_free,
    congr,
    {
      exact P_ih,
    },
    {
      exact Q_ih,
    }
  },
  case formula.forall_ : x P P_ih
  {
    unfold fast_simult_replace_free,
    simp only [eq_self_iff_true, true_and],
    simp only [function.update_ite_id],
    exact P_ih,
  },
end


example
  (P : formula)
  (v t : variable_) :
  fast_simult_replace_free (function.update_ite id v t) P = fast_replace_free v t P :=
begin
  induction P,
  case formula.true_
  {
    refl,
  },
  case formula.pred_ : name args
  {
    refl,
  },
  case formula.eq_ : x y
  {
    refl,
  },
  case formula.not_ : P P_ih
  {
    unfold fast_simult_replace_free,
    unfold fast_replace_free,
    congr,
    exact P_ih,
  },
  case formula.imp_ : P Q P_ih Q_ih
  {
    unfold fast_simult_replace_free,
    unfold fast_replace_free,
    congr,
    {
      exact P_ih,
    },
    {
      exact Q_ih,
    }
  },
  case formula.forall_ : x P P_ih
  {
    unfold fast_simult_replace_free,
    unfold fast_replace_free,
    split_ifs,
    {
      subst h,
      simp only [eq_self_iff_true, function.update_ite_idem, true_and],

      simp only [function.update_ite_id],
      apply fast_simult_replace_free_id,
    },
    {
      have s1 : (function.update_ite (function.update_ite (id : variable_ → variable_) v t) x x) = function.update_ite id v t,
      funext,
      unfold function.update_ite,
      split_ifs,
      {
        subst h_1,
        tauto,
      },
      {
        subst h_1,
        simp only [id.def],
      },
      {
        refl,
      },
      {
        refl,
      },

      simp only [eq_self_iff_true, true_and],
      simp only [s1],
      exact P_ih,
    }
  },
end


lemma huh
  (P : formula)
  (σ σ' : variable_ → variable_)
  (binders : finset variable_)
  (h1 : ∀ (v : variable_), v ∉ binders → σ v = σ' v) :
  simult_replace_free_aux σ binders P =
    simult_replace_free_aux σ' binders P :=
begin
  induction P generalizing binders,
  case formula.true_ : binders h1
  { admit },
  case formula.pred_ : name args binders h1
  {
    unfold simult_replace_free_aux,
    congr' 1,
    simp only [list.map_eq_map_iff],
    intros x a1,
    split_ifs,
    refl,
    exact h1 x h,
  },
  case formula.eq_ : P_ᾰ P_ᾰ_1 binders h1
  { admit },
  case formula.not_ : P_ᾰ P_ih binders h1
  { admit },
  case formula.imp_ : P_ᾰ P_ᾰ_1 P_ih_ᾰ P_ih_ᾰ_1 binders h1
  { admit },
  case formula.forall_ : x P P_ih binders h1
  {
    unfold simult_replace_free_aux,
    congr' 1,
    apply P_ih,
    intros v a1,
    simp only [finset.mem_union, finset.mem_singleton] at a1,
    push_neg at a1,
    cases a1,
    apply h1 v a1_left,
  },
end


example
  (P : formula)
  (σ : variable_ → variable_)
  (binders : finset variable_)
  (h1 : ∀ (v : variable_), v ∈ binders → v = σ v) :
  simult_replace_free_aux σ binders P =
    fast_simult_replace_free σ P :=
begin
  induction P generalizing binders σ,
  case formula.true_ : binders h1
  { admit },
  case formula.pred_ : name args binders σ h1
  {
    unfold fast_simult_replace_free,
    unfold simult_replace_free_aux,
    congr' 1,
    simp only [list.map_eq_map_iff],
    intros x a1,
    split_ifs,
    exact h1 x h,
    refl,
  },
  case formula.eq_ : P_ᾰ P_ᾰ_1 binders σ h1
  { admit },
  case formula.not_ : P_ᾰ P_ih binders σ h1
  { admit },
  case formula.imp_ : P_ᾰ P_ᾰ_1 P_ih_ᾰ P_ih_ᾰ_1 binders σ h1
  { admit },
  case formula.forall_ : x P P_ih binders σ h1
  {
    unfold fast_simult_replace_free,
    unfold simult_replace_free_aux,
    congr,

    rewrite huh P σ (function.update_ite σ x x),
    apply P_ih,
    {
      intros v a1,
      unfold function.update_ite,
      split_ifs,
      {
        exact h,
      },
      {
        simp only [finset.mem_union, finset.mem_singleton] at a1,
        tauto,
      },
    },
    {
      simp only [finset.mem_union, finset.mem_singleton, eq_self_iff_true, or_true],
      push_neg,
      intros v a1,
      cases a1,
      unfold function.update_ite,
      split_ifs,
      contradiction,
      refl,
    }
  },
end
