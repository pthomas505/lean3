import metalogic.fol.aux.function_update_ite


set_option pp.parens true


/--
  The type of individual variables.
  Individual variables range over elements of the domain.
-/
@[derive [inhabited, decidable_eq]]
structure ind_var : Type :=
(name : string)

/--
  The string representation of individual variables.
-/
def ind_var.repr : ind_var → string
| x := x.name

instance ind_var.has_repr : has_repr ind_var := has_repr.mk ind_var.repr


/--
  The type of predicate variables.
  Predicate variables range over predicate functions on the domain.

  Predicate variables of arity 0 are propositional variables (not propositional constants like T or F).
-/
@[derive [inhabited, decidable_eq]]
structure pred_var : Type :=
(name : string)
(arity : ℕ)

/--
  The string representation of predicate variables.
-/
def pred_var.repr : pred_var → string
| P := P.name ++ "_{" ++ P.arity.repr ++ "}"

instance pred_var.has_repr : has_repr pred_var := has_repr.mk pred_var.repr


/--
  The type of formulas.
-/
@[derive [inhabited, decidable_eq]]
inductive formula : Type
| pred_ (P : pred_var) : vector ind_var P.arity → formula
| not_ : formula → formula
| imp_ : formula → formula → formula
| forall_ : ind_var → formula → formula

open formula


/-
  D is a domain
-/
structure interpretation (D : Type) : Type :=
/-
  The domain is not empty.
-/
(nonempty : nonempty D)
/-
  The assignment of predicate variables to predicate functions on the domain.
  Predicate functions map lists of elements of the domain to {T, F}.
  (vector D P.arity → Prop) is a predicate function.
-/
(pred (P : pred_var) : (vector D P.arity → Prop))


-- The assignment of individual variables to elements of the domain.
def valuation (D : Type) := ind_var → D


def holds (D : Type) (I : interpretation D) : valuation D → formula → Prop
| V (pred_ X xs) := I.pred X (xs.map V)
| V (not_ phi) := ¬ holds V phi
| V (imp_ phi psi) := holds V phi → holds V psi
| V (forall_ x phi) := ∀ (d : D), holds (function.update_ite V x d) phi


def formula.is_valid (F : formula) : Prop :=
  ∀ (D : Type) (I : interpretation D) (V : valuation D),
    holds D I V F


/--
  ind_var.is_free_in v φ := True if and only if there is a free occurrence of the individual variable v in the formula φ.
-/
@[derive decidable]
def ind_var.is_free_in (v : ind_var) : formula → bool
| (pred_ _ xs) := v ∈ xs.to_list.to_finset
| (not_ phi) := ind_var.is_free_in phi
| (imp_ phi psi) := ind_var.is_free_in phi ∨ ind_var.is_free_in psi
| (forall_ x phi) := ¬ v = x ∧ ind_var.is_free_in phi


def ind_var.occurs_in (v : ind_var) : formula → Prop
| (pred_ _ xs) := v ∈ xs.to_list
| (not_ P) := ind_var.occurs_in P
| (imp_ P Q) := ind_var.occurs_in P ∨ ind_var.occurs_in Q
| (forall_ x P) := v = x ∨ ind_var.occurs_in P


def formula.is_atomic : formula → Prop
| (pred_ _ _) := true
| (not_ _) := false
| (imp_ _ _) := false
| (forall_ _ _) := false


/--
  pred_var.occurs_in P  := True if and only if there is an occurrence of the predicate variable Q in the formula φ.
-/
@[derive decidable]
def pred_var.occurs_in (P : pred_var) : formula → bool
| (pred_ X _) := X = P
| (not_ φ) := pred_var.occurs_in φ
| (imp_ φ ψ) := pred_var.occurs_in φ ∨ pred_var.occurs_in ψ
| (forall_ _ φ) := pred_var.occurs_in φ


def coincide
  {D : Type}
  (I J : interpretation D)
  (V_I V_J : valuation D)
  (phi : formula) :
  Prop :=
  (∀ (P : pred_var), P.occurs_in phi → I.pred P = J.pred P) ∧
  (∀ (v : ind_var), v.is_free_in phi → V_I v = V_J v)


def fast_admits_aux (v u : ind_var) : finset ind_var → formula → Prop
| binders (pred_ X xs) :=
    v ∈ xs.to_list → -- if there is a free occurrence of v in P
    u ∉ binders -- then it does not become a bound occurrence of u in P(u/v)
| binders (not_ phi) := fast_admits_aux binders phi
| binders (imp_ phi psi) := fast_admits_aux binders phi ∧ fast_admits_aux binders psi
| binders (forall_ x phi) := v = x ∨ fast_admits_aux (binders ∪ {x}) phi


def fast_admits (v u : ind_var) (F : formula) : Prop :=
  fast_admits_aux v u ∅ F


def fast_replace_free (v t : ind_var) : formula → formula
| (pred_ X xs) :=
    pred_
    X
    (xs.map (fun (x : ind_var), if x = v then t else x))
| (not_ phi) := not_ (fast_replace_free phi)
| (imp_ phi psi) := imp_ (fast_replace_free phi) (fast_replace_free psi)
| (forall_ x phi) :=
    if v = x
    then forall_ x phi -- v is not free in phi
    else forall_ x (fast_replace_free phi)


/--
  is_free_sub φ v t φ' := True if and only if φ' is the result of replacing in φ each free occurrence of v by a free occurrence of t.
-/
inductive is_free_sub : formula → ind_var → ind_var → formula → Prop

| pred_
  (X : pred_var) (xs : vector ind_var X.arity)
  (v t : ind_var) :
    is_free_sub (pred_ X xs) v t (pred_ X (xs.map (fun (x : ind_var), if x = v then t else x)))

| not_
  (phi : formula)
  (v t : ind_var)
  (phi' : formula) :
  is_free_sub phi v t phi' →
  is_free_sub phi.not_ v t phi'.not_

| imp_
  (phi psi : formula)
  (v t : ind_var)
  (phi' psi' : formula) :
  is_free_sub phi v t phi' →
  is_free_sub psi v t psi' →
  is_free_sub (phi.imp_ psi) v t (phi'.imp_ psi')

| forall_not_free_in
  (x : ind_var) (phi : formula)
  (v t : ind_var) :
  ¬ v.is_free_in (forall_ x phi) →
  is_free_sub (forall_ x phi) v t (forall_ x phi)

| forall_free_in
  (x : ind_var) (phi : formula)
  (v t : ind_var)
  (phi' : formula) :
  v.is_free_in (forall_ x phi) →
  ¬ x = t →
  is_free_sub phi v t phi' →
  is_free_sub (forall_ x phi) v t (forall_ x phi')

@[derive decidable]
def admits_fun_aux (σ : ind_var → ind_var) : finset ind_var → formula → bool
| binders (pred_ X xs) :=
    ∀ (v : ind_var), v ∈ xs.to_list → v ∉ binders → σ v ∉ binders 
| binders (not_ phi) := admits_fun_aux binders phi
| binders (imp_ phi psi) := admits_fun_aux binders phi ∧ admits_fun_aux binders psi
| binders (forall_ x phi) := admits_fun_aux (binders ∪ {x}) phi

@[derive decidable]
def admits_fun (σ : ind_var → ind_var) (phi : formula) : Prop :=
  admits_fun_aux σ ∅ phi


def fast_replace_free_fun : (ind_var → ind_var) → formula → formula
| σ (pred_ X xs) := pred_ X (xs.map σ)
| σ (not_ phi) := not_ (fast_replace_free_fun σ phi)
| σ (imp_ phi psi) := imp_ (fast_replace_free_fun σ phi) (fast_replace_free_fun σ psi)
| σ (forall_ x phi) := forall_ x (fast_replace_free_fun (function.update_ite σ x x) phi)


inductive is_free_sub_fun : formula → (ind_var → ind_var) → formula → Prop

| pred_
  (X : pred_var) (xs : vector ind_var X.arity)
  (σ : ind_var → ind_var) :
    is_free_sub_fun (pred_ X xs) σ (pred_ X (xs.map σ))

| not_
  (phi : formula)
  (σ : ind_var → ind_var)
  (phi' : formula) :
  is_free_sub_fun phi σ phi' →
  is_free_sub_fun phi.not_ σ phi'.not_

| imp_
  (phi psi : formula)
  (σ : ind_var → ind_var)
  (phi' psi' : formula) :
  is_free_sub_fun phi σ phi' →
  is_free_sub_fun psi σ psi' →
  is_free_sub_fun (phi.imp_ psi) σ (phi'.imp_ psi')

| forall_not_free_in
  (x : ind_var) (phi : formula)
  (σ : ind_var → ind_var) :
  (∀ (v : ind_var), v.is_free_in (forall_ x phi) → σ v = v) →
  is_free_sub_fun (forall_ x phi) σ (forall_ x phi)

| forall_free_in
  (x : ind_var) (phi : formula)
  (σ : ind_var → ind_var)
  (phi' : formula) :
  ¬ (∀ (v : ind_var), v.is_free_in (forall_ x phi) → σ v = v) →
  (∀ (v : ind_var), v.is_free_in (forall_ x phi) → ¬ σ v = x) →
  is_free_sub_fun phi σ phi' →
  is_free_sub_fun (forall_ x phi) σ (forall_ x phi')


def is_free_sub_chain_aux : list formula → list ind_var → list ind_var → Prop
| (last :: list.nil) list.nil list.nil := true
| (fst :: snd :: tl) (x :: xs) (y :: ys) :=
    is_free_sub fst x y snd ∧ is_free_sub_chain_aux (snd :: tl) xs ys
| _ _ _ := false

def is_free_sub_chain (F : formula) (xs ys : list ind_var) (G : formula) : Prop :=
  ∃ (l : list formula), is_free_sub_chain_aux ((F :: l) ++ [G]) xs ys


/--
  is_pred_sub A P zs H B := The formula A is said to be transformed into the formula B by a substitution of H* for P z₁ ... zₙ, abbreviated: Sub A (P zⁿ / H*) B, iff B is obtained from A upon replacing in A each occurrence of a derivative of the name form P z₁ ... zₙ by the corresponding derivative of the substituend H*, provided that: (i) P does not occur in a component formula (∀ x A₁) of A if x is a parameter of H*, and (ii) the name variable zₖ, k = 1, ..., n, is not free in a component formula (∀ x H) of H* if P t₁ ... tₙ occurs in A with x occurring in tₖ. If conditions (i) and (ii) are not satisfied, then the indicated substitution for predicate variables is left undefined.
-/
inductive is_pred_sub (P : pred_var) (zs : vector ind_var P.arity) (H : formula) : formula → formula → Prop

/-
  If A is an atomic formula not containing P then Sub A (P zⁿ / H*) A.
-/
| pred_not_occurs_in
  (A : formula) :
  A.is_atomic →
  ¬ P.occurs_in A →
  is_pred_sub A A

  /-
  If A = P t₁ ... tₙ and Sf H* (zⁿ / tⁿ) B, then Sub A (P zⁿ / H*) B.

  Sf H* (zⁿ / tⁿ) B :=
    admits_fun (function.update_list_ite id zs.to_list ts.to_list) H* ∧ 
    fast_replace_free_fun (function.update_list_ite id zs.to_list ts.to_list) H* = B
  -/
| pred_occurs_in
  (A : formula)
  (ts : vector ind_var P.arity)
  (B : formula) :
  A = pred_ P ts →
  admits_fun (function.update_list_ite id zs.to_list ts.to_list) H →
  fast_replace_free_fun (function.update_list_ite id zs.to_list ts.to_list) H = B → 
  is_pred_sub (pred_ P ts) B

/-
  If A = (¬ A₁) and Sub A₁ (P zⁿ / H*) B₁, then Sub A (P zⁿ / H*) (¬ B₁).
-/
| not_
  (A₁ : formula)
  (B₁ : formula) :
  is_pred_sub A₁ B₁ →
  is_pred_sub A₁.not_ B₁.not_

/-
  If A = (A₁ → A₂), Sub A₁ (P zⁿ / H*) B₁, and Sub A₂ (P zⁿ / H*) B₂, then Sub A (P zⁿ / H*) (B₁ → B₁).
-/
| imp_
  (A₁ A₂ : formula)
  (B₁ B₂ : formula) :
  is_pred_sub A₁ B₁ →
  is_pred_sub A₂ B₂ →
  is_pred_sub (A₁.imp_ A₂) (B₁.imp_ B₂)

/-
  If A = (∀ x A₁) and P does not occur in A then Sub A (P zⁿ / H*) A.
-/
| forall_not_occurs_in
  (x : ind_var)
  (A₁ : formula) :
  ¬ P.occurs_in (forall_ x A₁) →
  is_pred_sub (forall_ x A₁) (forall_ x A₁)

/-
  If A = (∀ x A₁), P occurs in A, x is not free in H*, and Sub A₁ (P zⁿ / H*) B₁, then Sub A (P zⁿ / H*) (∀ x B₁).
-/
| forall_occurs_in
  (x : ind_var)
  (A₁ : formula)
  (B₁ : formula) :
  P.occurs_in (forall_ x A₁) →
  ¬ x.is_free_in H →
  is_pred_sub A₁ B₁ →
  is_pred_sub (forall_ x A₁) (forall_ x B₁)


lemma holds_congr_ind_var
  {D : Type}
  (I : interpretation D)
  (V V' : valuation D)
  (F : formula)
  (h1 : ∀ (v : ind_var), v.is_free_in F → V v = V' v) :
  holds D I V F ↔ holds D I V' F :=
begin
  induction F generalizing V V',
  case formula.pred_ : X xs V V' h1
  {
    unfold ind_var.is_free_in at h1,
    squeeze_simp at h1,

    unfold holds,
    congr' 2,
    ext1,
    squeeze_simp,
    apply h1,
    squeeze_simp,
  },
  case formula.not_ : phi phi_ih V V' h1
  {
    apply not_congr,
    exact phi_ih V V' h1,
  },
  case formula.imp_ : phi psi phi_ih psi_ih V V' h1
  {
    unfold ind_var.is_free_in at h1,
    squeeze_simp at h1,

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
    unfold ind_var.is_free_in at h1,
    squeeze_simp at h1,

    unfold holds,
    apply forall_congr,
    intros d,
    apply phi_ih,
    intros a a1,
    unfold function.update_ite,
    split_ifs,
    {
      refl,
    },
    {
      exact h1 a h a1,
    }
  },
end


lemma holds_congr_pred_var
  {D : Type}
  (I I' : interpretation D)
  (V : valuation D)
  (F : formula)
  (h1 : ∀ (P : pred_var), P.occurs_in F → I.pred P = I'.pred P) :
  holds D I V F ↔ holds D I' V F :=
begin
  induction F generalizing V,
  case formula.pred_ : X xs V
  {
    unfold pred_var.occurs_in at h1,
    squeeze_simp at h1,

    unfold holds,
    induction h1,
    refl,
  },
  case formula.not_ : phi phi_ih V
  {
    unfold pred_var.occurs_in at h1,

    unfold holds,
    apply not_congr,
    apply phi_ih h1,
  },
  case formula.imp_ : phi psi phi_ih psi_ih V
  {
    unfold pred_var.occurs_in at h1,
    squeeze_simp at h1,

    unfold holds,
    apply imp_congr,
    {
      apply phi_ih,
      intros P a1,
      apply h1,
      left,
      exact a1,
    },
    {
      apply psi_ih,
      intros P a1,
      apply h1,
      right,
      exact a1,
    }
  },
  case formula.forall_ : x phi phi_ih V
  {
    unfold pred_var.occurs_in at h1,

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
    apply holds_congr_ind_var,
    exact h1_right,
  },
  {
    apply holds_congr_pred_var,
    exact h1_left,
  }
end


lemma substitution_theorem_aux
  {D : Type}
  (I : interpretation D)
  (val val' : valuation D)
  (v t : ind_var)
  (binders : finset ind_var)
  (P : formula)
  (h1 : fast_admits_aux v t binders P)
  (h2 : ∀ (v : ind_var), ¬ v ∈ binders → val' v = val v) :
  holds D I (function.update_ite val v (val' t)) P ↔
    holds D I val (fast_replace_free v t P) :=
begin
  induction P generalizing binders val,
  case formula.pred_ : name args binders val h1
  {
    unfold fast_admits_aux at h1,

    unfold fast_replace_free,
    unfold holds,
    congr' 2,
    ext1,
    squeeze_simp,
    split_ifs,
    subst h,
    unfold function.update_ite,
    split_ifs,
    apply h2,
    apply h1,
    squeeze_simp,
    apply h2,
    apply h1,
    squeeze_simp,
    unfold function.update_ite,
    split_ifs,
    refl,
  },
  case formula.not_ : P P_ih binders val h1
  {
    unfold fast_admits_aux at h1,

    unfold fast_replace_free,
    unfold holds,
    apply not_congr,
    apply P_ih binders,
    exact h1,
    exact h2,
  },
  case formula.imp_ : P Q P_ih Q_ih binders val h1
  {
    unfold fast_admits_aux at h1,
    cases h1,

    unfold fast_replace_free,
    unfold holds,
    apply imp_congr,
    {
      apply P_ih binders,
      exact h1_left,
      exact h2,
    },
    {
      apply Q_ih binders,
      exact h1_right,
      exact h2,
    }
  },
  case formula.forall_ : x P P_ih binders val h1
  {
    unfold fast_admits_aux at h1,

    unfold fast_replace_free,
    split_ifs,
    {
      unfold holds,
      apply forall_congr,
      intros d,
      subst h,
      congr' 2,
      funext,
      unfold function.update_ite,
      split_ifs;
      refl,
    },
    {
      unfold holds,
      apply forall_congr,
      intros d,
      specialize P_ih (binders ∪ {x}),

      rewrite <- P_ih,
      congr' 2,
      funext,
      unfold function.update_ite,
      split_ifs,
      subst h_1,
      subst h_2,
      contradiction,
      refl,
      refl,
      refl,
      cases h1,
      contradiction,
      exact h1,
      unfold function.update_ite,
      intros a,
      split_ifs,
      cases h1,
      contradiction,
      subst h_1,
      simp only [finset.mem_union, finset.mem_singleton, eq_self_iff_true, or_true, not_true, is_empty.forall_iff],
      intros a1,
      apply h2,
      simp only [finset.mem_union, finset.mem_singleton] at a1,
      push_neg at a1,
      cases a1,
      exact a1_left,
    }
  },
end


theorem substitution_theorem
  {D : Type}
  (I : interpretation D)
  (val : valuation D)
  (v t : ind_var)
  (P : formula)
  (h1 : fast_admits v t P) :
  holds D I (function.update_ite val v (val t)) P ↔
    holds D I val (fast_replace_free v t P) :=
begin
  unfold fast_admits at h1,
  apply substitution_theorem_aux,
  exact h1,
  simp only [finset.not_mem_empty, not_false_iff, eq_self_iff_true, forall_const],
end


example
  (v t : ind_var)
  (P : formula)
  (h1 : fast_admits v t P)
  (h2 : P.is_valid) :
  (fast_replace_free v t P).is_valid :=
begin
  unfold formula.is_valid at h2,

  unfold formula.is_valid,
  intros D I V,
  rewrite <- substitution_theorem,
  apply h2,
  exact h1,
end


theorem substitution_theorem_ind
  {D : Type}
  (I : interpretation D)
  (val : valuation D)
  (v t : ind_var)
  (P P' : formula)
  (h1 : is_free_sub P v t P') :
  holds D I (function.update_ite val v (val t)) P ↔
    holds D I val P' :=
begin
  induction h1 generalizing val,
  case is_free_sub.pred_ : h1_P h1_xs h1_v h1_t
  {
    unfold holds,
    congr' 2,
    ext1,
    squeeze_simp,
    split_ifs,
    unfold function.update_ite,
    split_ifs,
    refl,
    unfold function.update_ite,
    split_ifs,
    refl,
  },
  case is_free_sub.not_ : h1_P h1_v h1_t h1_P' h1_1 h1_ih
  {
    unfold holds,
    apply not_congr,
    apply h1_ih,
  },
  case is_free_sub.imp_ : h1_P h1_Q h1_v h1_t h1_P' h1_Q' h1_1 h1_2 h1_ih_1 h1_ih_2
  {
    unfold holds,
    apply imp_congr,
    apply h1_ih_1,
    apply h1_ih_2,
  },
  case is_free_sub.forall_not_free_in : h1_x h1_P h1_v h1_t h1_1
  {
    unfold ind_var.is_free_in at h1_1,
    squeeze_simp at h1_1,

    unfold holds,
    apply forall_congr,
    intros d,
    apply holds_congr_ind_var,
    intros x a1,
    unfold function.update_ite,
    split_ifs,
    refl,
    subst h_1,
    specialize h1_1 h,
    rewrite h1_1 at a1,
    contradiction,
    refl,
  },
  case is_free_sub.forall_free_in : h1_x h1_P h1_v h1_t h1_P' h1_1 h1_2 h1_3 h1_ih
  {
    unfold ind_var.is_free_in at h1_1,
    squeeze_simp at h1_1,
    cases h1_1,

    unfold holds,
    apply forall_congr,
    intros d,

    specialize h1_ih (function.update_ite val h1_x d),

    rewrite <- h1_ih,
    apply holds_congr_ind_var,
    intros x a1,
    funext,
    unfold function.update_ite,
    split_ifs,
    refl,
    subst h_1,
    contradiction,
    refl,
    subst h_2,
    contradiction,
    refl,
    refl,
  },
end


lemma substitution_theorem_fun_aux
  {D : Type}
  (I : interpretation D)
  (val val' : valuation D)
  (σ σ' : ind_var → ind_var)
  (binders : finset ind_var)
  (P : formula)
  (h1 : admits_fun_aux σ binders P)

  (h2 : ∀ (x : ind_var), x ∈ binders ∨ σ' x ∉ binders → (val x = val' (σ' x)))
  (h2' : ∀ (x : ind_var), x ∈ binders → σ' x = x)

  (h3 : ∀ (x : ind_var), x ∉ binders -> σ' x = σ x) :
  holds D I val P ↔
    holds D I val' (fast_replace_free_fun σ' P) :=
begin
  induction P generalizing binders val val' σ σ',
  case formula.pred_ : name args binders val val' σ σ' h1
  {
    unfold admits_fun_aux at h1,
    simp only [bool.of_to_bool_iff] at h1,

    unfold fast_replace_free_fun,
    unfold holds,
    congr' 2,
    ext1,
    squeeze_simp,
    apply h2,
    by_cases c1 : args.nth m ∈ binders,
    left,
    exact c1,
    right,
    rewrite h3,
    apply h1,
    squeeze_simp,
    exact c1,
    exact c1,
  },
  case formula.not_ : P P_ih binders val h1
  {
    unfold fast_replace_free_fun,
    apply not_congr,
    apply P_ih,
    unfold admits_fun_aux at h1,
    exact h1,
    exact h2,
    exact h2',
    exact h3,
  },
  case formula.imp_ : P Q P_ih Q_ih binders val h1
  {
    unfold admits_fun_aux at h1,
    squeeze_simp at h1,
    cases h1,

    unfold fast_replace_free_fun,
    apply imp_congr,
    apply P_ih,
    exact h1_left,
    exact h2,
    exact h2',
    exact h3,

    apply Q_ih,
    exact h1_right,
    exact h2,
    exact h2',
    exact h3,
  },
  case formula.forall_ : x P P_ih binders val val' σ σ' h1 h2 h2' h3
  {
    unfold admits_fun_aux at h1,

    unfold fast_replace_free_fun,
    unfold holds,
    apply forall_congr,
    intros d,

    apply P_ih (binders ∪ {x}) (function.update_ite val x d) (function.update_ite val' x d) σ (function.update_ite σ' x x) h1,
    {
      intros v,
      simp only [finset.mem_union, finset.mem_singleton],
      unfold function.update_ite,
      split_ifs,
      simp only [eq_self_iff_true, implies_true_iff],
      intros a1,
      push_neg at a1,
      simp only [ne.def] at a1,
      cases a1,
      specialize h2' v,
      cases a1,
      specialize h2' a1,
      subst h_1,
      exfalso,
      apply h,
      symmetry,
      exact h2',
      contradiction,
      cases a1,
      contradiction,
      intros a2,
      apply h2,
      tauto,
    },
    {
      intros v a1,
      unfold function.update_ite,
      simp only [finset.mem_union, finset.mem_singleton] at a1,
      split_ifs,
      subst h,
      cases a1,
      apply h2',
      exact a1,
      contradiction,
    },
    {
      intros v a1,
      simp only [finset.mem_union, finset.mem_singleton] at a1,
      unfold function.update_ite,
      split_ifs,
      push_neg at a1,
      cases a1,
      contradiction,
      push_neg at a1,
      cases a1,
      apply h3,
      exact a1_left,
    }
  },
end


theorem substitution_theorem_fun
  {D : Type}
  (I : interpretation D)
  (val : valuation D)
  (σ : ind_var → ind_var)
  (P : formula)
  (h1 : admits_fun σ P) :
  holds D I (val ∘ σ)  P ↔
    holds D I val (fast_replace_free_fun σ P) :=
begin
  apply substitution_theorem_fun_aux,
  exact h1,
  simp only [finset.not_mem_empty, not_false_iff, false_or, eq_self_iff_true, forall_const],
  simp only [finset.not_mem_empty, is_empty.forall_iff, forall_const],
  simp only [finset.not_mem_empty, not_false_iff, eq_self_iff_true, forall_const],
end


example
  (σ : ind_var → ind_var)
  (P : formula)
  (h1 : admits_fun σ P)
  (h2 : P.is_valid) :
  (fast_replace_free_fun σ P).is_valid :=
begin
  unfold formula.is_valid at h2,

  unfold formula.is_valid,
  intros D I V,
  rewrite <- substitution_theorem_fun,
  apply h2,
  exact h1,
end


lemma pred_sub_aux
  (D : Type)
  (I J : interpretation D)
  (V : valuation D)
  (A : formula)
  (P : pred_var)
  (zs : vector ind_var P.arity)
  (H : formula)
  (B : formula)
  (h1 : is_pred_sub P zs H A B)
  (h2 : ∀ (Q : pred_var) (ds : vector D Q.arity), ¬ P = Q → (I.pred Q ds ↔ J.pred Q ds))
  (h3 : ∀ (ds : vector D P.arity), J.pred P ds ↔ holds D I (function.update_list_ite V zs.to_list ds.to_list) H) :
  holds D I V B ↔ holds D J V A :=
begin
  induction h1 generalizing V,
  case is_pred_sub.pred_not_occurs_in : h1_A h1_1 h1_2 V h3
  {
    apply coincidence_theorem,
    unfold coincide,
    split,
    {
      intros Q a1,
      funext ds,
      squeeze_simp,
      apply h2,
      intros contra,
      subst contra,
      contradiction,
    },
    {
      squeeze_simp,
    }
  },
  case is_pred_sub.pred_occurs_in : h1_A h1_ts h1_B h1_1 h1_2 h1_3 V h3
  {
    obtain s1 := substitution_theorem_fun I V (function.update_list_ite id zs.to_list h1_ts.to_list) H h1_2,
    rewrite h1_3 at s1,

    have s2 : (V ∘ function.update_list_ite id zs.to_list h1_ts.to_list) = (function.update_list_ite (V ∘ id) zs.to_list (h1_ts.to_list.map V)),
    apply function.update_list_ite_comp,

    rewrite s2 at s1,
    clear s2,
    squeeze_simp at s1,
    sorry,
  },
  case is_pred_sub.not_ : h1_A₁ h1_B₁ h1_ᾰ h1_ih V h3
  {
    unfold holds,
    apply not_congr,
    apply h1_ih,
    exact h3,
  },
  case is_pred_sub.imp_ : h1_A₁ h1_A₂ h1_B₁ h1_B₂ h1_1 h1_2 h1_ih_1 h1_ih_2 V h3
  {
    unfold holds,
    apply imp_congr,
    apply h1_ih_1,
    exact h3,
    apply h1_ih_2,
    exact h3,
  },
  case is_pred_sub.forall_not_occurs_in : h1_x h1_A₁ h1_1 V h3
  {
    unfold pred_var.occurs_in at h1_1,
    apply coincidence_theorem,
    unfold coincide,
    split,
    {
      unfold pred_var.occurs_in,
      intros Q a1,
      funext ds,
      squeeze_simp,
      apply h2,
      intros contra,
      apply h1_1,
      subst contra,
      exact a1,
    },
    {
      squeeze_simp,
    },
  },
  case is_pred_sub.forall_occurs_in : h1_x h1_A₁ h1_B₁ h1_1 h1_2 h1_3 h1_ih V h3
  {
    have s1 : ∀ (d : D) (ds : list D), holds D I (function.update_list_ite (function.update_ite V h1_x d) zs.to_list ds) H ↔ holds D I (function.update_list_ite V zs.to_list ds) H,
    {
      intros d ds,
      apply coincidence_theorem,
      unfold coincide,
      split,
      {
        squeeze_simp,
      },
      {
        intros v a1,
        clear h1_3, clear h3, clear h1_ih,
        induction zs.to_list generalizing ds,
        unfold function.update_list_ite,
        unfold function.update_ite,
        split_ifs,
        exfalso,
        apply h1_2,
        subst h,
        exact a1,
        refl,
        cases ds,
        {
          unfold function.update_list_ite,
          unfold function.update_ite,
          split_ifs,
          {
            exfalso,
            apply h1_2,
            subst h,
            exact a1,
          },
          {
            refl,
          }
        },
        {
          unfold function.update_list_ite,
          unfold function.update_ite,
          split_ifs,
          {
            refl,
          },
          {
            apply ih,
          }
        }
      },
    },

    unfold holds,
    apply forall_congr,
    intros d,
    apply h1_ih,
    sorry,
  },
end


example
  (A : formula)
  (P : pred_var)
  (zs : vector ind_var P.arity)
  (H : formula)
  (B : formula)
  (h1 : is_pred_sub P zs H A B)
  (h2 : A.is_valid) :
  B.is_valid :=
begin
  unfold formula.is_valid at h2,

  unfold formula.is_valid,
  intros D I V,

  let J : interpretation D := {
    nonempty := I.nonempty,
    pred := fun (R : pred_var) (ds : vector D R.arity), ite (¬ P = R) (I.pred R ds) (holds D I (function.update_list_ite V zs.to_list ds.to_list) H)
  },


  have s2 : (∀ (Q : pred_var) (ds : vector D Q.arity), (¬(P = Q)) → (I.pred Q ds ↔ J.pred Q ds)),
  {
    squeeze_simp,
    intros Q ds a1,
    split,
    split_ifs,
    tauto,
    split_ifs,
    tauto,
  },

  have s3 : (∀ (ds : vector D P.arity), (J.pred P ds ↔ holds D I (function.update_list_ite V zs.to_list ds.to_list) H)),
  {
    squeeze_simp,
  },

  obtain s1 := pred_sub_aux D I J V A P zs H B h1 s2 s3,

  cases s1,
  apply s1_mpr,
  apply h2,
end






def replace_pred_fun (τ : Π (P : pred_var), vector ind_var P.arity × formula) : formula → formula

| (pred_ P ts) :=
  fast_replace_free_fun (function.update_list_ite id (τ P).fst.to_list ts.to_list) (τ P).snd

| (not_ phi) := not_ (replace_pred_fun phi)

| (imp_ phi psi) := imp_ (replace_pred_fun phi) (replace_pred_fun psi)

| (forall_ x phi) := forall_ x (replace_pred_fun phi)


def admits_pred_fun_aux (τ : Π (P : pred_var), vector ind_var P.arity × formula) : finset ind_var → formula → bool

| binders (pred_ P ts) :=
  admits_fun (function.update_list_ite id (τ P).fst.to_list ts.to_list) (τ P).snd ∧
 ∀ (x : ind_var), x ∈ binders → x.is_free_in (τ P).snd → ¬ x ∈ (τ P).fst.to_list

| binders (not_ phi) := admits_pred_fun_aux binders phi

| binders (imp_ phi psi) := admits_pred_fun_aux binders phi ∧ admits_pred_fun_aux binders psi

| binders (forall_ x phi) := admits_pred_fun_aux (binders ∪ {x}) phi


/-
lemma pred_sub_aux
  (D : Type)
  (I J : interpretation D)
  (V : valuation D)
  (A : formula)
  (P : pred_var)
  (zs : list ind_var)
  (H : formula)
  (B : formula)
  (h1 : is_pred_sub A P zs H B)
  (h2 : ∀ (Q : pred_var) (ds : list D), ¬ P = Q → (I.pred Q ds ↔ J.pred Q ds))
  (h3 : ∀ (ds : list D), J.pred P ds ↔ holds D I (function.update_list_ite V zs ds) H) :
  holds D I V B ↔ holds D J V A :=
-/


example
  (D : Type)
  (I J : interpretation D)
  (V : valuation D)
  (τ : Π (P : pred_var), vector ind_var P.arity × formula)
  (binders : finset ind_var)
  (phi : formula)
  (h1 : admits_pred_fun_aux τ binders phi)
  (h3 : ∀ (P : pred_var) (ds : vector D P.arity),
    J.pred P ds ↔ holds D I (function.update_list_ite V (τ P).fst.to_list ds.to_list) (τ P).snd) :
  holds D I V phi ↔ holds D J V (replace_pred_fun τ phi) :=
begin
  induction phi generalizing V binders,
  case formula.pred_ : P ts V binders h1
  {
    unfold admits_pred_fun_aux at h1,
    squeeze_simp at h1,
    unfold admits_fun at h1,
    cases h1,

    set zs := (τ P).fst,
    set H := (τ P).snd,
    set σ := (function.update_list_ite id zs.to_list ts.to_list),

    obtain s1 := substitution_theorem_fun I V (function.update_list_ite id zs.to_list ts.to_list) H h1_left,

    have s2 : (V ∘ function.update_list_ite id zs.to_list ts.to_list) = (function.update_list_ite (V ∘ id) zs.to_list (ts.to_list.map V)),
    apply function.update_list_ite_comp,

    simp only [s2] at s1,

    by_cases c1 : replace_pred_fun τ (pred_ P ts) = pred_ P ts,
    {
      simp only [c1],
      apply coincidence_theorem,
      unfold coincide,
      split,
      {
        unfold replace_pred_fun at c1,
        simp only [c1] at s1,
        intros Q a1,
        unfold pred_var.occurs_in at a1,
        squeeze_simp at a1,
        sorry,
      },
      {
        squeeze_simp,
      }
    },
    {
      unfold replace_pred_fun at c1,

      unfold replace_pred_fun,
      sorry,
    }
  },
  case formula.not_ : phi_ᾰ phi_ih V binders h1
  { admit },
  case formula.imp_ : phi_ᾰ phi_ᾰ_1 phi_ih_ᾰ phi_ih_ᾰ_1 V binders h1
  { admit },
  case formula.forall_ : x phi phi_ih V binders h1
  {
    unfold admits_pred_fun_aux at h1,

    unfold replace_pred_fun,
    unfold holds,
    apply forall_congr,
    intros d,
    apply phi_ih,
    apply h1,
  },
end
