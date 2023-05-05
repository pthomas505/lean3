import metalogic.fol.aux.function_update_ite


set_option pp.parens true


/--
  The type of individual variables.
  Individual variables range over elements of the domain.
-/
@[derive [inhabited, decidable_eq]]
inductive ind_var_ : Type
| mk : string → ind_var_

/--
  The string representation of individual variables.
-/
def ind_var_.repr : ind_var_ → string
| (ind_var_.mk name) := name

instance ind_var_.has_repr : has_repr ind_var_ := has_repr.mk ind_var_.repr


/--
  The type of predicate variables.
  Predicate variables range over predicate functions on the domain.
-/
@[derive [inhabited, decidable_eq]]
inductive pred_var_ : Type
| mk : string → pred_var_


/--
  The string representation of predicate variables.
-/
def pred_var_.repr : pred_var_ → string
| (pred_var_.mk name) := name

instance pred_var_.has_repr : has_repr pred_var_ := has_repr.mk pred_var_.repr


/--
  The type of formulas.
-/
@[derive [inhabited, decidable_eq]]
inductive formula : Type
| pred_ : pred_var_ → list ind_var_ → formula
| not_ : formula → formula
| imp_ : formula → formula → formula
| forall_ : ind_var_ → formula → formula

open formula


-- D is a domain
structure interpretation (D : Type) : Type :=
-- There is at least one element in the domain.
(nonempty : nonempty D)
-- The assignment of predicate variables to predicate functions on the domain.
-- Predicate functions map elements of the domain to {T, F}.
-- list D → Prop is a predicate function.
(pred : pred_var_ → (list D → Prop))

/-
  pred_ _ [] is a propositional variable (not a propositional constant like T or F).
-/

-- The assignment of individual variables to elements of the domain.
def valuation (D : Type) := ind_var_ → D


def holds (D : Type) (I : interpretation D) : valuation D → formula → Prop
| V (pred_ X xs) := I.pred X (xs.map V)
| V (not_ P) := ¬ holds V P
| V (imp_ P Q) := holds V P → holds V Q
| V (forall_ x P) := ∀ (d : D), holds (function.update_ite V x d) P


def formula.is_valid (P : formula) : Prop :=
  ∀ (D : Type) (I : interpretation D) (V : valuation D),
    holds D I V P


/--
  ind_var_.is_free_in v φ := True if and only if there is a free occurrence of the individual variable v in the formula φ.
-/
@[derive decidable]
def ind_var_.is_free_in (v : ind_var_) : formula → bool
| (pred_ _ xs) := v ∈ xs.to_finset
| (not_ P) := ind_var_.is_free_in P
| (imp_ P Q) := ind_var_.is_free_in P ∨ ind_var_.is_free_in Q
| (forall_ x φ) := ¬ v = x ∧ ind_var_.is_free_in φ


def ind_var_.occurs_in (v : ind_var_) : formula → Prop
| (pred_ name args) := v ∈ args.to_finset
| (not_ P) := ind_var_.occurs_in P
| (imp_ P Q) := ind_var_.occurs_in P ∨ ind_var_.occurs_in Q
| (forall_ x P) := v = x ∨ ind_var_.occurs_in P


def formula.is_atomic : formula → Prop
| (pred_ _ _) := true
| (not_ P) := false
| (imp_ P Q) := false
| (forall_ x P) := false


/--
  pred_var_.occurs_in Q φ := True if and only if there is an occurrence of the predicate variable Q in the formula φ.
-/
@[derive decidable]
def pred_var_.occurs_in (Q : pred_var_) : formula → bool
| (pred_ P _) := P = Q
| (not_ φ) := pred_var_.occurs_in φ
| (imp_ φ ψ) := pred_var_.occurs_in φ ∨ pred_var_.occurs_in ψ
| (forall_ _ φ) := pred_var_.occurs_in φ


def coincide
  {D : Type}
  (I J : interpretation D)
  (val_I val_J : valuation D)
  (φ : formula) :
  Prop :=
  (∀ (P : pred_var_), P.occurs_in φ → I.pred P = J.pred P) ∧
  (∀ (v : ind_var_), v.is_free_in φ → val_I v = val_J v)


def fast_admits_aux (v u : ind_var_) : finset ind_var_ → formula → Prop
| binders (pred_ name args) :=
    v ∈ args → -- if there is a free occurrence of v in P
    u ∉ binders -- then it does not become a bound occurrence of u in P(u/v)
| binders (not_ P) := fast_admits_aux binders P
| binders (imp_ P Q) := fast_admits_aux binders P ∧ fast_admits_aux binders Q
| binders (forall_ x P) := v = x ∨ fast_admits_aux (binders ∪ {x}) P


def fast_admits (v u : ind_var_) (P : formula) : Prop :=
  fast_admits_aux v u ∅ P


def fast_replace_free (v t : ind_var_) : formula → formula
| (pred_ name args) :=
    pred_
    name
    (args.map (fun (x : ind_var_), if x = v then t else x))
| (not_ P) := not_ (fast_replace_free P)
| (imp_ P Q) := imp_ (fast_replace_free P) (fast_replace_free Q)
| (forall_ x P) :=
    if v = x
    then forall_ x P -- v is not free in P
    else forall_ x (fast_replace_free P)


/--
  is_free_sub φ v t φ' := True if and only if φ' is the result of replacing in φ each free occurrence of v by a free occurrence of t.
-/
inductive is_free_sub : formula → ind_var_ → ind_var_ → formula → Prop

| pred_
  (P : pred_var_) (xs : list ind_var_)
  (v t : ind_var_) :
    is_free_sub (pred_ P xs) v t (pred_ P (xs.map (fun (x : ind_var_), if x = v then t else x)))

| not_
  (P : formula)
  (v t : ind_var_)
  (P' : formula) :
  is_free_sub P v t P' →
  is_free_sub P.not_ v t P'.not_

| imp_
  (P Q : formula)
  (v t : ind_var_)
  (P' Q' : formula) :
  is_free_sub P v t P' →
  is_free_sub Q v t Q' →
  is_free_sub (P.imp_ Q) v t (P'.imp_ Q')

| forall_not_free_in
  (x : ind_var_) (P : formula)
  (v t : ind_var_) :
  ¬ v.is_free_in (forall_ x P) →
  is_free_sub (forall_ x P) v t (forall_ x P)

| forall_free_in
  (x : ind_var_) (P : formula)
  (v t : ind_var_)
  (P' : formula) :
  v.is_free_in (forall_ x P) →
  ¬ x = t →
  is_free_sub P v t P' →
  is_free_sub (forall_ x P) v t (forall_ x P')

@[derive decidable]
def admits_fun_aux (σ : ind_var_ → ind_var_) : finset ind_var_ → formula → bool
| binders (pred_ name args) :=
    ∀ (v : ind_var_), v ∈ args → v ∉ binders → σ v ∉ binders 
| binders (not_ P) := admits_fun_aux binders P
| binders (imp_ P Q) := admits_fun_aux binders P ∧ admits_fun_aux binders Q
| binders (forall_ x P) := admits_fun_aux (binders ∪ {x}) P

@[derive decidable]
def admits_fun (σ : ind_var_ → ind_var_) (P : formula) : Prop :=
  admits_fun_aux σ ∅ P


def fast_replace_free_fun : (ind_var_ → ind_var_) → formula → formula
| σ (pred_ name args) := pred_ name (args.map σ)
| σ (not_ P) := not_ (fast_replace_free_fun σ P)
| σ (imp_ P Q) := imp_ (fast_replace_free_fun σ P) (fast_replace_free_fun σ Q)
| σ (forall_ x P) := forall_ x (fast_replace_free_fun (function.update_ite σ x x) P)


inductive is_free_sub_fun : formula → (ind_var_ → ind_var_) → formula → Prop

| pred_
  (P : pred_var_) (xs : list ind_var_)
  (σ : ind_var_ → ind_var_) :
    is_free_sub_fun (pred_ P xs) σ (pred_ P (xs.map σ))

| not_
  (P : formula)
  (σ : ind_var_ → ind_var_)
  (P' : formula) :
  is_free_sub_fun P σ P' →
  is_free_sub_fun P.not_ σ P'.not_

| imp_
  (P Q : formula)
  (σ : ind_var_ → ind_var_)
  (P' Q' : formula) :
  is_free_sub_fun P σ P' →
  is_free_sub_fun Q σ Q' →
  is_free_sub_fun (P.imp_ Q) σ (P'.imp_ Q')

| forall_not_free_in
  (x : ind_var_) (P : formula)
  (σ : ind_var_ → ind_var_) :
  (∀ (v : ind_var_), v.is_free_in (forall_ x P) → σ v = v) →
  is_free_sub_fun (forall_ x P) σ (forall_ x P)

| forall_free_in
  (x : ind_var_) (P : formula)
  (σ : ind_var_ → ind_var_)
  (P' : formula) :
  ¬ (∀ (v : ind_var_), v.is_free_in (forall_ x P) → σ v = v) →
  (∀ (v : ind_var_), v.is_free_in (forall_ x P) → ¬ σ v = x) →
  is_free_sub_fun P σ P' →
  is_free_sub_fun (forall_ x P) σ (forall_ x P')


def is_free_sub_chain_aux : list formula → list ind_var_ → list ind_var_ → Prop
| (last :: list.nil) list.nil list.nil := true
| (fst :: snd :: tl) (x :: xs) (y :: ys) :=
    is_free_sub fst x y snd ∧ is_free_sub_chain_aux (snd :: tl) xs ys
| _ _ _ := false

def is_free_sub_chain (P : formula) (xs ys : list ind_var_) (Q : formula) : Prop :=
  ∃ (l : list formula), is_free_sub_chain_aux ((P :: l) ++ [Q]) xs ys


def function.update_list_ite
  {α β : Type}
  [decidable_eq α]
  (f : α → β) :
  list α → list β → α → β
| (x :: xs) (y :: ys) := function.update_ite (function.update_list_ite xs ys) x y 
| _ _ := f


def function.update_list_ite'
  {α β : Type}
  [decidable_eq α]
  (f : α → β)
  (xs : list α)
  (ys : list β) :
  α → β :=
  list.foldr (fun (p : α × β) (g : α → β), function.update_ite f p.fst p.snd) f (list.zip xs ys) 

#eval function.update_list_ite' (fun (n : ℕ), n) [0, 3, 0] [10, 2, 2] 0


def replace_pred (P : pred_var_) (zs : list ind_var_) (H : formula) : formula → formula
| (pred_ Q ts) :=
  if P = Q
  then fast_replace_free_fun (function.update_list_ite id zs ts) H
  else pred_ Q ts
| (not_ φ) := not_ (replace_pred φ)
| (imp_ φ ψ) := imp_ (replace_pred φ) (replace_pred ψ)
| (forall_ x φ) := forall_ x (replace_pred φ)


@[derive decidable]
def admits_replace_pred (P : pred_var_) (zs : list ind_var_) (H : formula) : formula → bool
| (pred_ Q ts) :=
  P = Q ∧ admits_fun (function.update_list_ite id zs ts) H
| (not_ φ) := (admits_replace_pred φ)
| (imp_ φ ψ) := (admits_replace_pred φ) ∧ (admits_replace_pred ψ)
| (forall_ x φ) := P.occurs_in (forall_ x φ) → ¬ x.is_free_in H →
  admits_replace_pred φ


/--
  is_pred_sub A P zs H B := The formula A is said to be transformed into the formula B by a substitution of H* for P z₁ ... zₙ, abbreviated: Sub A (P zⁿ / H*) B, iff B is obtained from A upon replacing in A each occurrence of a derivative of the name form P z₁ ... zₙ by the corresponding derivative of the substituend H*, provided that: (i) P does not occur in a component formula (∀ x A₁) of A if x is a parameter of H*, and (ii) the name variable zₖ, k = 1, ..., n, is not free in a component formula (∀ x H) of H* if P t₁ ... tₙ occurs in A with x occurring in tₖ. If conditions (i) and (ii) are not satisfied, then the indicated substitution for predicate variables is left undefined.
-/
inductive is_pred_sub : formula → pred_var_ → list ind_var_ → formula → formula → Prop

/-
  If A is an atomic formula not containing P then Sub A (P zⁿ / H*) A.

  A := pred_ Q ts
-/
| pred_not_occurs_in
  (Q : pred_var_) (ts : list ind_var_)
  (P : pred_var_)
  (zs : list ind_var_)
  (H : formula) :
  ¬ P = Q →
  is_pred_sub (pred_ Q ts) P zs H (pred_ Q ts)

  /-
  If A = P t₁ ... tₙ and Sf H* (zⁿ / tⁿ) B, then Sub A (P zⁿ / H*) B.

  Sub A (P zⁿ / H*) B :=
    admits_fun (function.update_list_ite id zs ts) H ∧ 
    fast_replace_free_fun (function.update_list_ite id zs ts) H = B
  -/
| pred_occurs_in
  (P : pred_var_) (ts : list ind_var_)
  (zs : list ind_var_)
  (H : formula)
  (B : formula) :
  admits_fun (function.update_list_ite id zs ts) H →
  fast_replace_free_fun (function.update_list_ite id zs ts) H = B →
  is_pred_sub (pred_ P ts) P zs H B

| not_
  (A : formula)
  (P : pred_var_)
  (zs : list ind_var_)
  (H : formula)
  (B : formula) :
  is_pred_sub A P zs H B →
  is_pred_sub A.not_ P zs H B.not_

| imp_
  (A1 A2 : formula)
  (P : pred_var_)
  (zs : list ind_var_)
  (H : formula)
  (B1 B2 : formula) :
  is_pred_sub A1 P zs H B1 →
  is_pred_sub A2 P zs H B2 →
  is_pred_sub (A1.imp_ A2) P zs H (B1.imp_ B2)

| forall_not_occurs_in
  (x : ind_var_)
  (A : formula)
  (P : pred_var_)
  (zs : list ind_var_)
  (H : formula)
  (B : formula) :
  ¬ P.occurs_in (forall_ x A) →
  is_pred_sub (forall_ x A) P zs H (forall_ x A)

| forall_occurs_in
  (x : ind_var_)
  (A : formula)
  (P : pred_var_)
  (zs : list ind_var_)
  (H : formula)
  (B : formula) :
  P.occurs_in (forall_ x A) →
  ¬ x.is_free_in H →
  is_pred_sub A P zs H B →
  is_pred_sub (forall_ x A) P zs H (forall_ x B)


lemma admits_fun_aux_and_fast_replace_free_fun_imp_is_free_sub_fun
  (P P' : formula)
  (σ : ind_var_ → ind_var_)
  (binders : finset ind_var_)
  (h1 : admits_fun_aux σ binders P)
  (h2 : fast_replace_free_fun σ P = P') :
  is_free_sub_fun P σ P' :=
begin
  subst h2,
  sorry,
end


lemma holds_congr_ind_var
  {D : Type}
  (I : interpretation D)
  (val val' : valuation D)
  (φ : formula)
  (h1 : ∀ (v : ind_var_), v.is_free_in φ → val v = val' v) :
  holds D I val φ ↔ holds D I val' φ :=
begin
  induction φ generalizing val val',
  case formula.pred_ : P xs val val' h1
  {
    unfold ind_var_.is_free_in at h1,
    simp only [list.mem_to_finset] at h1,
    squeeze_simp at h1,

    unfold holds,
    congr' 2,
    simp only [list.map_eq_map_iff],
    exact h1,
  },
  case formula.not_ : φ φ_ih val val' h1
  {
    apply not_congr,
    exact φ_ih val val' h1,
  },
  case formula.imp_ : φ ψ φ_ih ψ_ih val val' h1
  {
    unfold ind_var_.is_free_in at h1,
    squeeze_simp at h1,

    apply imp_congr,
    {
      apply φ_ih val val',
      intros x a1,
      apply h1,
      left,
      exact a1,
    },
    {
      apply ψ_ih val val',
      intros x a1,
      apply h1,
      right,
      exact a1,
    }
  },
  case formula.forall_ : x φ φ_ih val val' h1
  {
    unfold ind_var_.is_free_in at h1,
    squeeze_simp at h1,

    unfold holds,
    apply forall_congr,
    intros d,
    apply φ_ih,
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
  (val : valuation D)
  (φ : formula)
  (h1 : ∀ (P : pred_var_), P.occurs_in φ → I.pred P = I'.pred P) :
  holds D I val φ ↔ holds D I' val φ :=
begin
  induction φ generalizing val,
  case formula.pred_ : P xs val
  {
    unfold pred_var_.occurs_in at h1,
    squeeze_simp at h1,

    unfold holds,
    induction h1,
    refl,
  },
  case formula.not_ : φ φ_ih val
  {
    unfold pred_var_.occurs_in at h1,

    unfold holds,
    apply not_congr,
    apply φ_ih h1,
  },
  case formula.imp_ : φ ψ φ_ih ψ_ih val
  {
    unfold pred_var_.occurs_in at h1,
    squeeze_simp at h1,

    unfold holds,
    apply imp_congr,
    {
      apply φ_ih,
      intros P a1,
      apply h1,
      left,
      exact a1,
    },
    {
      apply ψ_ih,
      intros P a1,
      apply h1,
      right,
      exact a1,
    }
  },
  case formula.forall_ : x φ φ_ih val
  {
    unfold pred_var_.occurs_in at h1,

    unfold holds,
    apply forall_congr,
    intros a,
    apply φ_ih h1,
  },
end


theorem coincidence_theorem
  {D : Type}
  (I I' : interpretation D)
  (val val' : valuation D)
  (φ : formula)
  (h1 : coincide I I' val val' φ) :
  holds D I val φ ↔ holds D I' val' φ :=
begin
  unfold coincide at h1,
  cases h1,

  transitivity holds D I val' φ,
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
  (v t : ind_var_)
  (binders : finset ind_var_)
  (P : formula)
  (h1 : fast_admits_aux v t binders P)
  (h2 : ∀ (v : ind_var_), ¬ v ∈ binders → val' v = val v) :
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
    simp only [list.map_map],
    simp only [list.map_eq_map_iff],
    intros x a1,
    simp only [function.comp_app],
    unfold function.update_ite,
    split_ifs,
    apply h2,
    apply h1,
    subst h,
    exact a1,
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
  (v t : ind_var_)
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
  (v t : ind_var_)
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
  (v t : ind_var_)
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
    simp only [list.map_map],
    simp only [list.map_eq_map_iff],
    intros x a1,
    unfold function.update_ite,
    simp only [function.comp_app],
    split_ifs;
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
    unfold ind_var_.is_free_in at h1_1,
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
    unfold ind_var_.is_free_in at h1_1,
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


example
  (D : Type)
  (I : interpretation D)
  (V : valuation D)
  (P Q : formula)
  (zs ts : list ind_var_)
  (h1 : zs.nodup)
  (h2 : ∀ (z : ind_var_), z ∈ zs → ¬ z ∈ ts)
  (h3 : is_free_sub_chain P zs ts Q) :
  holds D I (function.update_list_ite V zs (ts.map V)) P ↔
  holds D I V Q :=
begin
  sorry,
end


lemma substitution_theorem_fun_aux
  {D : Type}
  (I : interpretation D)
  (val val' : valuation D)
  (σ σ' : ind_var_ → ind_var_)
  (binders : finset ind_var_)
  (P : formula)
  (h1 : admits_fun_aux σ binders P)

  (h2 : ∀ (x : ind_var_), x ∈ binders ∨ σ' x ∉ binders → (val x = val' (σ' x)))
  (h2' : ∀ (x : ind_var_), x ∈ binders → σ' x = x)

  (h3 : ∀ (x : ind_var_), x ∉ binders -> σ' x = σ x) :
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
    simp only [list.map_map],
    congr' 2,
    simp only [list.map_eq_map_iff],
    intros v a1,
    simp only [function.comp_app],
    apply h2,
    by_cases c1 : v ∈ binders,
    left,
    exact c1,
    right,
    specialize h1 v a1 c1,
    specialize h3 v c1,
    rewrite h3,
    exact h1,
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
  (σ : ind_var_ → ind_var_)
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
  (σ : ind_var_ → ind_var_)
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
  (P : pred_var_)
  (zs : list ind_var_)
  (H : formula)
  (B : formula)
  (h1 : is_pred_sub A P zs H B)
  (h2 : ∀ (Q : pred_var_) (ds : list D), ¬ P = Q → (I.pred Q ds ↔ J.pred Q ds))
  (h3 : ∀ (ds : list D), J.pred P ds ↔ holds D I (function.update_list_ite V zs ds) H) :
  holds D I V B ↔ holds D J V A :=
begin
  induction h1 generalizing V,
  case is_pred_sub.pred_not_occurs_in : h1_Q h1_ts h1_P h1_zs h1_H h1_1
  {
    apply coincidence_theorem,
    unfold coincide,
    split,
    {
      unfold pred_var_.occurs_in,
      intros Q a1,
      funext ds,
      squeeze_simp,
      apply h2,
      squeeze_simp at a1,
      subst a1,
      exact h1_1,
    },
    {
      squeeze_simp,
    }
  },
  case is_pred_sub.pred_occurs_in : h1_P h1_ts h1_zs h1_H h1_B h1_1 h1_2 V h3
  {
    obtain s1 := substitution_theorem_fun I V (function.update_list_ite id h1_zs h1_ts) h1_H h1_1,
    rewrite h1_2 at s1,

    have s2 : (V ∘ function.update_list_ite id h1_zs h1_ts) = ( function.update_list_ite (V ∘ id) h1_zs (h1_ts.map V)),
    {
      clear h1_1, clear h1_2, clear h2, clear h3, clear s1,
      funext,
      squeeze_simp,
      induction h1_zs generalizing h1_ts,
      unfold function.update_list_ite,
      squeeze_simp,
      cases h1_ts,
      squeeze_simp,
      unfold function.update_list_ite,
      squeeze_simp,
      unfold function.update_list_ite,
      squeeze_simp,
      unfold function.update_ite,
      split_ifs,
      unfold function.update_list_ite,
      unfold function.update_ite,
      split_ifs,
      refl,
      unfold function.update_list_ite,
      unfold function.update_ite,
      split_ifs,
      apply h1_zs_ih,
    },
    rewrite s2 at s1,
    clear s2,
    squeeze_simp at s1,
    specialize h3 (list.map V h1_ts),
    rewrite <- h3 at s1,
    clear h3,
    rewrite <- s1,
    unfold holds,
  },
  case is_pred_sub.not_ : h1_A h1_P h1_zs h1_H h1_B h1_1 h1_ih
  {
    unfold holds,
    apply not_congr,
    apply h1_ih,
    exact h2,
    exact h3,
  },
  case is_pred_sub.imp_ : h1_A1 h1_A2 h1_P h1_zs h1_H h1_B1 h1_B2 h1_1 h1_2 h1_ih_1 h1_ih_2
  {
    unfold holds,
    apply imp_congr,
    apply h1_ih_1,
    exact h2,
    exact h3,
    apply h1_ih_2,
    exact h2,
    exact h3,
  },
  case is_pred_sub.forall_not_occurs_in : h1_x h1_A h1_P h1_zs h1_H h1_B h1_1
  {
    unfold pred_var_.occurs_in at h1_1,
    apply coincidence_theorem,
    unfold coincide,
    split,
    {
      unfold pred_var_.occurs_in,
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
  case is_pred_sub.forall_occurs_in : h1_x h1_A h1_P h1_zs h1_H h1_B h1_1 h1_2 h1_3 h1_ih
  {
    have s1 : ∀ (d : D) (ds : list D), holds D I (function.update_list_ite (function.update_ite V h1_x d) h1_zs ds) h1_H ↔ holds D I (function.update_list_ite V h1_zs ds) h1_H,
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
        induction h1_zs generalizing ds,
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
            apply h1_zs_ih,
          }
        }
      },
    },

    unfold holds,
    apply forall_congr,
    intros d,
    apply h1_ih,
    exact h2,
    intros ds,
    rewrite h3 ds,
    symmetry,
    exact s1 d ds,
  },
end


example
  (A : formula)
  (P : pred_var_)
  (zs : list ind_var_)
  (H : formula)
  (B : formula)
  (h1 : is_pred_sub A P zs H B)
  (h2 : A.is_valid) :
  B.is_valid :=
begin
  unfold formula.is_valid at h2,

  unfold formula.is_valid,
  intros D I V,

  let J : interpretation D := {
    nonempty := I.nonempty,
    pred := fun (R : pred_var_) (ds : list D), ite (¬ P = R) (I.pred R ds) (holds D I (function.update_list_ite V zs ds) H)
  },


  have s2 : (∀ (Q : pred_var_) (ds : list D), (¬(P = Q)) → (I.pred Q ds ↔ J.pred Q ds)),
  {
    squeeze_simp,
    intros Q ds a1,
    split,
    split_ifs,
    tauto,
    split_ifs,
    tauto,
  },

  have s3 : (∀ (ds : list D), (J.pred P ds ↔ holds D I (function.update_list_ite V zs ds) H)),
  {
    squeeze_simp,
  },

  obtain s1 := pred_sub_aux D I J V A P zs H B h1 s2 s3,

  cases s1,
  apply s1_mpr,
  apply h2,
end
