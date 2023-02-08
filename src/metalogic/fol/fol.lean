import data.finset logic.function.basic


set_option pp.parens true


abbreviation var_name := string
abbreviation func_name := string
abbreviation pred_name := string


inductive term : Type
| var : var_name → term
| func (n : ℕ) : func_name → (fin n → term) → term

open term


inductive formula : Type
| pred (n : ℕ) : pred_name → (fin n → term) → formula
| not : formula → formula
| imp : formula → formula → formula
| forall_ : var_name → formula → formula

open formula


structure interpretation (D : Type) : Type :=
(nonempty : nonempty D)
(func (n : ℕ) : func_name → ((fin n → D) → D))
(pred (n : ℕ) : pred_name → ((fin n → D) → Prop))


def valuation (D : Type) : Type := var_name → D

def eval_term (D : Type) (M : interpretation D) (V : valuation D) : term → D
| (var x) := V x
| (func n f ts) := M.func n f (fun (i : fin n), eval_term (ts i))


def holds (D : Type) (M : interpretation D) : valuation D → formula → Prop
| V (pred n P ts) := M.pred n P (fun (i : fin n), eval_term D M V (ts i))
| V (not φ) := ¬ holds V φ
| V (imp φ ψ) := holds V φ → holds V ψ
| V (forall_ x φ) := ∀ (a : D), holds (function.update V x a) φ


def is_valid (φ : formula) : Prop :=
  ∀ (D : Type),
	∀ (M : interpretation D),
	∀ (V : valuation D),
	holds D M V φ


/-
From "First Order Mathematical Logic" by Angelo Margaris:

An occurrence of a variable $v$ in a formula $P$ is bound if and only if
it occurs in a subformula of $P$ of the form $\forall v Q$. An occurrence
of $v$ in $P$ is free if and only if it is not a bound occurrence. The
variable $v$ is free or bound in $P$ according as it has a free or bound
occurrence in $P$.

If $P$ is a formula, $v$ is a variable, and $t$ is a term, then $P(t/v)$ is
the result of replacing each free occurrence of $v$ in $P$ by an occurrence
of $t$.

If $v$ and $u$ are variables and $P$ is a formula, then $P$ admits $u$ for $v$
if and only if there is no free occurrence of $v$ in $P$ that becomes a
bound occurrence of $u$ in $P(u/v)$. If $t$ is a term, then $P$ admits $t$ for
$v$ if and only if $P$ admits for $v$ every variable in $t$.
-/


/-
sub_term v t t' = t'(t/v)
The result of replacing each occurrence of the
variable named v in the term t' by the term t.
-/
def sub_term (v : var_name) (t : term) : term → term
| (var x) := if x = v then t else var x
| (func n f ts) := func n f (fun (i : fin n), sub_term (ts i))


/-
sub_formula v t P = P(t/v)
The result of replacing each free occurrence of the variable named v in the
formula P by an occurrence of the term t.
-/
def sub_formula (v : var_name) (t : term) : formula → formula
| (pred n P ts) := pred n P (fun (i : fin n), sub_term v t (ts i))
| (not φ) := not (sub_formula φ)
| (imp φ ψ) := imp (sub_formula φ) (sub_formula ψ)
| (forall_ x φ) := if x = v then forall_ x φ else forall_ x (sub_formula φ)


def term.all_var_set : term → finset var_name
| (var x) := {x}
| (func n _ ts) := finset.univ.bUnion (fun (i : fin n), (ts i).all_var_set)

/-
admits_var_aux v u ∅ P = P admits u for v
There is no free occurrence of the variable named v in the formula P that
becomes a bound occurrence of the variable named u in p(u/v).
-/
def admits_var_aux (v u : var_name) : formula → finset var_name → Prop
| (pred n P ts) binders :=
    v ∉ finset.univ.bUnion (fun (i : fin n), (ts i).all_var_set) ∨
    v ∈ binders ∨
    u ∉ binders
| (not φ) binders := admits_var_aux φ binders
| (imp φ ψ) binders := admits_var_aux φ binders ∧ admits_var_aux ψ binders
| (forall_ x φ) binders := admits_var_aux φ (binders ∪ {x})

/-
admits_term v t P = P admits t for v
P admits for v every variable in t.
-/
def admits_term (v : var_name) (t : term) (φ : formula) : Prop :=
∀ u ∈ t.all_var_set, admits_var_aux v u φ ∅


def formula.free_var_set : formula → finset var_name
| (pred n _ ts) := finset.univ.bUnion (fun (i : fin n), (ts i).all_var_set)
| (not φ) := φ.free_var_set
| (imp φ ψ) := φ.free_var_set ∪ ψ.free_var_set
| (forall_ x φ) := φ.free_var_set \ {x}


theorem thm_1
  (D : Type)
  (M : interpretation D)
  (V1 V2 : valuation D)
  (t : term)
  (h1 : ∀ x ∈ t.all_var_set, V1 x = V2 x) :
  eval_term D M V1 t = eval_term D M V2 t :=
begin
  induction t,
  case term.var : x {
    unfold term.all_var_set at h1,
    simp only [finset.mem_singleton, forall_eq] at h1,
    unfold eval_term,
    exact h1
  },
  case term.func : n f ts ih {
    unfold term.all_var_set at h1,
    simp only [finset.mem_bUnion, finset.mem_univ, exists_true_left, forall_exists_index] at h1,

    simp only at ih,
    unfold eval_term,
    congr, funext,

    apply ih i,
    intros x h2,
    exact h1 x i h2,
	}
end


theorem thm_2
  (D : Type)
  (M : interpretation D)
  (V1 V2 : valuation D)
  (φ : formula)
  (h1 : ∀ x ∈ φ.free_var_set, V1 x = V2 x) :
  holds D M V1 φ ↔ holds D M V2 φ :=
begin
  induction φ generalizing V1 V2,
  case formula.pred : n P ts {
    unfold formula.free_var_set at h1,
    simp only [finset.mem_bUnion, finset.mem_univ, exists_true_left, forall_exists_index] at h1,

    unfold holds,
    apply iff_of_eq,
    congr, funext,
    apply thm_1,
    intros x h2,
    exact h1 x i h2
  },
  case formula.not : φ ih {
    unfold formula.free_var_set at h1,
    unfold holds,
    apply iff.not,
    exact ih V1 V2 h1
  },
  case formula.imp : φ ψ ih_φ ih_ψ {
    unfold formula.free_var_set at h1,
    simp only [finset.mem_union, or_imp_distrib, forall_and_distrib] at h1,
    cases h1,

    unfold holds,
    apply iff.imp,
    exact ih_φ V1 V2 h1_left,
    exact ih_ψ V1 V2 h1_right
  },
  case formula.forall_ : x φ ih {
    unfold formula.free_var_set at h1,
    simp only [finset.mem_sdiff, finset.mem_singleton, and_imp] at h1,

    unfold holds,
    apply forall_congr,
    intros a,
    apply ih,
    intros y h2,
    by_cases y = x,
    {
      rewrite h,
      simp only [function.update_same]
    },
    {
      simp only [function.update_noteq h],
      exact h1 y h2 h
    },
  }
end


theorem thm_4
  (v : var_name)
  (t t' : term) :
  (sub_term v t t').all_var_set =
    t'.all_var_set.bUnion (fun (y : var_name), (function.update var v t y).all_var_set) :=
begin
  induction t',
  case term.var : x
  {
    unfold sub_term,
    unfold term.all_var_set,
    unfold function.update,
    simp only [eq_rec_constant, dite_eq_ite, finset.singleton_bUnion]
  },
  case term.func : n f ts ih
  {
    simp only at ih,

    unfold sub_term,
    unfold term.all_var_set,
    simp only [finset.bUnion_bUnion],
    congr, funext,
    exact ih i
  },
end


theorem thm_5
  (D : Type)
  (M : interpretation D)
  (V : valuation D)
  (v : var_name)
  (t t' : term) :
  eval_term D M V (sub_term v t t') =
    eval_term D M ((eval_term D M V) ∘ (function.update var v t)) t' :=
begin
  induction t',
  case term.var : x
  {
    unfold sub_term,
    unfold function.comp,
    unfold eval_term,
    unfold function.update,
    simp only [eq_rec_constant, dite_eq_ite]
  },
  case term.func : n f ts ih
  {
    simp only at ih,

    unfold sub_term,
    unfold eval_term,
    congr, funext,
    exact ih i
  },
end


theorem thm_6
  (v : var_name)
  (t : term)
  (φ : formula)
  (x : var_name)
  (h1 : admits_term v t φ)
  (h2 : ∀ (v0 : var_name), ∀ (t0 : term), (sub_formula v0 t0 φ).free_var_set = 
    φ.free_var_set.bUnion (fun (y : var_name), (function.update var v0 t0 y).all_var_set)) :
  x ∉ (φ.free_var_set \ {x}).bUnion (fun (y : var_name), (function.update var v t y).all_var_set) :=
begin
  unfold admits_term at h1,

  squeeze_simp at *,
  intros y h3 h4,
  intro contra,
  apply h4,
  sorry,
end


theorem thm_7
  (v : var_name)
  (t : term)
  (φ : formula) :
  (sub_formula v t φ).free_var_set =
    φ.free_var_set.bUnion (fun (y : var_name), (function.update var v t y).all_var_set) :=
begin
  induction φ,
  case formula.pred : n P ts
  {
    unfold sub_formula,
    unfold formula.free_var_set,
    simp only [thm_4],
    apply finset.ext, intros a,
    simp only [finset.mem_bUnion, finset.mem_univ, exists_prop, exists_true_left],
    split,
    {
      intros h1, apply exists.elim h1, intros a2 h2,
      apply exists.elim h2, intros a3 h3, cases h3,
      apply exists.intro a3, split,
      apply exists.intro a2, exact h3_left, exact h3_right
    },
    {
      intro h1, apply exists.elim h1, intros a2 h2, cases h2,
      apply exists.elim h2_left, intros a3 h3, apply exists.intro a3,
      apply exists.intro a2, exact and.intro h3 h2_right
    }
  },
  case formula.not : φ ih
  {
    unfold sub_formula,
    unfold formula.free_var_set,
    exact ih
  },
  case formula.imp : φ ψ φ_ih ψ_ih
  {
    unfold sub_formula,
    unfold formula.free_var_set,
    rewrite φ_ih, rewrite ψ_ih,
    apply finset.ext, intro a,
    simp only [or_and_distrib_right, exists_or_distrib, finset.mem_bUnion,
    finset.mem_union, exists_prop]
  },
  case formula.forall_ : x φ ih
  {
    unfold sub_formula,
    split_ifs,
    unfold formula.free_var_set, sorry,
    sorry
  },
end


theorem thm_8
  (D : Type)
  (M : interpretation D)
  (V : valuation D)
  (v : var_name)
  (t : term)
  (φ : formula) :
  holds D M V (sub_formula v t φ) ↔
    holds D M ((eval_term D M V) ∘ (function.update var v t)) φ :=
begin
  induction φ,
  case formula.pred : n P ts
  {
    unfold sub_formula,
    unfold holds,
    simp only [thm_5]
  },
  case formula.not : φ ih
  {
    unfold sub_formula,
    unfold holds,
    exact iff.not ih
  },
  case formula.imp : φ ψ φ_ih ψ_ih
  {
    unfold sub_formula,
    unfold holds,
    exact iff.imp φ_ih ψ_ih
  },
  case formula.forall_ : x φ ih
  {
    unfold sub_formula,
    split_ifs,
    {
      rewrite h,
      unfold holds,
      apply forall_congr,
      intros a,
      sorry
    },
    {
      sorry
    }
  },
end


example
  (v : var_name)
  (t : term)
  (φ : formula)
  (h1 : admits_term v t φ)
  (h2 : is_valid φ) :
  is_valid (sub_formula v t φ) :=
begin
  unfold is_valid at h2,
  unfold is_valid,
  intros D M V,
  simp only [thm_8], apply h2
end
