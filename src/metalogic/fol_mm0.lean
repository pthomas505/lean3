import logic.function.basic
import tactic
import data.fin.vec_notation


set_option pp.parens true


def function.update_fin
	{α β : Type}
	[decidable_eq α]
	(σ : α → β) :
	Π (n : ℕ), (fin n → α) → (fin n → β) → (α → β)
| 0 _ _ x := σ x
| (n + 1) f g x :=
	if x = f n
	then g n
	else function.update_fin n (fun (i : fin n), f i) (fun (i : fin n), g i) x

#eval function.update_fin (fun (n : ℕ), n) 5 ![1, 5, 10, 11, 1] ![10, 8, 5, 8, 12] 0


lemma function.update_fin_noteq
	{α β : Type}
	[decidable_eq α]
	(σ : α → β)
	(n : ℕ)
	(xs : fin n → α)
	(ys : fin n → β)
	(x : α)
	(h1 : ∀ (i : fin n), ¬ x = xs i) :
	function.update_fin σ n xs ys x = σ x :=
begin
	induction n,
	case nat.zero
  {
		unfold function.update_fin
	},
  case nat.succ : n ih
  {
		unfold function.update_fin,
		have s1 : ¬ x = xs ↑n, apply h1,
		rewrite if_neg s1,
		apply ih,
		intros i,
		by_cases ↑i = ↑n,
		rewrite h, exact s1,
		exact h1 ↑i,
	},
end

def function.cast_fin
	{α : Type}
	[decidable_eq α]
	(m n : ℕ)
	(h : m = n)
	(f : fin m → α) :
	fin n → α := by {subst h, exact f}


abbreviation var_name := string
abbreviation meta_var_name := string
abbreviation def_name := string


inductive formula : Type
| meta_var : meta_var_name → formula
| not : formula → formula
| imp : formula → formula → formula
| eq_ : var_name → var_name → formula
| forall_ : var_name → formula → formula
| def_ (n : ℕ) : def_name → (fin n → var_name) → formula

open formula


def valuation (D : Type) : Type := var_name → D
def meta_valuation (D : Type) : Type := meta_var_name → valuation D → Prop

structure def_t : Type :=
(name : string)
(n : ℕ)
(args : fin n → var_name)
(nodup : function.injective args)
(q : formula)

@[derive has_append]
def env : Type := list def_t


/-
def holds (D : Type) : meta_valuation D → env → formula → valuation D → Prop
| M E (meta_var X) V := M X V
| M E (not φ) V := ¬ holds M E φ V
| M E (imp φ ψ) V := holds M E φ V → holds M E ψ V
| M E (eq_ x y) V := V x = V y
| M E (forall_ x φ) V := ∀ (a : D), holds M E φ (function.update V x a)
| M [] (def_ _ _ _) V := false
| M (d :: E) (def_ n name args) V := 
		if name = d.name ∧ n = d.n
		then holds M E d.q (function.update_fin V d.n n d.args (V ∘ args))
		else holds M E (def_ n name args) V
-/

/-
Lean is unable to determine that the above definition of holds is decreasing,
so it needs to be broken into this pair of mutually recursive definitions.
-/

def holds'
	(D : Type)
	(M : meta_valuation D)
	(holds : formula → valuation D → Prop)
	(d : option def_t) :
	formula → valuation D → Prop
| (meta_var X) V := M X V
| (not φ) V := ¬ holds' φ V
| (imp φ ψ) V := holds' φ V → holds' ψ V
| (eq_ x y) V := V x = V y
| (forall_ x φ) V := ∀ (a : D), holds' φ (function.update V x a)
| (def_ n name args) V :=
		option.elim false
			(fun d : def_t,
				if h : name = d.name ∧ n = d.n
				then holds d.q (function.update_fin V d.n d.args (V ∘ (function.cast_fin n d.n h.right args)))
				else holds (def_ n name args) V)
			d

def holds
	(D : Type)
	(M : meta_valuation D) :
	env → formula → valuation D → Prop
| [] := holds' D M (fun _ _, false) option.none
| (d :: E) := holds' D M (holds E) (option.some d)


/-
These lemmas demonstrate that the pair of mutually recursive definitions
is equivalent to the version the Lean is unable to determine is decreasing.
-/

@[simp]
lemma holds_meta_var
	(D : Type)
	(M : meta_valuation D)
	(E : env)
	(V : valuation D)
	(X : meta_var_name) :
	holds D M E (meta_var X) V ↔ M X V := by {cases E; refl}

@[simp]
lemma holds_not
	(D : Type)
	(M : meta_valuation D)
	(E : env)
	(V : valuation D)
	(φ : formula) :
	holds D M E (not φ) V ↔ ¬ holds D M E φ V := by {cases E; refl}

@[simp]
lemma holds_imp
	(D : Type)
	(M : meta_valuation D)
	(E : env)
	(V : valuation D)
	(φ ψ : formula) :
	holds D M E (imp φ ψ) V ↔ holds D M E φ V → holds D M E ψ V := by {cases E; refl}

@[simp]
lemma holds_eq_
	(D : Type)
	(M : meta_valuation D)
	(E : env)
	(V : valuation D)
	(x y : var_name) :
	holds D M E (eq_ x y) V ↔ V x = V y := by {cases E; refl}

@[simp]
lemma holds_forall_
	(D : Type)
	(M : meta_valuation D)
	(E : env)
	(V : valuation D)
	(φ : formula)
	(x : var_name) :
	holds D M E (forall_ x φ) V ↔ ∀ (a : D), holds D M E φ (function.update V x a) := by {cases E; refl}

@[simp]
lemma holds_nil_def
	(D : Type)
	(M : meta_valuation D)
	(V : valuation D)
	(n : ℕ)
	(name : def_name)
	(args : fin n → var_name) :
	holds D M [] (def_ n name args) V ↔ false := by {refl}

@[simp]
lemma holds_not_nil_def
	(D : Type)
	(M : meta_valuation D)
	(E : env)
	(V : valuation D)
	(n : ℕ)
	(name : def_name)
	(args : fin n → var_name)
	(d : def_t) :
	holds D M (d :: E) (def_ n name args) V ↔
		if h : name = d.name ∧ n = d.n
		then holds D M E d.q (function.update_fin V d.n d.args (V ∘ (function.cast_fin n d.n h.right args)))
		else holds D M E (def_ n name args) V := by {refl}


/-
A substitution mapping.
A mapping of each variable name to another name.
-/
def instantiation :=
	{σ : var_name → var_name // ∃ (σ' : var_name → var_name), σ ∘ σ' = id ∧ σ' ∘ σ = id}

/-
A meta substitution mapping.
A mapping of each meta variable name to a formula.
-/
def meta_instantiation : Type := meta_var_name → formula

def formula.subst (σ : instantiation) (τ : meta_instantiation) : formula → formula
| (meta_var X) := τ X
| (not φ) := not φ.subst
| (imp φ ψ) := imp φ.subst ψ.subst
| (eq_ x y) := eq_ (σ.1 x) (σ.1 y)
| (forall_ x φ) := forall_ (σ.1 x) φ.subst
| (def_ n name args) := def_ n name (fun (i : fin n), σ.1 (args i))


lemma lem_1
	{α β : Type}
	[decidable_eq α]
	(f f' : α → α)
  (x : α)
  (h1 : (f' ∘ f) = id)
  (g : α → β)
  (a : β) :
  function.update (g ∘ f) x a = (function.update g (f x) a) ∘ f :=
begin
		apply funext, intros x',
		unfold function.comp,
		unfold function.update,
		simp only [eq_rec_constant, dite_eq_ite],
		apply if_congr,
		split,
		apply congr_arg,
		apply function.left_inverse.injective,
		exact congr_fun h1,
		refl, refl,
end


lemma lem_2
	{α β : Type}
	[decidable_eq α]
  (f f' : α → α)
	(x : α)
  (h1 : f' ∘ f = id)
  (h2 : f ∘ f' = id)
  (g : α → β)
  (a : β) :
  function.update (g ∘ f) (f' x) a = (function.update g x a) ∘ f :=
begin
	apply funext, intros x',
	unfold function.comp,
	unfold function.update,
	simp only [eq_rec_constant, dite_eq_ite],
	congr' 1, simp only [eq_iff_iff],
	split,
	intros h3, rewrite h3, rewrite <- function.comp_app f f' x, rewrite h2, simp only [id.def],
	intros h3, rewrite <- h3, rewrite <- function.comp_app f' f x', rewrite h1, simp only [id.def],
end

lemma ext_env_holds
	{D : Type}
	(M : meta_valuation D)
	(E E' : env)
	(φ : formula)
	(V : valuation D)
	(h1 : ∃ E1, E' = E1 ++ E) :
	holds D M E' φ V ↔ holds D M E φ V := sorry


lemma lem_3
	{D : Type}
	(V : valuation D)
	(M : meta_valuation D)
	(E E' : env)
	(σ : instantiation)
	(σ' : var_name → var_name)
	(τ : meta_instantiation)
	(h1 : σ.1 ∘ σ' = id)
	(h2 : σ' ∘ σ.1 = id)
	(h3 : ∃ E1, E' = E1 ++ E)
	(φ : formula) :
	holds D
		(fun (X : meta_var_name) (V' : valuation D), holds D M E' (τ X) (V' ∘ σ')) E φ (V ∘ σ.1) ↔
	holds D M E (φ.subst σ τ) V :=
begin
	induction E generalizing φ V,
	case list.nil
  {
		induction φ generalizing V,
		case formula.meta_var : φ V
		{
			simp only [holds_meta_var],
			unfold formula.subst,
			rewrite function.comp.assoc V σ.1 σ',
			rewrite h1,
			rewrite function.comp.right_id V,
			apply ext_env_holds, exact h3,
		},
		case formula.not : φ ih V
		{
			simp only [holds_not] at *,
			unfold formula.subst,
			rewrite ih,
			simp only [holds_not],
		},
		case formula.imp : φ ψ φ_ih ψ_ih V
		{
			simp only [holds_imp] at *,
			unfold formula.subst,
			simp only [φ_ih, ψ_ih],
			simp only [holds_imp],
		},
		case formula.eq_ : x y V
		{
			simp only [holds_eq_] at *,
			unfold formula.subst,
			simp only [holds_eq_],
		},
		case formula.forall_ : x φ φ_ih V
		{
			simp only [holds_forall_],
			apply forall_congr, intros a,
			rewrite lem_1 σ.1 σ' x h2 V a,
			apply φ_ih,
		},
		case formula.def_ : n name args V
		{
			simp only [holds_nil_def],
			unfold formula.subst,
			simp only [holds_nil_def],
		},
	},
  case list.cons : E_hd E_tl E_ih
  {
		induction φ generalizing V,
		case formula.meta_var : φ V
		{
			simp only [holds_meta_var],
			unfold formula.subst,
			rewrite function.comp.assoc V σ.1 σ',
			rewrite h1,
			rewrite function.comp.right_id V,
			apply ext_env_holds, exact h3,
		},
		case formula.not : φ ih
		{
			simp only [holds_not] at *,
			unfold formula.subst at *,
			rewrite ih,
			simp only [holds_not],
		},
		case formula.imp : φ ψ φ_ih ψ_ih
		{
			simp only [holds_imp] at *,
			unfold formula.subst,
			rewrite φ_ih, rewrite ψ_ih,
			simp only [holds_imp],
		},
		case formula.eq_ : x y
		{
			simp only [holds_eq_] at *,
			unfold formula.subst,
			simp only [holds_eq_],
		},
		case formula.forall_ : x φ φ_ih
		{
			simp only [holds_forall_],
			unfold formula.subst at *,
			simp only [holds_forall_],
			apply forall_congr, intros a,
			rewrite lem_1 σ.1 σ' x h2 V a,
			apply φ_ih,
		},
		case formula.def_ : n name args
		{
			have s1 : ∃ (E1 : env), E' = E1 ++ E_tl,
			apply exists.elim h3, intros a h4,
			apply exists.intro (a ++ [E_hd]),
			simp only [list.append_assoc, list.singleton_append],
			exact h4,

			simp only [holds_not_nil_def] at *,
			unfold formula.subst at *,
			simp only [holds_not_nil_def] at *,
			split_ifs,
			{
				specialize E_ih s1 E_hd.q,
				sorry,
			},
			{
				rewrite E_ih,
				unfold formula.subst,
				exact s1,
			}
		},
	},
end


-- changing v does not cause the value of φ to change

def is_not_free (D : Type) (M : meta_valuation D) (E : env) (v : var_name) (φ : formula) : Prop :=
	∀ (V : valuation D) (a : D),
	holds D M E φ V ↔ holds D M E φ (function.update V v a)

lemma lem_4
	{α β : Type}
	[decidable_eq α]
  (f g : α → β)
	(x : α)
  (h1 : ∀ (y : α), y ≠ x → f y = g y) :
  function.update f x (g x) = g :=
begin
  apply funext, intros a,
	unfold function.update,
	simp only [eq_rec_constant, dite_eq_ite],
	split_ifs,
	rewrite h,
	exact h1 a h,
end

theorem is_not_free_equiv
	{D : Type}
	(M : meta_valuation D)
	(E : env)
	(v : var_name)
	(φ : formula) :
	is_not_free D M E v φ ↔
		∀ (V V' : valuation D),
			(∀ (y : var_name), (y ≠ v → (V y = V' y))) →
				(holds D M E φ V ↔ holds D M E φ V') :=
begin
	unfold is_not_free,
	split,
	{
		intros h1 V V' h2,
		rewrite <- lem_4 V V' v h2,
		apply h1,
	},
	{
		intros h1 V a,
		apply h1,
		intros a' h2,
		simp only [function.update_noteq h2],
	}
end


def not_free (Γ : list (var_name × meta_var_name)) (v : var_name) : formula → Prop
| (meta_var X) := (v, X) ∈ Γ
| (not φ) := not_free φ
| (imp φ ψ) := not_free φ ∧ not_free ψ
| (eq_ x y) := x ≠ v ∧ y ≠ v
| (forall_ x φ) := x = v ∨ not_free φ
| (def_ n name args) := ∀ (i : fin n), ¬ args i = v


lemma not_free_imp_is_not_free
	{D : Type}
	(M : meta_valuation D)
	(E : env)
	(Γ : list (var_name × meta_var_name))
	(v : var_name)
	(φ : formula)
	(H : not_free Γ v φ)
	(nf : ∀ X, (v, X) ∈ Γ → is_not_free D M E v (meta_var X)) :
	is_not_free D M E v φ :=
begin
	induction φ,
	case formula.meta_var : X
  {
		unfold not_free at H,
		exact nf X H,
	},
  case formula.not : φ φ_ih
  {
		unfold not_free at *,
		unfold is_not_free at *,
		simp only [holds_not],
		intros V a,
		apply not_congr,
		exact φ_ih H V a,
	},
  case formula.imp : φ ψ φ_ih ψ_ih
  {
		unfold not_free at *,
		unfold is_not_free at *,
		simp only [holds_imp],
		cases H,
		intros V a,
		apply imp_congr,
		exact φ_ih H_left V a,
		exact ψ_ih H_right V a,
	},
  case formula.eq_ : x y
  {
		unfold not_free at H,
		unfold is_not_free at *,
		simp only [holds_eq_],
		cases H,
		intros V a,
		simp only [function.update_noteq H_left, function.update_noteq H_right],
	},
  case formula.forall_ : x φ φ_ih
  {
		unfold is_not_free at *,
		unfold not_free at *,
		simp only [holds_forall_],
		intros V a,
		apply forall_congr, intros a',
		cases H,
		{
			rewrite H,
			simp only [function.update_idem],
		},
		{
			by_cases v = x,
			{
				rewrite h,
				simp only [function.update_idem],
			},
			{
				simp only [function.update_comm h],
				apply φ_ih H,
			}
		}
	},
	case formula.def_ : n name args
  {
		unfold is_not_free at *,
		unfold not_free at *,
		induction E,
		case list.nil
		{
			simp only [holds_nil_def, iff_self, forall_2_true_iff],
		},
		case list.cons : hd tl ih
		{
			intros V a,
			simp only [holds_not_nil_def, ne.def, holds_meta_var] at *,
			specialize ih nf V a,
			split_ifs,
			{
				rewrite iff_eq_eq, congr' 1,
				funext,
				rewrite [function.update_fin_noteq, function.update_fin_noteq],
				sorry, sorry, sorry,
			},
			{
				exact ih,
			}
		},
	}
end


lemma lem_5
	{D : Type}
	(M : meta_valuation D)
	(E : env)
	(Γ Γ' : list (var_name × meta_var_name))
	(σ : instantiation)
	(σ' : var_name → var_name)
  (τ : meta_instantiation)
  (left : ((σ.1 ∘ σ') = id))
  (right : ((σ' ∘ σ.1) = id))
  (nf : ∀ (v : var_name) (X : meta_var_name), ((v, X) ∈ Γ') → is_not_free D M E v (meta_var X))
  (H : ∀ (v : var_name) (X : meta_var_name), ((v, X) ∈ Γ) → not_free Γ' (σ.1 v) (τ X)) :
  ∀ (v : var_name) (X : meta_var_name),
		((v, X) ∈ Γ) →
			is_not_free D (fun (X : meta_var_name) (V' : valuation D), holds D M E (τ X) (V' ∘ σ'))
				E v (meta_var X) :=
begin
	intros v X h1,
	unfold is_not_free,
	simp only [holds_meta_var],
	intros V a,
	rewrite <- lem_2 σ' σ.1 v left right,
	apply not_free_imp_is_not_free M E Γ',
	exact H v X h1,
	intros X' h2,
	exact nf (σ.1 v) X' h2,
end


def exists_ (x : var_name) (φ : formula) : formula := not (forall_ x (not φ))


-- if (v, X) ∈ Γ then v is not free in (meta_var X)
inductive is_proof : list (var_name × meta_var_name) → list formula → formula → Prop
| hyp (Γ : list (var_name × meta_var_name)) (Δ : list formula)
	{φ : formula} :
	φ ∈ Δ → is_proof Γ Δ φ

| mp (Γ : list (var_name × meta_var_name)) (Δ : list formula)
	{φ ψ : formula} :
	is_proof Γ Δ φ → is_proof Γ Δ (φ.imp ψ) → is_proof Γ Δ ψ

| prop_1 (Γ : list (var_name × meta_var_name)) (Δ : list formula)
	{φ ψ : formula} :
	is_proof Γ Δ (φ.imp (ψ.imp φ))

| prop_2 (Γ : list (var_name × meta_var_name)) (Δ : list formula)
	{φ ψ χ : formula} :
	is_proof Γ Δ ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))

| prop_3 (Γ : list (var_name × meta_var_name)) (Δ : list formula)
	{φ ψ : formula} :
	is_proof Γ Δ (((not φ).imp (not ψ)).imp (ψ.imp φ))

| gen (Γ : list (var_name × meta_var_name)) (Δ : list formula)
	{φ : formula} {x : var_name} :
	is_proof Γ Δ φ → is_proof Γ Δ (forall_ x φ)

| pred_1 (Γ : list (var_name × meta_var_name)) (Δ : list formula)
	{φ ψ : formula} {x : var_name} :
	is_proof Γ Δ ((forall_ x (φ.imp ψ)).imp ((forall_ x φ).imp (forall_ x ψ)))

| pred_2 (Γ : list (var_name × meta_var_name)) (Δ : list formula)
	{φ : formula} {x : var_name} :
	not_free Γ x φ → is_proof Γ Δ (φ.imp (forall_ x φ))

| eq_1 (Γ : list (var_name × meta_var_name)) (Δ : list formula)
	{x y : var_name} :
	x ≠ y → is_proof Γ Δ (exists_ x (eq_ x y))

| eq_2 (Γ : list (var_name × meta_var_name)) (Δ : list formula)
	{x y z : var_name} :
	is_proof Γ Δ ((eq_ x y).imp ((eq_ x z).imp (eq_ y z)))

| thm (Γ Γ' : list (var_name × meta_var_name)) (Δ Δ' : list formula)
	{φ : formula} {σ : instantiation} {τ : meta_instantiation} :
	is_proof Γ Δ φ →
	(∀ (x : var_name) (X : meta_var_name), (x, X) ∈ Γ → not_free Γ' (σ.1 x) (τ X)) →
	(∀ (ψ : formula), ψ ∈ Δ → is_proof Γ' Δ' (ψ.subst σ τ)) →
	is_proof Γ' Δ' (φ.subst σ τ)


example
	(D : Type)
	(M : meta_valuation D)
	(E : env)
	(Γ : list (var_name × meta_var_name))
	(Δ : list formula)
	(φ : formula)
	(H : is_proof Γ Δ φ)
	(nf : ∀ v X, (v, X) ∈ Γ → is_not_free D M E v (meta_var X))
	(hyp : ∀ (φ ∈ Δ) V, holds D M E φ V) :
	∀ (V : valuation D), holds D M E φ V :=
begin
	induction H generalizing M,
	case is_proof.hyp : H_Γ H_Δ H_φ H_ᾰ M nf hyp
  {
		exact hyp H_φ H_ᾰ,
	},
  case is_proof.mp : H_Γ H_Δ H_φ H_ψ H_ᾰ H_ᾰ_1 H_ih_ᾰ H_ih_ᾰ_1 M nf hyp
  {
		intros V,
		simp only [holds_imp] at *,
		apply H_ih_ᾰ_1 M nf hyp,
		apply H_ih_ᾰ M nf hyp,
	},
  case is_proof.prop_1 : H_Γ H_Δ H_φ H_ψ M nf hyp
  {
		simp only [holds_imp],
		intros V h1 h2, exact h1,
	},
  case is_proof.prop_2 : H_Γ H_Δ H_φ H_ψ H_χ M nf hyp
  {
		simp only [holds_imp],
		intros V h1 h2 h3,
		apply h1, exact h3, apply h2, exact h3,
	},
  case is_proof.prop_3 : H_Γ H_Δ H_φ H_ψ M nf hyp
  {
		simp only [holds_imp, holds_not],
		intros V h1 h2,
		by_contradiction,
		exact h1 h h2,
	},
  case is_proof.gen : H_Γ H_Δ H_φ H_x H_ᾰ H_ih M nf hyp
  {
		simp only [holds_forall_],
		intros V a,
		apply H_ih M nf hyp,
	},
  case is_proof.pred_1 : H_Γ H_Δ H_φ H_ψ H_x M nf hyp
  {
		simp only [holds_imp, holds_forall_],
		intros V h1 h2 a,
		apply h1,
		apply h2,
	},
  case is_proof.pred_2 : H_Γ H_Δ H_φ H_x H_ᾰ M nf hyp
  {
		have s1 : is_not_free D M E H_x H_φ,
		apply not_free_imp_is_not_free M E H_Γ H_x H_φ H_ᾰ,
		intros X h2, exact nf H_x X h2,

		simp only [holds_imp, holds_forall_],
		intros V h2 a,
		unfold is_not_free at s1,
		rewrite <- s1, exact h2,
	},
  case is_proof.eq_1 : H_Γ H_Δ H_x H_y H_ᾰ M nf hyp
  {
		unfold exists_,
		simp only [holds_not, holds_forall_, holds_eq_, not_forall],
		intros V,
		push_neg,
		simp only [function.update_same],
		apply exists.intro (V H_y),
		symmetry,
		apply function.update_noteq,
		symmetry, exact H_ᾰ,
	},
  case is_proof.eq_2 : H_Γ H_Δ H_x H_y H_z M nf hyp
  {
		simp only [holds_imp, holds_eq_],
		intros V h1 h2,
		transitivity V H_x,
		symmetry,
		exact h1,
		exact h2,
	},
  case is_proof.thm : H_Γ H_Γ' H_Δ H_Δ' H_φ H_σ H_τ H_ᾰ H_ᾰ_1 H_ᾰ_2 H_ih_ᾰ H_ih_ᾰ_1 M nf hyp
  {
		obtain ⟨σ', left, right⟩ := H_σ.2,
		intros V,
		rewrite <- lem_3 V M E sorry H_σ σ' H_τ left right,
		apply H_ih_ᾰ,
		intros v X h1,
		sorry,
		--exact lem_5 M E H_Γ H_Γ' H_σ σ' H_τ left right nf H_ᾰ_1 v X h1,
		intros φ h2 V',
		specialize H_ih_ᾰ_1 φ h2 M nf hyp (V' ∘ σ'),
		rewrite <- lem_3 (V' ∘ σ') M E sorry H_σ σ' H_τ left right sorry φ at H_ih_ᾰ_1,
		rewrite function.comp.assoc at H_ih_ᾰ_1,
		rewrite right at H_ih_ᾰ_1,
		simp only [function.comp.right_id] at H_ih_ᾰ_1,
		exact H_ih_ᾰ_1, sorry,
	},
end
