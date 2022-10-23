import logic.function.basic
import tactic


set_option pp.parens true


lemma aux_1
	{α β : Type}
	[decidable_eq α]
	(f f' : α → α)
  (x : α)
  (h1 : f' ∘ f = id)
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


lemma aux_2
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


lemma aux_3
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


def function.update_list
	{α β : Type}
	[decidable_eq α]
	(f : α → β) :
	list (α × β) → α → β
| [] := f
| (hd :: tl) := function.update (function.update_list tl) hd.fst hd.snd

#eval function.update_list (fun (n : ℕ), n) [(0,1), (3,2), (0,2)] 0


lemma function.update_comp
	{α β γ : Type}
	[decidable_eq α]
  (f : α → β)
	(x : α)
  (a : β)
	(g : β → γ) :
  g ∘ function.update f x a = function.update (g ∘ f) x (g a) :=
begin
	funext x',
	unfold function.comp,
	by_cases x' = x,
	{
		rewrite h,
		simp only [function.update_same],
	},
	{
		simp only [function.update_noteq h],
	}
end


lemma function.update_list_comp
	{α β γ : Type}
	[decidable_eq α]
	(f : α → β)
	(l : list (α × β))
	(g : β → γ) :
	g ∘ function.update_list f l =
		function.update_list (g ∘ f) (list.map (fun (i : α × β), (i.fst, g i.snd)) l) :=
begin
	induction l,
	case list.nil
  {
		unfold function.update_list,
		unfold list.map,
		unfold function.update_list,
	},
  case list.cons : hd tl ih
  {
		unfold function.update_list,
		unfold list.map,
		unfold function.update_list,
		rewrite function.update_comp,
		rewrite ih,
	},
end


lemma function.update_list_noteq
	{α β : Type}
	[decidable_eq α]
	(f : α → β)
	(l : list (α × β))
	(x : α)
	(h1 : ∀ (p : α × β), p ∈ l → ¬ x = p.fst) :
	function.update_list f l x = f x :=
begin
	induction l,
	case list.nil
  { unfold function.update_list, },
  case list.cons : hd tl ih
  {
		unfold function.update_list,
		have s1 : ¬ x = hd.fst,
		apply h1,
		simp only [list.mem_cons_iff, eq_self_iff_true, true_or],

		simp only [function.update_noteq s1],
		apply ih,
		intros p h2,
		apply h1,
		simp only [list.mem_cons_iff],
		apply or.intro_right,
		exact h2,
	},
end


lemma function.update_list_mem
	{α β : Type}
	[decidable_eq α]
	(f : α → β)
	(l : list (α × β))
	(x : α × β)
	(h1 : list.nodup (list.map prod.fst l))
	(h2 : x ∈ l) :
	function.update_list f l x.fst = x.snd :=
begin
	induction l,
	case list.nil
  {
		unfold function.update_list,
		simp only [list.not_mem_nil] at h2,
		contradiction,
	},
  case list.cons : hd tl ih
  {
		simp only [list.map, list.nodup_cons, list.mem_map, prod.exists, exists_and_distrib_right, exists_eq_right, not_exists] at h1,
		cases h1,

		unfold function.update_list,
		cases h2,
		{
			rewrite h2,
			simp only [function.update_same],
		},
		{
			have s1 : ¬ x.fst = hd.fst,
			by_contradiction contra,
			apply h1_left x.snd,
			rewrite <- contra,
			simp only [prod.mk.eta],
			exact h2,

			simp only [function.update_noteq s1],
			exact ih h1_right h2,
		}
	},
end


lemma list.nth_le_zip_eq
	{α β : Type}
  [decidable_eq α]
	(n : ℕ)
  (l : list α)
	(l' : list β)
  (h1 : n < l.length)
  (h2 : n < l'.length)
  (h3 : n < (l.zip l').length) :
  ((l.nth_le n h1, l'.nth_le n h2) = ((l.zip l').nth_le n h3)) :=
begin
	simp,
end

lemma blah
	{α β : Type}
  [decidable_eq α]
	(n : ℕ)
  (l : list α)
	(l' : list β)
  (h1 : (n < l.length))
  (h2 : (n < l'.length))
  (h3 : l.length = l'.length) :
  ((l.nth_le n h1, l'.nth_le n h2) ∈ l.zip l') :=
begin
  have h4 : n < (l.zip l').length,
	simp, split, exact h1, exact h2,
	have s1 : ((l.nth_le n h1, l'.nth_le n h2) = ((l.zip l').nth_le n h4)),
	apply list.nth_le_zip_eq,
	rewrite s1, apply list.nth_le_mem,
end

lemma function.update_list_zip
	{α β : Type}
	[decidable_eq α]
	(f : α → β)
	(l l' : list α)
	(n : ℕ)
	(h1 : n < l'.length)
	(h2 : n < (list.map f l).length)
	(h3 : l'.nodup)
	(h4 : l.length = l'.length) :
	(function.update_list f (l'.zip (list.map f l))) (l'.nth_le n h1) =
		(list.map f l).nth_le n h2 :=
begin
	apply function.update_list_mem f (l'.zip (list.map f l)) (l'.nth_le n h1, (list.map f l).nth_le n h2),
	rewrite list.map_fst_zip, exact h3,
	simp, rewrite h4,
	apply blah n l' (list.map f l) h1 h2, rewrite <- h4, simp,
end


-- Syntax


abbreviation var_name := string
abbreviation meta_var_name := string
abbreviation def_name := string


inductive formula : Type
| meta_var_ : meta_var_name → formula
| not_ : formula → formula
| imp_ : formula → formula → formula
| eq_ : var_name → var_name → formula
| forall_ : var_name → formula → formula
| def_ : def_name → list var_name → formula

open formula


-- If (v, X) ∈ Γ then v is not free in meta_var_ X.
def not_free (Γ : list (var_name × meta_var_name)) (v : var_name) : formula → Prop
| (meta_var_ X) := (v, X) ∈ Γ
| (not_ φ) := not_free φ
| (imp_ φ ψ) := not_free φ ∧ not_free ψ
| (eq_ x y) := x ≠ v ∧ y ≠ v
| (forall_ x φ) := x = v ∨ not_free φ
| (def_ name args) := ∀ (x : var_name), x ∈ args → ¬ x = v


-- φ.not_free S ↔ φ.free_var_set ⊆ S
def formula.not_free : formula → list var_name → Prop
| (meta_var_ X) S := false
| (not_ φ) S := φ.not_free S
| (imp_ φ ψ) S := φ.not_free S ∧ ψ.not_free S
| (eq_ x y) S := x ∈ S ∧ y ∈ S
| (forall_ x φ) S := φ.not_free (x :: S)
| (def_ name args) S := args ⊆ S


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
| (meta_var_ X) := τ X
| (not_ φ) := not_ φ.subst
| (imp_ φ ψ) := imp_ φ.subst ψ.subst
| (eq_ x y) := eq_ (σ.1 x) (σ.1 y)
| (forall_ x φ) := forall_ (σ.1 x) φ.subst
| (def_ name args) := def_ name (list.map σ.1 args)


structure definition_ : Type :=
(name : string)
(n : ℕ)
(args : list var_name)
(nodup : args.nodup)
(q : formula)
(nf : q.not_free args)


@[derive has_append]
def env : Type := list definition_


def exists_ (x : var_name) (φ : formula) : formula := not_ (forall_ x (not_ φ))


-- if (v, X) ∈ Γ then v is not_ free in (meta_var_ X)
inductive is_proof : list (var_name × meta_var_name) → list formula → formula → Prop
| hyp (Γ : list (var_name × meta_var_name)) (Δ : list formula)
	{φ : formula} :
	φ ∈ Δ → is_proof Γ Δ φ

| mp (Γ : list (var_name × meta_var_name)) (Δ : list formula)
	{φ ψ : formula} :
	is_proof Γ Δ φ → is_proof Γ Δ (φ.imp_ ψ) → is_proof Γ Δ ψ

| prop_1 (Γ : list (var_name × meta_var_name)) (Δ : list formula)
	{φ ψ : formula} :
	is_proof Γ Δ (φ.imp_ (ψ.imp_ φ))

| prop_2 (Γ : list (var_name × meta_var_name)) (Δ : list formula)
	{φ ψ χ : formula} :
	is_proof Γ Δ ((φ.imp_ (ψ.imp_ χ)).imp_ ((φ.imp_ ψ).imp_ (φ.imp_ χ)))

| prop_3 (Γ : list (var_name × meta_var_name)) (Δ : list formula)
	{φ ψ : formula} :
	is_proof Γ Δ (((not_ φ).imp_ (not_ ψ)).imp_ (ψ.imp_ φ))

| gen (Γ : list (var_name × meta_var_name)) (Δ : list formula)
	{φ : formula} {x : var_name} :
	is_proof Γ Δ φ → is_proof Γ Δ (forall_ x φ)

| pred_1 (Γ : list (var_name × meta_var_name)) (Δ : list formula)
	{φ ψ : formula} {x : var_name} :
	is_proof Γ Δ ((forall_ x (φ.imp_ ψ)).imp_ ((forall_ x φ).imp_ (forall_ x ψ)))

| pred_2 (Γ : list (var_name × meta_var_name)) (Δ : list formula)
	{φ : formula} {x : var_name} :
	not_free Γ x φ → is_proof Γ Δ (φ.imp_ (forall_ x φ))

| eq_1 (Γ : list (var_name × meta_var_name)) (Δ : list formula)
	{x y : var_name} :
	x ≠ y → is_proof Γ Δ (exists_ x (eq_ x y))

| eq_2 (Γ : list (var_name × meta_var_name)) (Δ : list formula)
	{x y z : var_name} :
	is_proof Γ Δ ((eq_ x y).imp_ ((eq_ x z).imp_ (eq_ y z)))

| thm (Γ Γ' : list (var_name × meta_var_name)) (Δ Δ' : list formula)
	{φ : formula} {σ : instantiation} {τ : meta_instantiation} :
	is_proof Γ Δ φ →
	(∀ (x : var_name) (X : meta_var_name), (x, X) ∈ Γ → not_free Γ' (σ.1 x) (τ X)) →
	(∀ (ψ : formula), ψ ∈ Δ → is_proof Γ' Δ' (ψ.subst σ τ)) →
	is_proof Γ' Δ' (φ.subst σ τ)


-- Semantics


def valuation (D : Type) : Type := var_name → D
def meta_valuation (D : Type) : Type := meta_var_name → valuation D → Prop

/-
def holds (D : Type) : meta_valuation D → env → formula → valuation D → Prop
| M E (meta_var_ X) V := M X V
| M E (not_ φ) V := ¬ holds M E φ V
| M E (imp_ φ ψ) V := holds M E φ V → holds M E ψ V
| M E (eq_ x y) V := V x = V y
| M E (forall_ x φ) V := ∀ (a : D), holds M E φ (function.update V x a)
| M [] (def_ _ _) V := false
| M (d :: E) (def_ name args) V :=
		if name = d.name ∧ args.length = d.args.length
		then holds M E d.q (function.update_list V (list.zip d.args (list.map V args)))
		else holds M E (def_ name args) V
-/

/-
Lean is unable to determine that the above definition of holds is decreasing,
so it needs to be broken into this pair of mutually recursive definitions.
-/

def holds'
	(D : Type)
	(M : meta_valuation D)
	(holds : formula → valuation D → Prop)
	(d : option definition_) :
	formula → valuation D → Prop
| (meta_var_ X) V := M X V
| (not_ φ) V := ¬ holds' φ V
| (imp_ φ ψ) V := holds' φ V → holds' ψ V
| (eq_ x y) V := V x = V y
| (forall_ x φ) V := ∀ (a : D), holds' φ (function.update V x a)
| (def_ name args) V :=
		option.elim
			false
			(
				fun d : definition_,
				if name = d.name ∧ args.length = d.args.length
				then holds d.q (function.update_list V (list.zip d.args (list.map V args)))
				else holds (def_ name args) V
			)
			d

def holds
	(D : Type)
	(M : meta_valuation D) :
	env → formula → valuation D → Prop
| [] := holds' D M (fun _ _, false) option.none
| (d :: E) := holds' D M (holds E) (option.some d)


/-
These lemmas demonstrate that the pair of mutually recursive definitions
is equivalent to the version that Lean is unable to determine is decreasing.
-/

@[simp]
lemma holds_meta_var
	{D : Type}
	(M : meta_valuation D)
	(E : env)
	(X : meta_var_name)
	(V : valuation D) :
	holds D M E (meta_var_ X) V ↔ M X V := by {cases E; refl}

@[simp]
lemma holds_not
	{D : Type}
	(M : meta_valuation D)
	(E : env)
	(φ : formula)
	(V : valuation D) :
	holds D M E (not_ φ) V ↔ ¬ holds D M E φ V := by {cases E; refl}

@[simp]
lemma holds_imp
	{D : Type}
	(M : meta_valuation D)
	(E : env)
	(φ ψ : formula)
	(V : valuation D) :
	holds D M E (imp_ φ ψ) V ↔ holds D M E φ V → holds D M E ψ V := by {cases E; refl}

@[simp]
lemma holds_eq
	{D : Type}
	(M : meta_valuation D)
	(E : env)
	(x y : var_name)
	(V : valuation D) :
	holds D M E (eq_ x y) V ↔ V x = V y := by {cases E; refl}

@[simp]
lemma holds_forall
	{D : Type}
	(M : meta_valuation D)
	(E : env)
	(φ : formula)
	(x : var_name)
	(V : valuation D) :
	holds D M E (forall_ x φ) V ↔ ∀ (a : D), holds D M E φ (function.update V x a) := by {cases E; refl}

@[simp]
lemma holds_nil_def
	{D : Type}
	(M : meta_valuation D)
	(name : def_name)
	(args : list var_name)
	(V : valuation D) :
	holds D M [] (def_ name args) V ↔ false := by {refl}

@[simp]
lemma holds_not_nil_def
	{D : Type}
	(M : meta_valuation D)
	(d : definition_)
	(E : env)
	(name : def_name)
	(args : list var_name)
	(V : valuation D) :
	holds D M (d :: E) (def_ name args) V ↔
		if name = d.name ∧ args.length = d.args.length
		then holds D M E d.q (function.update_list V (list.zip d.args (list.map V args)))
		else holds D M E (def_ name args) V :=
begin
	unfold holds, unfold holds', simp only [option.elim],
end


example
	{D : Type}
	(M : meta_valuation D)
	(E : env)
	(V1 V2 : valuation D)
	(φ : formula)
	(S : list var_name)
	(hf : φ.not_free S)
	(h1 : ∀ v ∈ S, V1 v = V2 v) :
	holds D M E φ V1 ↔ holds D M E φ V2 :=
begin
	induction E generalizing S φ V1 V2,
	case list.nil : S φ V1 V2 hf h1
  {
		induction φ generalizing V1 V2,
		case formula.meta_var_ : φ V1 V2 h1
		{
			unfold formula.not_free at hf,
			contradiction,
		},
		case formula.not_ : φ φ_ih V1 V2 h1
		{
			unfold formula.not_free at hf,
			simp only [holds_not],
			apply not_congr,
			apply φ_ih hf, exact h1,
		},
		case formula.imp_ : φ ψ φ_ih ψ_ih V1 V2 h1
		{
			unfold formula.not_free at hf,
			cases hf,
			simp only [holds_imp],
			apply imp_congr,
			exact φ_ih hf_left V1 V2 h1,
			exact ψ_ih hf_right V1 V2 h1,
		},
		case formula.eq_ : x y V1 V2 h1
		{
			unfold formula.not_free at hf,
			cases hf,
			simp only [holds_eq],
			simp only [h1 x hf_left, h1 y hf_right],
		},
		case formula.forall_ : x φ φ_ih V1 V2 h1
		{
			unfold formula.not_free at hf,
			simp only [holds_forall],
			apply forall_congr, intros a,
			apply φ_ih,
			sorry,
			intros v h2,
			by_cases v = x,
			{
				rewrite h,
				simp only [function.update_same],
			},
			{
				simp only [function.update_noteq h],
				exact h1 v h2,
			},
		},
		case formula.def_ : name args V1 V2 h1
		{
			unfold formula.not_free at hf,
			simp only [holds_nil_def],
		},
	},
  case list.cons : E_hd E_tl E_ih S φ V1 V2 hf h1
  {
		induction φ generalizing V1 V2,
		case formula.meta_var_ : φ V1 V2 h1
		{
			unfold formula.not_free at hf,
			contradiction,
		},
		case formula.not_ : φ φ_ih V1 V2 h1
		{
			unfold formula.not_free at hf,
			simp only [holds_not],
			apply not_congr,
			apply φ_ih hf, exact h1,
		},
		case formula.imp_ : φ ψ φ_ih ψ_ih V1 V2 h1
		{
			unfold formula.not_free at hf,
			cases hf,
			simp only [holds_imp],
			apply imp_congr,
			exact φ_ih hf_left V1 V2 h1,
			exact ψ_ih hf_right V1 V2 h1,
		},
		case formula.eq_ : x y V1 V2 h1
		{
			unfold formula.not_free at hf,
			cases hf,
			simp only [holds_eq],
			simp only [h1 x hf_left, h1 y hf_right],
		},
		case formula.forall_ : x φ φ_ih V1 V2 h1
		{
			unfold formula.not_free at hf,
			simp only [holds_forall],
			apply forall_congr, intros a,
			apply φ_ih,
			sorry,
			intros v h2,
			by_cases v = x,
			{
				rewrite h,
				simp only [function.update_same],
			},
			{
				simp only [function.update_noteq h],
				exact h1 v h2,
			},
		},
		case formula.def_ : name args V1 V2 h1
		{
			unfold formula.not_free at hf,
			simp only [holds_not_nil_def],
			split_ifs,
			{
				cases h,
				apply E_ih E_hd.args E_hd.q _ _ E_hd.nf,
				intros v h2,
				simp only [list.mem_iff_nth_le] at h2,
				apply exists.elim h2,
				intros a h3,
				apply exists.elim h3, intros h4 h5,
				rewrite <- h5,
				have s1 : a < (list.map V1 args).length, simp,
				rewrite h_right, exact h4,

				have s2 : a < (list.map V2 args).length, simp,
				rewrite h_right, exact h4,

				have s3 : a < args.length, rewrite h_right, exact h4,

				rewrite function.update_list_zip V1 args E_hd.args a h4 s1,
				rewrite function.update_list_zip V2 args E_hd.args a h4 s2,

				have s4 : (list.map V1 args).nth_le a s1 = V1 (args.nth_le a s3),
				simp, rewrite s4,

				have s5 : (list.map V2 args).nth_le a s2 = V2 (args.nth_le a s3),
				simp, rewrite s5, apply h1,


				have s7 : args.nth_le a s3 ∈ args,
				apply list.nth_le_mem args a s3,
				
				apply set.mem_of_mem_of_subset _ hf,
				apply s7,

				exact E_hd.nodup, exact h_right, exact E_hd.nodup, exact h_right,
			},
			{
				apply E_ih,
				unfold formula.not_free, exact hf, exact h1,
			}
		},
	},
end


lemma ext_env_holds
	{D : Type}
	(M : meta_valuation D)
	(E E' : env)
	(φ : formula)
	(V : valuation D)
	(h1 : ∃ E1, E' = E1 ++ E) :
	holds D M E' φ V ↔ holds D M E φ V := sorry


lemma lem_1
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
		case formula.meta_var_ : φ V
		{
			simp only [holds_meta_var],
			unfold formula.subst,
			rewrite function.comp.assoc V σ.1 σ',
			rewrite h1,
			rewrite function.comp.right_id V,
			apply ext_env_holds, exact h3,
		},
		case formula.not_ : φ ih V
		{
			simp only [holds_not] at *,
			unfold formula.subst,
			rewrite ih,
			simp only [holds_not],
		},
		case formula.imp_ : φ ψ φ_ih ψ_ih V
		{
			simp only [holds_imp] at *,
			unfold formula.subst,
			simp only [φ_ih, ψ_ih],
			simp only [holds_imp],
		},
		case formula.eq_ : x y V
		{
			simp only [holds_eq] at *,
			unfold formula.subst,
			simp only [holds_eq],
		},
		case formula.forall_ : x φ φ_ih V
		{
			simp only [holds_forall],
			apply forall_congr, intros a,
			rewrite aux_1 σ.1 σ' x h2 V a,
			apply φ_ih,
		},
		case formula.def_ : name args V
		{
			simp only [holds_nil_def],
			unfold formula.subst,
			simp only [holds_nil_def],
		},
	},
  case list.cons : E_hd E_tl E_ih
  {
		induction φ generalizing V,
		case formula.meta_var_ : φ V
		{
			simp only [holds_meta_var],
			unfold formula.subst,
			rewrite function.comp.assoc V σ.1 σ',
			rewrite h1,
			rewrite function.comp.right_id V,
			apply ext_env_holds, exact h3,
		},
		case formula.not_ : φ ih
		{
			simp only [holds_not] at *,
			unfold formula.subst at *,
			rewrite ih,
			simp only [holds_not],
		},
		case formula.imp_ : φ ψ φ_ih ψ_ih
		{
			simp only [holds_imp] at *,
			unfold formula.subst,
			rewrite φ_ih, rewrite ψ_ih,
			simp only [holds_imp],
		},
		case formula.eq_ : x y
		{
			simp only [holds_eq] at *,
			unfold formula.subst,
			simp only [holds_eq],
		},
		case formula.forall_ : x φ φ_ih
		{
			simp only [holds_forall],
			unfold formula.subst at *,
			simp only [holds_forall],
			apply forall_congr, intros a,
			rewrite aux_1 σ.1 σ' x h2 V a,
			apply φ_ih,
		},
		case formula.def_ : name args
		{
			have s1 : ∃ (E1 : env), E' = E1 ++ E_tl,
			apply exists.elim h3, intros a h4,
			apply exists.intro (a ++ [E_hd]),
			simp only [list.append_assoc, list.singleton_append],
			exact h4,

			simp only [holds_not_nil_def] at *,
			unfold formula.subst at *,
			simp only [holds_not_nil_def] at *,
			sorry,
		},
	},
end


-- changing v does not_ cause the value of φ to change

def is_not_free (D : Type) (M : meta_valuation D) (E : env) (v : var_name) (φ : formula) : Prop :=
	∀ (V : valuation D) (a : D),
	holds D M E φ V ↔ holds D M E φ (function.update V v a)

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
		rewrite <- aux_3 V V' v h2,
		apply h1,
	},
	{
		intros h1 V a,
		apply h1,
		intros a' h2,
		simp only [function.update_noteq h2],
	}
end


lemma not_free_imp_is_not_free
	{D : Type}
	(M : meta_valuation D)
	(E : env)
	(Γ : list (var_name × meta_var_name))
	(v : var_name)
	(φ : formula)
	(H : not_free Γ v φ)
	(nf : ∀ X, (v, X) ∈ Γ → is_not_free D M E v (meta_var_ X)) :
	is_not_free D M E v φ :=
begin
	induction E,
	case list.nil
  {
		induction φ,
		case formula.meta_var_ : φ
		{
			unfold not_free at H,
			exact nf φ H,
		},
		case formula.not_ : φ φ_ih
		{
			unfold not_free at *,
			unfold is_not_free at *,
			simp only [holds_not],
			intros V a,
			apply not_congr,
			exact φ_ih H V a,
		},
		case formula.imp_ : φ ψ φ_ih ψ_ih
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
			simp only [holds_eq],
			cases H,
			intros V a,
			simp only [function.update_noteq H_left, function.update_noteq H_right],
		},
		case formula.forall_ : x φ φ_ih
		{
			unfold is_not_free at *,
			unfold not_free at *,
			simp only [holds_forall],
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
		case formula.def_ : name args
		{
			unfold is_not_free at *,
			unfold not_free at *,
			intros V a,
			simp only [holds_nil_def],
		},
	},
  case list.cons : E_hd E_tl E_ih
  {
		induction φ,
		case formula.meta_var_ : φ
		{
			unfold not_free at H,
			apply nf, exact H,
		},
		case formula.not_ : φ φ_ih
		{
			unfold not_free at *,
			unfold is_not_free at *,
			sorry,
		},
		case formula.imp_ : φ_ᾰ φ_ᾰ_1 φ_ih_ᾰ φ_ih_ᾰ_1
		{ admit },
		case formula.eq_ : φ_ᾰ φ_ᾰ_1
		{ admit },
		case formula.forall_ : φ_ᾰ φ_ᾰ_1 φ_ih
		{ admit },
		case formula.def_ : name args
		{
			unfold not_free at H,
			unfold is_not_free at *,
			simp only [holds_not_nil_def, holds_meta_var] at *,
			specialize E_ih nf,
			intros V a,
			split_ifs,
			{
				sorry,
			},
			{
				apply E_ih,
			}
		},
	},
end


lemma lem_2
	{D : Type}
	(M : meta_valuation D)
	(E : env)
	(Γ Γ' : list (var_name × meta_var_name))
	(σ : instantiation)
	(σ' : var_name → var_name)
  (τ : meta_instantiation)
  (left : ((σ.1 ∘ σ') = id))
  (right : ((σ' ∘ σ.1) = id))
  (nf : ∀ (v : var_name) (X : meta_var_name), ((v, X) ∈ Γ') → is_not_free D M E v (meta_var_ X))
  (H : ∀ (v : var_name) (X : meta_var_name), ((v, X) ∈ Γ) → not_free Γ' (σ.1 v) (τ X)) :
  ∀ (v : var_name) (X : meta_var_name),
		((v, X) ∈ Γ) →
			is_not_free D (fun (X : meta_var_name) (V' : valuation D), holds D M E (τ X) (V' ∘ σ'))
				E v (meta_var_ X) :=
begin
	intros v X h1,
	unfold is_not_free,
	simp only [holds_meta_var],
	intros V a,
	rewrite <- aux_2 σ' σ.1 v left right,
	apply not_free_imp_is_not_free M E Γ',
	exact H v X h1,
	intros X' h2,
	exact nf (σ.1 v) X' h2,
end


example
	(D : Type)
	(M : meta_valuation D)
	(E : env)
	(Γ : list (var_name × meta_var_name))
	(Δ : list formula)
	(φ : formula)
	(H : is_proof Γ Δ φ)
	(nf : ∀ v X, (v, X) ∈ Γ → is_not_free D M E v (meta_var_ X))
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
		simp only [holds_forall],
		intros V a,
		apply H_ih M nf hyp,
	},
  case is_proof.pred_1 : H_Γ H_Δ H_φ H_ψ H_x M nf hyp
  {
		simp only [holds_imp, holds_forall],
		intros V h1 h2 a,
		apply h1,
		apply h2,
	},
  case is_proof.pred_2 : H_Γ H_Δ H_φ H_x H_ᾰ M nf hyp
  {
		have s1 : is_not_free D M E H_x H_φ,
		apply not_free_imp_is_not_free M E H_Γ H_x H_φ H_ᾰ,
		intros X h2, exact nf H_x X h2,

		simp only [holds_imp, holds_forall],
		intros V h2 a,
		unfold is_not_free at s1,
		rewrite <- s1, exact h2,
	},
  case is_proof.eq_1 : H_Γ H_Δ H_x H_y H_ᾰ M nf hyp
  {
		unfold exists_,
		simp only [holds_not, holds_forall, holds_eq, not_forall],
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
		simp only [holds_imp, holds_eq],
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
		rewrite <- lem_1 V M E _ H_σ σ' H_τ left right,
		apply H_ih_ᾰ,
		intros v X h1,
		exact lem_2 M E H_Γ H_Γ' H_σ σ' H_τ left right nf H_ᾰ_1 v X h1,
		intros φ h2 V',
		specialize H_ih_ᾰ_1 φ h2 M nf hyp (V' ∘ σ'),
		rewrite <- lem_1 (V' ∘ σ') M E E H_σ σ' H_τ left right _ φ at H_ih_ᾰ_1,
		rewrite function.comp.assoc at H_ih_ᾰ_1,
		rewrite right at H_ih_ᾰ_1,
		simp only [function.comp.right_id] at H_ih_ᾰ_1,
		exact H_ih_ᾰ_1,
		apply exists.intro list.nil,
		simp only [list.nil_append],
		apply exists.intro list.nil,
		simp only [list.nil_append],
	},
end
