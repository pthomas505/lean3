/-
References:

-/


import data.finset data.fin.vec_notation

set_option pp.parens true


def function.update_fin
	{α β : Type}
	[decidable_eq α]
	(σ : α → β) :
	Π (n : ℕ), (fin n → α) → (fin n → β) → (α → β)
| 0 _ _ := σ
| (n + 1) f g :=
	function.update
		(function.update_fin n (fun (i : fin n), (f i)) (fun (i : fin n), (g i)))
		(f n) (g n)

#eval function.update_fin (fun (n : ℕ), n) 3 ![0, 5, 0] ![10, 8, 5] 0


example
	{α β : Type}
	[decidable_eq α]
	(σ : α → β)
	(n : ℕ)
	(xs : fin n → α)
	(ys : fin n → β)
	(x : α)
	(h1 : ∀ (i : fin n), x ≠ xs i) :
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
		have s1 : x ≠ xs ↑n, apply h1,
		simp only [function.update_noteq s1],
		apply ih,
		intros i,
		by_cases ↑i = ↑n,
		rewrite h, exact s1,
		exact h1 ↑i
	},
end

example
	{α : Type}
	(n : ℕ)
	(f : fin n.succ → α)
	(nodup : function.injective f) :
	function.injective (fun (i : fin n), f i.cast_succ) :=
nodup.comp (fin.cast_succ_injective _)


example
	{α β : Type}
	[decidable_eq α]
	(σ : α → β)
	(n : ℕ)
	(xs : fin n → α)
	(nodup : function.injective xs)
	(ys : fin n → β)
	(x : α)
	(i : fin n)
	(h1 : x = xs i) :
	function.update_fin σ n xs ys x = ys i :=
begin
	induction n,
	case nat.zero
  { exact fin.elim0 i },
  case nat.succ : n ih
  {
		unfold function.update_fin,
		subst h1,
		by_cases i = ↑n,
		{
			rewrite h, apply function.update_same
		},
		{
			have s1 : xs i ≠ xs ↑n, intro contra, apply h, tauto,
			simp only [function.update_noteq s1],
			have s2 : function.injective (fun (i : fin n), xs ↑i),
			unfold function.injective at *, intros a b h2,
			sorry,
			sorry,
		}
	},
end


def fin_map
	{α β : Type}
	(m : α → β)
	(n : ℕ)
	(f : fin n → α) :
	(fin n → β) :=
	fun (i : fin n), m (f i)


abbreviation var_name := ℕ
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


-- sub_var_term_single x t t0 = t0 [x / t]
def sub_var_term_single (x : var_name) (t : term) : term → term
| (var y) := if y = x then t else var y
| (func n f ts) := func n f (fun (i : fin n), sub_var_term_single (ts i))


-- (((t0 [x1 / t1]) [x2 / t2]) ... [xn / tn])
def sub_var_term_single_repeat
	(t0 : term) :
	Π (n : ℕ), (fin n → var_name) → (fin n → term) → term
| 0 _ _ := t0
| (n + 1) xs ts :=
	sub_var_term_single (xs n) (ts n)
		(sub_var_term_single_repeat n (fun (i : fin n), (xs i)) (fun (i : fin n), (ts i)))


lemma lem_b
	(n : ℕ)
	(zs : fin n → var_name)
	(ts : fin n → term)
	(i : fin n) :
	sub_var_term_single_repeat (var (zs i)) n zs ts = ts i :=
begin
	induction n,
	case nat.zero
  { apply fin.elim0 i },
  case nat.succ : n ih
  {
		by_cases i = n,
		{
			specialize ih (fin.init zs) (fin.init ts),
			sorry
		},
		{
			sorry
		}
	},
end


structure interpretation (ω : Type) : Type :=
(nonempty : nonempty ω)
(var : var_name → ω)
(func (n : ℕ) : func_name → ((fin n → ω) → ω))
(pred (n : ℕ) : pred_name → ((fin n → ω) → Prop))


def interpretation.var_update
	{ω : Type}
	(I : interpretation ω)
	(x : var_name)
	(d : ω) :
	interpretation ω :=
	{
		nonempty := I.nonempty,
		var := function.update I.var x d,
		func := I.func,
		pred := I.pred
	}


def interpretation.var_update_repeat
	{ω : Type}
	(I : interpretation ω)
	(n : ℕ)
	(xs : fin n → var_name)
	(ds : fin n → ω) :
	interpretation ω :=
	{
		nonempty := I.nonempty,
		var := function.update_fin I.var n xs ds,
		func := I.func,
		pred := I.pred
	}


def interpretation.term {ω : Type} (I : interpretation ω) : term → ω
| (var x) := I.var x
| (func n f t) := I.func n f (fun (i : fin n), interpretation.term (t i))


def term.all_var_set : term → finset var_name
| (var x) := {x}
| (func n f t) := finset.univ.bUnion (fun (i : fin n), (t i).all_var_set)


lemma lem_1_a
	(n : ℕ)
	(x : var_name)
	(t : term)
	(ω : Type)
	(I : interpretation ω)
	(t0 : term) :
	(I.var_update x (I.term t)).term t0 = I.term (sub_var_term_single x t t0) :=
begin
	induction t0,
	case term.var : y
  {
		unfold sub_var_term_single,
		unfold interpretation.var_update,
		unfold interpretation.term,
		simp only,
		split_ifs,
		{
			subst h,
			apply function.update_same
		},
		{
			unfold interpretation.term,
			apply function.update_noteq h
		}
	},
  case term.func : n f ts ih
  {
		simp only at ih,
		unfold sub_var_term_single,
		unfold interpretation.term,
		have s1 : (I.var_update x (I.term t)).func = I.func, unfold interpretation.var_update,
		rewrite s1,
		congr, funext,
		exact ih i,
	},
end

lemma lem_1_b
	(n : ℕ)
	(zs : fin n → var_name)
	(nodup : function.injective zs)
	(ts : fin n → term)
	(h1 : ∀ (i j : fin n), (zs i) ∉ (ts j).all_var_set)
	(ω : Type)
	(I : interpretation ω)
	(t0 : term) :
	(I.var_update_repeat n zs (fin_map I.term n ts)).term t0 =
		I.term (sub_var_term_single_repeat t0 n zs ts) :=
begin
	induction t0,
	case term.var : x
  {
		by_cases ∃ (i : fin n), x = zs i,
		{
			apply exists.elim h, intros i h2,
			rewrite h2,
			unfold interpretation.term,
			unfold interpretation.var_update_repeat,
			simp only,
			have s1 : function.update_fin I.var n zs (fin_map I.term n ts) (zs i) = (fin_map I.term n ts) i,
			sorry, --apply lem_a I.var n zs nodup (fin_map I.term n ts) (zs i), refl,
			rewrite s1,
			rewrite lem_b,
			unfold fin_map
		},
		{
			push_neg at h,
			unfold interpretation.var_update_repeat,
			unfold interpretation.term,
			simp,
			have s1 : function.update_fin I.var n zs (fin_map I.term n ts) x = I.var x,
			sorry,
			sorry,
		}
	},
  case term.func : t0_n t0_ᾰ t0_ᾰ_1 t0_ih
  { admit },
end