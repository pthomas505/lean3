/-
References:

-/


import data.finset

set_option pp.parens true


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


def sub_var_term_single (x : var_name) (t : term) : term → term
| (var y) := if y = x then t else var y
| (func n f ts) := func n f (fun (i : fin n), sub_var_term_single (ts i))


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
