import logic.function.basic

set_option pp.parens true


def var_symbol := ℕ
def func_symbol := ℕ
def func_var_symbol := ℕ
def pred_symbol := ℕ
def pred_var_symbol := ℕ


inductive term : Type
| var : var_symbol → term
| func (n : ℕ) : func_symbol → (fin n → term) → term
| func_var (n : ℕ) : func_var_symbol → (fin n → term) → term

open term


inductive formula : Type
| bottom : formula
| top : formula
| pred (n : ℕ) : pred_symbol → (fin n → term) → formula
| eq : term → term → formula
| pred_var (n : ℕ) : pred_var_symbol → (fin n → term) → formula
| not : formula → formula
| and : formula → formula → formula
| or : formula → formula → formula
| imp : formula → formula → formula
| iff : formula → formula → formula
| forall_var : var_symbol → formula → formula
| exists_var : var_symbol → formula → formula
| forall_func_var : ℕ → func_var_symbol → formula → formula
| exists_func_var : ℕ → func_var_symbol → formula → formula
| forall_pred_var : ℕ → pred_var_symbol → formula → formula
| exists_pred_var : ℕ → pred_var_symbol → formula → formula

open formula


structure assignment (D : Type) : Type :=
(var : var_symbol → D)
-- n place function variable to an n place function
(func_var (n : ℕ) : func_var_symbol → ((fin n → D) → D))
-- n place relation variable to an n place relation
(pred_var (n : ℕ) : pred_var_symbol → ((fin n → D) → Prop))

def update_func_var
	(D : Type)
	(v : assignment D)
	(n : ℕ)
	(f : func_var_symbol)
	(a : (fin n → D) → D) :
	Π (k : ℕ), func_var_symbol → ((fin k → D) → D) :=
	fun (k : ℕ) (g : func_var_symbol),
	if h : k = n ∧ g = f
	then by {cases h, subst h_left, exact a}
	else v.func_var k g

def update_pred_var
	(D : Type)
	(v : assignment D)
	(n : ℕ)
	(X : pred_var_symbol)
	(a : (fin n → D) → Prop) :
	Π (k : ℕ), pred_var_symbol → ((fin k → D) → Prop) :=
	fun (k : ℕ) (P : pred_var_symbol),
	if h : k = n ∧ P = X
	then by {cases h, subst h_left, exact a}
	else v.pred_var k P


structure model (D : Type) : Type :=
(nonempty : nonempty D)
(func (n : ℕ) : func_symbol → ((fin n → D) → D))
(pred (n : ℕ) : pred_symbol → ((fin n → D) → Prop))


def eval_term (D : Type) (m : model D) (v : assignment D) : term → D
| (var x) := v.var x
| (func n f t) := m.func n f (fun (i : fin n), eval_term (t i))
| (func_var n u t) := v.func_var n u (fun (i : fin n), eval_term (t i))


def holds (D : Type) (m : model D) : assignment D → formula → Prop
| _ bottom := false
| _ top := true
| v (pred n P t) := m.pred n P (fun (i : fin n), eval_term D m v (t i))
| v (eq s t) := eval_term D m v s = eval_term D m v t
| v (pred_var n X t) := v.pred_var n X (fun (i : fin n), eval_term D m v (t i))
| v (not φ) := ¬ holds v φ
| v (and φ ψ) := holds v φ ∧ holds v ψ
| v (or φ ψ) := holds v φ ∨ holds v ψ
| v (imp φ ψ) := holds v φ → holds v ψ
| v (iff φ ψ) := holds v φ ↔ holds v ψ
| v (forall_var x φ) := ∀ a : D,
		holds {
			var := function.update v.var x a,
			func_var := v.func_var,
			pred_var := v.pred_var } φ
| v (exists_var x φ) := ∃ a : D,
		holds {
			var := function.update v.var x a,
			func_var := v.func_var,
			pred_var := v.pred_var } φ
| v (forall_func_var n X φ) := ∀ (a : (fin n → D) → D),
		holds {
			var := v.var,
			func_var := update_func_var D v n X a,
			pred_var := v.pred_var } φ
| v (exists_func_var n X φ) := ∃ (a : (fin n → D) → D),
		holds {
			var := v.var,
			func_var := update_func_var D v n X a,
			pred_var := v.pred_var } φ
| v (forall_pred_var n X φ) := ∀ (a : (fin n → D) → Prop),
		holds {
			var := v.var,
			func_var := v.func_var,
			pred_var := update_pred_var D v n X a } φ
| v (exists_pred_var n X φ) := ∃ (a : (fin n → D) → Prop),
		holds {
			var := v.var,
			func_var := v.func_var,
			pred_var := update_pred_var D v n X a } φ
