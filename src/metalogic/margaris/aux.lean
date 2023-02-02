/-
Reference:
First Order Mathematical Logic (Dover Books on Mathematics)
by Angelo Margaris
-/


import data.finset

set_option pp.parens true


@[derive decidable_eq]
inductive variable_ : Type
| variable_ : string → variable_


@[derive decidable_eq]
inductive pred_name_ : Type
| pred_name_ : string → pred_name_


@[derive decidable_eq]
inductive formula : Type
| pred_ : pred_name_ → list variable_ → formula
| not_ : formula → formula
| imp_ : formula → formula → formula
| forall_ : variable_ → formula → formula

open formula


def formula.free_var_set : formula → finset variable_
| (pred_ name args) := args.to_finset
| (not_ P) := P.free_var_set
| (imp_ P Q) := P.free_var_set ∪ Q.free_var_set
| (forall_ x P) := P.free_var_set \ {x}


/-
pg. 48

If $P$ is a formula, $v$ is a variable, and $t$ is a term, then $P(t/v)$ is the result of replacing each free occurrence of $v$ in $P$ by an occurrence of $t$.
-/

-- v -> t
def replace
  {α : Type}
  [decidable_eq α]
  (v t x : α) : α :=
  if x = v then t else x

-- P (t/v)
-- v -> t in P
def replace_free (v t : variable_) : formula → formula
| (pred_ name args) := pred_ name (args.map (replace v t))
| (not_ P) := not_ (replace_free P)
| (imp_ P Q) := imp_ (replace_free P) (replace_free Q)
| (forall_ x P) :=
  if x = v
  then forall_ x P
  else forall_ x (replace_free P)


/-
pg. 48

If $v$ and $u$ are variables and $P$ is a formula, then $P$ admits $u$ for $v$ if and only if there is no free occurrence of $v$ in $P$ that becomes a bound occurrence of $u$ in $P(u/v)$. If $t$ is a term, then $P$ admits $t$ for $v$ if and only if $P$ admits for $v$ every variable in $t$.
-/

-- P admits u for v
-- v → u in P


def admits_aux (v u : variable_) : finset variable_ → formula → Prop
| binders (pred_ name args) :=
    v ∉ args ∨
    v ∈ binders ∨
    u ∉ binders
| binders (not_ P) := admits_aux binders P
| binders (imp_ P Q) := admits_aux binders P ∧ admits_aux binders Q
| binders (forall_ x P) := admits_aux (binders ∪ {x}) P

def admits (v u : variable_) (P : formula) : Prop :=
  admits_aux v u ∅ P


example
  (P : formula)
  (v u : variable_)
  (S T : finset variable_)
  (h1 : admits_aux v u (S ∪ T) P)
  (h2 : v ∉ T) :
  admits_aux v u S P :=
begin
  induction P generalizing S,
  case formula.pred_ : name args S h1
  {
    unfold admits_aux at h1,

    unfold admits_aux,
    cases h1,
    {
      apply or.intro_left,
      exact h1,
    },
    {
      cases h1,
      {
        simp only [finset.mem_union] at h1,
        cases h1,
        {
          apply or.intro_right,
          apply or.intro_left,
          exact h1,
        },
        {
          contradiction,
        }
      },
      {
        simp only [finset.mem_union] at h1,
        push_neg at h1,
        cases h1,
        apply or.intro_right,
        apply or.intro_right,
        exact h1_left,
      }
    }
  },
  case formula.not_ : P P_ih S h1
  {
    unfold admits_aux at h1,

    unfold admits_aux,
    exact P_ih S h1,
  },
  case formula.imp_ : P Q P_ih Q_ih S h1
  {
    unfold admits_aux at h1,
    cases h1,

    unfold admits_aux,
    split,
    {
      exact P_ih S h1_left,
    },
    {
      exact Q_ih S h1_right,
    },
  },
  case formula.forall_ : x P P_ih S h1
  {
    unfold admits_aux at h1,
    simp only [finset.union_right_comm S T {x}] at h1,

    unfold admits_aux,
    apply P_ih,
    exact h1,
  },
end


example
  (P : formula)
  (v u : variable_)
  (S T : finset variable_)
  (h1 : admits_aux v u S P)
  (h2 : u ∉ T) :
  admits_aux v u (S ∪ T) P :=
begin
  induction P generalizing S,
  case formula.pred_ : name args S h1
  {
    unfold admits_aux at h1,

    unfold admits_aux,
    cases h1,
    {
      apply or.intro_left,
      exact h1,
    },
    {
      cases h1,
      {
        simp only [finset.mem_union],
        apply or.intro_right,
        apply or.intro_left,
        apply or.intro_left,
        exact h1,
      },
      {
        apply or.intro_right,
        apply or.intro_right,
        simp only [finset.mem_union],
        push_neg,
        split,
        {
          exact h1,
        },
        {
          exact h2,
        },
      }
    }
  },
  case formula.not_ : P P_ih S h1
  {
    unfold admits_aux at h1,

    unfold admits_aux,
    exact P_ih S h1,
  },
  case formula.imp_ : P Q P_ih Q_ih S h1
  {
    unfold admits_aux at h1,
    cases h1,

    unfold admits_aux,
    split,
    {
      exact P_ih S h1_left,
    },
    {
      exact Q_ih S h1_right,
    },
  },
  case formula.forall_ : x P P_ih S h1
  {
    unfold admits_aux at h1,

    unfold admits_aux,
    simp only [finset.union_right_comm S T {x}],
    apply P_ih,
    exact h1,
  },
end


def admits_aux' (v u : variable_) : finset variable_ → formula → Prop
| binders (pred_ name args) :=
    v ∈ args → -- if there is a free occurrence of v in P
    u ∉ binders -- then it does not become a bound occurrence of u in P(u/v)
| binders (not_ P) := admits_aux' binders P
| binders (imp_ P Q) := admits_aux' binders P ∧ admits_aux' binders Q
| binders (forall_ x P) := x = v ∨ admits_aux' (binders ∪ {x}) P

def admits' (v u : variable_) (P : formula) : Prop :=
  admits_aux' v u ∅ P


example
  (P : formula)
  (v u : variable_)
  (S T : finset variable_)
  (h1 : admits_aux' v u (S ∪ T) P) :
  --(h2 : v ∉ T) :
  admits_aux' v u S P :=
begin
  induction P generalizing S,
  case formula.pred_ : name args S h1
  {
    unfold admits_aux' at h1,
    simp only [finset.mem_union] at h1,
    push_neg at h1,

    unfold admits_aux',
    intros a1,
    specialize h1 a1,
    cases h1,
    exact h1_left,
  },
  case formula.not_ : P P_ih S h1
  {
    unfold admits_aux' at h1,

    unfold admits_aux',
    exact P_ih S h1,
  },
  case formula.imp_ : P Q P_ih Q_ih S h1
  {
    unfold admits_aux' at h1,
    cases h1,

    unfold admits_aux',
    split,
    {
      exact P_ih S h1_left,
    },
    {
      exact Q_ih S h1_right,
    },
  },
  case formula.forall_ : x P P_ih S h1
  {
    unfold admits_aux' at h1,
    simp only [finset.union_right_comm S T {x}] at h1,

    unfold admits_aux',
    cases h1,
    {
      apply or.intro_left,
      exact h1,
    },
    {
      apply or.intro_right,
      apply P_ih,
      exact h1,
    }
  },
end
