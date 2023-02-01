/-
Reference:
First Order Mathematical Logic (Dover Books on Mathematics)
by Angelo Margaris
-/


import data.finset


@[derive decidable_eq]
inductive variable_ : Type
| variable_ : string → variable_


@[derive decidable_eq]
inductive pred_symbol_ : Type
| pred_symbol_ : string → pred_symbol_


@[derive decidable_eq]
inductive formula : Type
| pred_ : pred_symbol_ → list variable_ → formula
| not_ : formula → formula
| imp_ : formula → formula → formula
| forall_ : variable_ → formula → formula

open formula


def formula.free_var_set : formula → finset variable_
| (pred_ name args) := args.to_finset
| (not_ P) := P.free_var_set
| (imp_ P Q) := P.free_var_set ∪ Q.free_var_set
| (forall_ x P) := P.free_var_set \ {x}


def formula.is_bound_list_aux : finset variable_ →  formula → list bool
| binders (pred_ name args) := args.map (fun (x : variable_), x ∈ binders)
| binders (not_ P) := P.is_bound_list_aux binders
| binders (imp_ P Q) := (P.is_bound_list_aux binders) ++ (Q.is_bound_list_aux binders)
| binders (forall_ x P) := P.is_bound_list_aux (binders ∪ {x})

def formula.is_bound_list (P : formula) : list bool :=
  P.is_bound_list_aux ∅


@[derive decidable_eq]
inductive formula' : Type
| pred_ : pred_symbol_ → list bool → formula'
| not_ : formula' → formula'
| imp_ : formula' → formula' → formula'
| forall_ : variable_ → formula' → formula'

def to_is_free_aux : finset variable_ → formula → formula'
| binders (pred_ name args) :=
    formula'.pred_ name (args.map (fun (x : variable_), x ∉ binders))
| binders (not_ P) := formula'.not_ (to_is_free_aux binders P)
| binders (imp_ P Q) := formula'.imp_ (to_is_free_aux binders P) (to_is_free_aux binders Q)
| binders (forall_ x P) := formula'.forall_ x (to_is_free_aux (binders ∪ {x}) P)

def to_is_free (P : formula) : formula' :=
  to_is_free_aux ∅ P


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

/-
def admits (v u : variable_) : formula → Prop
| (pred_ name args) := true
| (not_ P) := admits P
| (imp_ P Q) := admits P ∧ admits Q
| (forall_ x P) := x = v ∨ ((x = u → v ∉ P.free_var_set) ∧ admits P)
-/



example
  (α : Type)
  [decidable_eq α]
  (S T : finset α)
  (x : α)
  (h1 : (S \ {x}) ∩ T = ∅) :
  S ∩ (T ∪ {x}) = ∅ :=
begin
  sorry,
end

lemma blah
  (P : formula)
  (v u : variable_)
  (S : finset variable_)
  (h1 : admits_aux v u S P)
  (h2 : P.free_var_set ∩ S = ∅) :
  to_is_free_aux S (replace_free v u P) = to_is_free_aux S P :=
begin
  induction P generalizing S,
  case formula.pred_ : name args S h1 h2
  {
    unfold replace_free,
    induction args generalizing S,
    case list.nil
    {
      simp only [list.map_nil],
    },
    case list.cons : args_hd args_tl args_ih
    {
      unfold admits_aux at h1,
      simp only [list.mem_cons_iff] at h1,
      push_neg at h1,

      unfold formula.free_var_set at h2,

      
      unfold to_is_free_aux at args_ih,
      unfold admits_aux at args_ih,
      unfold formula.free_var_set at args_ih,
      specialize args_ih S,

      have s1 : v ∉ args_tl ∨ v ∈ S ∨ u ∉ S,
      cases h1,
      cases h1,
      apply or.intro_left,
      exact h1_right,
      apply or.intro_right,
      exact h1,

      specialize args_ih s1 sorry,
      injection args_ih,


      unfold to_is_free_aux,
      congr' 1,
      simp only [list.map, list.map_map] at *,
      split,
      {
        unfold replace,
        split_ifs,
        cases h1,
        rewrite h at h1,
        cases h1,
        contradiction,
        subst h,
        cases h1,
        sorry, --contradiction
        sorry, -- true and true
        refl,
      },
      {
        exact h_2,
      }
    },
  },
  case formula.not_ : P P_ih S h1 h2
  {
    unfold admits_aux at h1,
    unfold formula.free_var_set at h2,
    unfold replace_free,
    unfold to_is_free_aux,
    congr' 1,
    exact P_ih S h1 h2,
  },
  case formula.imp_ : P Q P_ih Q_ih S h1 h2
  {
    unfold admits_aux at h1,
    cases h1,
    unfold formula.free_var_set at h2,
    rewrite finset.inter_distrib_right at h2,
    rewrite finset.union_eq_empty_iff at h2,
    cases h2,
    
    unfold replace_free,
    unfold to_is_free_aux,
    congr' 1,
    apply P_ih S h1_left h2_left,
    apply Q_ih S h1_right h2_right,
  },
  case formula.forall_ : x P P_ih S h1 h2
  {
    unfold replace_free,
    split_ifs,
    {
      refl,
    },
    {
      unfold admits_aux at h1,

      unfold formula.free_var_set at h2,

      specialize P_ih (S ∪ {x}) h1,
      specialize P_ih sorry,
      unfold to_is_free_aux,
      congr,
      exact P_ih,
    }
  },
end


example
  (P : formula)
  (v u : variable_)
  (h1 : admits v u P) :
  to_is_free (replace_free v u P) = to_is_free P :=
begin
  unfold admits at h1,
  unfold to_is_free,
  apply blah,
  exact h1,
  simp only [finset.inter_empty],
end


example
  (P : formula)
  (v u : variable_)
  (binders : finset variable_)
  (h1 : admits_aux v u binders P)
  (h2 : ∀ (x : variable_), x ∈ P.free_var_set → x ∉ binders) :
  (replace_free v u P).is_bound_list_aux binders =
    P.is_bound_list_aux binders :=
begin
  induction P generalizing binders,
  case formula.pred_ : name args binders h1 h2
  {
    induction args,
    case list.nil
    {
      unfold replace_free,
      simp only [list.map_nil],
    },
    case list.cons : args_hd args_tl args_ih
    {
      unfold admits_aux at h1,
      simp only [list.mem_cons_iff] at h1,
      push_neg at h1,

      unfold formula.free_var_set at h2,
      simp only [list.to_finset_cons, finset.mem_insert, list.mem_to_finset, forall_eq_or_imp] at h2,
      cases h2,

      unfold admits_aux at args_ih,

      unfold formula.free_var_set at args_ih,
      simp only [list.mem_to_finset] at args_ih,

      unfold replace_free at args_ih,
      unfold formula.is_bound_list_aux at args_ih,
      simp only [list.map_map] at args_ih,

      unfold replace_free,
      unfold formula.is_bound_list_aux,
      simp only [list.map, list.map_map, bool.to_bool_eq],

      split,
      {
        have s1 : ¬ replace v u args_hd ∈ binders,
        unfold replace,
        split_ifs,
        {
          subst h,
          cases h1,
          {
            cases h1,
            contradiction,
          },
          {
            cases h1,
            {
              contradiction,
            },
            {
              exact h1,
            }
          }
        },
        {
          exact h2_left,
        },

        split,
        {
          intros a1,
          contradiction,
        },
        {
          intros a1,
          contradiction,
        },
      },
      {
        apply args_ih,
        {
          cases h1,
          {
            cases h1,
            apply or.intro_left,
            exact h1_right,
          },
          {
            apply or.intro_right,
            exact h1,
          },
        },
        {
          exact h2_right,
        },
      },
    },
  },
  case formula.not_ : P_ᾰ P_ih binders h1 h2
  { admit },
  case formula.imp_ : P_ᾰ P_ᾰ_1 P_ih_ᾰ P_ih_ᾰ_1 binders h1 h2
  { admit },
  case formula.forall_ : P_ᾰ P_ᾰ_1 P_ih binders h1 h2
  { admit },
end
