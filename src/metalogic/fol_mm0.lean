import logic.function.basic
import tactic


set_option pp.parens true


lemma aux_1
  {α β : Type}
  [decidable_eq α]
  (g : α → β)
  (f f' : α → α)
  (x : α)
  (a : β)
  (h1 : f' ∘ f = id) :
  (function.update g (f x) a) ∘ f = function.update (g ∘ f) x a :=
begin
    have s1 : function.left_inverse f' f,
    exact congr_fun h1,

    apply function.update_comp_eq_of_injective,
    exact function.left_inverse.injective s1,
end


lemma aux_2
  {α β : Type}
  [decidable_eq α]
  (g : α → β)
  (f f' : α → α)
  (x : α)
  (a : β)
  (h1 : f' ∘ f = id)
  (h2 : f ∘ f' = id) :
  (function.update g x a) ∘ f = function.update (g ∘ f) (f' x) a :=
begin
  rewrite <- aux_1 g f f' (f' x) a h1,
  congr,
  rewrite <- function.comp_app f f' x,
  rewrite h2,
  exact id.def x,
end


lemma aux_3
  {α β : Type}
  [decidable_eq α]
  (f g : α → β)
  (x : α)
  (h1 : ∀ (y : α), ¬ y = x → f y = g y) :
  function.update f x (g x) = g :=
begin
  apply funext, intros y,
  by_cases c1 : y = x,
  {
    rewrite c1,
    simp only [function.update_same],
  },
  {
    simp only [function.update_noteq c1],
    exact h1 y c1,
  },
end


lemma list.nth_le_mem_zip
  {α β : Type}
  [decidable_eq α]
  (l1 : list α)
  (l2 : list β)
  (n : ℕ)
  (h1 : n < l1.length)
  (h2 : n < l2.length) :
  ((l1.nth_le n h1, l2.nth_le n h2) ∈ l1.zip l2) :=
begin
  have s1 : n < (l1.zip l2).length,
  simp only [list.length_zip, lt_min_iff],
  split,
  {
    exact h1,
  },
  {
    exact h2,
  },

  have s2 : (list.zip l1 l2).nth_le n s1 = (l1.nth_le n h1, l2.nth_le n h2),
  exact list.nth_le_zip,

  rewrite <- s2,
  exact (list.zip l1 l2).nth_le_mem n s1,
end


lemma list.map_fst_zip_is_prefix
  {α β : Type}
  (l1 : list α)
  (l2 : list β) :
  list.map prod.fst (l1.zip l2) <+: l1 :=
begin
  induction l1 generalizing l2,
  case list.nil : l2
  {
    simp only [list.zip_nil_left, list.map_nil],
  },
  case list.cons : l1_hd l1_tl l1_ih l2
  {
    induction l2,
    case list.nil
    {
      unfold list.is_prefix,
      apply exists.intro (l1_hd :: l1_tl),
      simp only [list.zip_nil_right, list.map_nil, list.nil_append, eq_self_iff_true, and_self],
    },
    case list.cons : l2_hd l2_tl l2_ih
    {
      simp only [list.map, list.zip_cons_cons],
      rewrite list.prefix_cons_inj,
      exact l1_ih l2_tl,
    },
  },
end


lemma list.map_fst_zip_nodup
  {α β : Type}
  (l1 : list α)
  (l2 : list β)
  (h1 : l1.nodup) :
  (list.map prod.fst (l1.zip l2)).nodup :=
begin
  have s1 : list.map prod.fst (l1.zip l2) <+ l1,
  apply list.is_prefix.sublist,
  exact l1.map_fst_zip_is_prefix l2,

  exact list.nodup.sublist s1 h1,
end


def function.update_list
  {α β : Type}
  [decidable_eq α]
  (f : α → β) :
  list (α × β) → α → β
| [] := f
| (hd :: tl) := function.update (function.update_list tl) hd.fst hd.snd

#eval function.update_list (fun (n : ℕ), n) [(0,1), (3,2), (0,2)] 0


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
    simp only [list.not_mem_nil] at h2,
    contradiction,
  },
  case list.cons : hd tl ih
  {
    simp only [list.map, list.nodup_cons, list.mem_map, prod.exists,
      exists_and_distrib_right, exists_eq_right, not_exists] at h1,
    cases h1,

    simp only [list.mem_cons_iff] at h2,

    unfold function.update_list,
    cases h2,
    {
      rewrite h2,
      simp only [function.update_same],
    },
    {
      have s1 : ¬ x.fst = hd.fst,
      intro contra,
      apply h1_left x.snd,
      rewrite <- contra,
      simp only [prod.mk.eta],
      exact h2,

      simp only [function.update_noteq s1],
      exact ih h1_right h2,
    }
  },
end


lemma function.update_list_not_mem
  {α β : Type}
  [decidable_eq α]
  (f : α → β)
  (l : list (α × β))
  (x : α)
  (h1 : x ∉ list.map prod.fst l) :
  function.update_list f l x = f x :=
begin
  induction l,
  case list.nil
  {
    unfold function.update_list,
  },
  case list.cons : hd tl ih
  {
    simp only [list.map, list.mem_cons_iff, list.mem_map, prod.exists,
      exists_and_distrib_right, exists_eq_right] at h1,
    push_neg at h1,
    cases h1,

    unfold function.update_list,
    simp only [function.update_noteq h1_left],
    apply ih,
    simp only [list.mem_map, prod.exists, exists_and_distrib_right, exists_eq_right, not_exists],
    exact h1_right,
  },
end


lemma function.update_list_mem_ext
  {α β : Type}
  [decidable_eq α]
  (f g : α → β)
  (l : list (α × β))
  (x : α)
  (h1 : x ∈ list.map prod.fst l) :
  function.update_list f l x = function.update_list g l x :=
begin
  induction l,
  case list.nil
  {
    simp only [list.map_nil, list.not_mem_nil] at h1,
    contradiction,
  },
  case list.cons : hd tl ih
  {
    simp only [list.map, list.mem_cons_iff] at h1,

    unfold function.update_list,
    by_cases c1 : x = hd.fst,
    {
      rewrite c1,
      simp only [function.update_same],
    },
    {
      simp only [function.update_noteq c1],
      cases h1,
      {
        contradiction,
      },
      {
        exact ih h1,
      }
    },
  },
end


lemma function.update_list_zip_mem_ext
  {α β : Type}
  [decidable_eq α]
  (f g : α → β)
  (l1 : list α)
  (l2 : list β)
  (x : α)
  (h1 : l1.length ≤ l2.length)
  (h2 : x ∈ l1) :
  function.update_list f (l1.zip l2) x =
    function.update_list g (l1.zip l2) x :=
begin
  have s1 : x ∈ list.map prod.fst (l1.zip l2),
  rewrite list.map_fst_zip l1 l2 h1,
  exact h2,

  exact function.update_list_mem_ext f g (list.zip l1 l2) x s1,
end


lemma function.update_list_zip_map_mem_ext
  {α β : Type}
  [decidable_eq α]
  (l1 l2 : list α)
  (f g h : α → β)
  (x : α)
  (h1 : l1.length ≤ l2.length)
  (h2 : x ∈ l1) :
  function.update_list f (l1.zip (list.map h l2)) x =
    function.update_list g (l1.zip (list.map h l2)) x :=
begin
  have s1 : l1.length ≤ (list.map h l2).length,
  simp only [list.length_map],
  exact h1,

  exact function.update_list_zip_mem_ext f g l1 (list.map h l2) x s1 h2,
end


lemma function.update_list_zip_map_mem_ext'
  {α β : Type}
  [decidable_eq α]
  (l1 l2 : list α)
  (f g h h' : α → β)
  (x : α)
  (h1 : ∀ (y : α), y ∈ l2 → h y = h' y)
  (h2 : l1.length ≤ l2.length)
  (h3 : x ∈ l1) :
  function.update_list f (l1.zip (list.map h l2)) x =
    function.update_list g (l1.zip (list.map h' l2)) x :=
begin
  have s1 : list.map h l2 = list.map h' l2,
  rewrite list.map_eq_map_iff,
  exact h1,

  rewrite s1,
  exact function.update_list_zip_map_mem_ext l1 l2 f g h' x h2 h3,
end


lemma function.update_list_zip_map_mem
  {α β : Type}
  [decidable_eq α]
  (f g : α → β)
  (l : list α)
  (x : α)
  (h1 : x ∈ l) :
  function.update_list f (l.zip (list.map g l)) x = g x :=
begin
  induction l,
  case list.nil
  {
    simp only [list.not_mem_nil] at h1,
    contradiction,
  },
  case list.cons : hd tl ih
  {
    simp only [list.mem_cons_iff] at h1,

    simp only [list.map, list.zip_cons_cons],
    unfold function.update_list,
    by_cases c1 : x = hd,
    {
      rewrite c1,
      simp only [function.update_same],
    },
    {
      cases h1,
      {
        contradiction,
      },
      {
        simp only [function.update_noteq c1],
        exact ih h1,
      }
    }
  },
end


lemma function.update_list_update
  {α β : Type}
  [decidable_eq α]
  (f g : α → β)
  (l1 l2 : list α)
  (v : α)
  (a : β)
  (x : α)
  (h1 : ∀ (y : α), y ∈ l2 → ¬ y = v)
  (h2 : l1.length ≤ l2.length)
  (h3 : x ∈ l1) :
  function.update_list g (l1.zip (list.map (function.update f v a) l2)) x =
    function.update_list f (l1.zip (list.map f l2)) x:=
begin
  have s1 : ∀ (y : α), y ∈ l2 → function.update f v a y = f y,
  intros y a1,
  exact function.update_noteq (h1 y a1) a f,

  exact function.update_list_zip_map_mem_ext' l1 l2 g f (function.update f v a) f x s1 h2 h3,
end


lemma function.update_list_nth_le_zip
  {α β : Type}
  [decidable_eq α]
  (f : α → β)
  (l1 : list α)
  (l2 : list β)
  (n : ℕ)
  (h1 : n < l1.length)
  (h2 : n < l2.length)
  (h3 : l1.nodup) :
  (function.update_list f (l1.zip l2)) (l1.nth_le n h1) = l2.nth_le n h2 :=
begin
  have s1 : (list.map prod.fst (l1.zip l2)).nodup,
  exact list.map_fst_zip_nodup l1 l2 h3,

  have s2 : (l1.nth_le n h1, l2.nth_le n h2) ∈ l1.zip l2,
  exact list.nth_le_mem_zip l1 l2 n h1 h2,

  exact function.update_list_mem f (l1.zip l2) (l1.nth_le n h1, l2.nth_le n h2) s1 s2,
end


lemma function.update_list_comp
  {α β γ : Type}
  [decidable_eq α]
  (f : α → β)
  (g : β → γ)
  (l : list (α × β)) :
  g ∘ function.update_list f l =
    function.update_list (g ∘ f) (list.map (fun (i : α × β), (i.fst, g i.snd)) l) :=
begin
  induction l,
  case list.nil
  {
    unfold list.map,
    unfold function.update_list,
  },
  case list.cons : hd tl ih
  {
    unfold list.map,
    unfold function.update_list,
    rewrite function.comp_update,
    rewrite ih,
  },
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

/-
(v, X) ∈ Γ if and only if v is not free in meta_var_ X.
not_free Γ v φ = v is not free in φ in the context Γ
-/
def not_free (Γ : list (var_name × meta_var_name)) (v : var_name) : formula → Prop
| (meta_var_ X) := (v, X) ∈ Γ
| (not_ φ) := not_free φ
| (imp_ φ ψ) := not_free φ ∧ not_free ψ
| (eq_ x y) := x ≠ v ∧ y ≠ v
| (forall_ x φ) := x = v ∨ not_free φ
| (def_ name args) := ∀ (x : var_name), x ∈ args → ¬ x = v


def formula.meta_var_set : formula → finset meta_var_name
| (meta_var_ X) := {X}
| (not_ φ) := φ.meta_var_set
| (imp_ φ ψ) := φ.meta_var_set ∪ ψ.meta_var_set
| (eq_ x y) := ∅
| (forall_ x φ) := φ.meta_var_set
| (def_ name args) := ∅


/-
True if and only if the formula has no meta variables and all the variables
that occur free in the formula are in the list.
-/
def formula.no_meta_var_and_all_free_in_list : formula → list var_name → Prop
| (meta_var_ X) S := false
| (not_ φ) S := φ.no_meta_var_and_all_free_in_list S
| (imp_ φ ψ) S := φ.no_meta_var_and_all_free_in_list S ∧ ψ.no_meta_var_and_all_free_in_list S
| (eq_ x y) S := x ∈ S ∧ y ∈ S
| (forall_ x φ) S := φ.no_meta_var_and_all_free_in_list (x :: S)
| (def_ name args) S := args ⊆ S


lemma no_meta_var_imp_meta_var_set_is_empty
  (φ : formula)
  (l : list var_name)
  (h1 : φ.no_meta_var_and_all_free_in_list l) :
  φ.meta_var_set = ∅ :=
begin
  induction φ generalizing l,
  case formula.meta_var_ : X l h1
  {
    unfold formula.no_meta_var_and_all_free_in_list at h1,
    contradiction,
  },
  case formula.not_ : φ φ_ih l h1
  {
    unfold formula.no_meta_var_and_all_free_in_list at h1,
    unfold formula.meta_var_set,
    exact φ_ih l h1,
  },
  case formula.imp_ : φ ψ φ_ih ψ_ih l h1
  {
    unfold formula.no_meta_var_and_all_free_in_list at h1,
    cases h1,
    unfold formula.meta_var_set,
    rewrite φ_ih l h1_left,
    rewrite ψ_ih l h1_right,
    exact finset.empty_union ∅,
  },
  case formula.eq_ : x y l h1
  {
    unfold formula.no_meta_var_and_all_free_in_list at h1,
    unfold formula.meta_var_set,
  },
  case formula.forall_ : x args φ_ih l h1
  {
    unfold formula.no_meta_var_and_all_free_in_list at h1,
    unfold formula.meta_var_set,
    exact φ_ih (x :: l) h1,
  },
  case formula.def_ : name args l h1
  {
    unfold formula.no_meta_var_and_all_free_in_list at h1,
    unfold formula.meta_var_set,
  },
end


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
(args : list var_name)
(q : formula)
(nodup : args.nodup)
(nf : q.no_meta_var_and_all_free_in_list args)


@[derive [has_append, has_mem definition_]]
def env : Type := list definition_


def env.nodup_ : env → Prop :=
  list.pairwise (fun (d1 d2 : definition_), d1.name = d2.name → d1.args.length = d2.args.length → false)


/-
True if and only if the formula is a meta variable or every definition in the
formula is defined in the environment.
-/
def formula.is_meta_var_or_all_def_in_env (E : env) : formula → Prop
| (meta_var_ _) := true
| (not_ φ) := φ.is_meta_var_or_all_def_in_env
| (imp_ φ ψ) := φ.is_meta_var_or_all_def_in_env ∧ ψ.is_meta_var_or_all_def_in_env
| (eq_ _ _) := true
| (forall_ _ φ) := φ.is_meta_var_or_all_def_in_env
| (def_ name args) :=
  ∃ (d : definition_), d ∈ E ∧ name = d.name ∧ args.length = d.args.length


def env.well_formed : env → Prop
| list.nil := true
| (d :: E) :=
    (∀ (d' : definition_), d' ∈ E → d.name = d'.name → d.args.length = d'.args.length → false)
    ∧ d.q.is_meta_var_or_all_def_in_env E
    ∧ env.well_formed E


lemma env_well_formed_imp_nodup
  (E : env)
  (h1 : E.well_formed) :
  E.nodup_ :=
begin
  induction E,
  case list.nil
  {
    unfold env.nodup_,
    simp only [list.pairwise.nil],
  },
  case list.cons : hd tl ih
  {
    unfold env.well_formed at h1,
    cases h1,
    cases h1_right,

    unfold env.nodup_ at ih,

    unfold env.nodup_,
    simp only [list.pairwise_cons],
    split,
    {
      exact h1_left,
    },
    {
      exact ih h1_right_right,
    },
  },
end


lemma is_meta_var_or_all_def_in_env_ext
  (E E' : env)
  (φ : formula)
  (h1 : ∃ (E1 : env), E' = E1 ++ E)
  (h2 : φ.is_meta_var_or_all_def_in_env E) :
  φ.is_meta_var_or_all_def_in_env E' :=
begin
  induction E generalizing φ,
  case list.nil : φ h2
  {
    induction φ,
    case formula.meta_var_ : X
    {
      unfold formula.is_meta_var_or_all_def_in_env,
    },
    case formula.not_ : φ φ_ih
    {
      unfold formula.is_meta_var_or_all_def_in_env at *,
      exact φ_ih h2,
    },
    case formula.imp_ : φ ψ φ_ih ψ_ih
    {
      unfold formula.is_meta_var_or_all_def_in_env at *,
      cases h2,
      split,
      {
        exact φ_ih h2_left,
      },
      {
        exact ψ_ih h2_right,
      }
    },
    case formula.eq_ : x y
    {
      unfold formula.is_meta_var_or_all_def_in_env,
    },
    case formula.forall_ : x φ φ_ih
    {
      unfold formula.is_meta_var_or_all_def_in_env at *,
      exact φ_ih h2,
    },
    case formula.def_ : name args
    {
      unfold formula.is_meta_var_or_all_def_in_env at h2,
      simp only [list.not_mem_nil, false_and, exists_false] at h2,
      contradiction,
    },
  },
  case list.cons : E_hd E_tl E_ih φ h2
  {
    induction φ,
    case formula.meta_var_ : X
    {
      unfold formula.is_meta_var_or_all_def_in_env,
    },
    case formula.not_ : φ φ_ih
    {
      unfold formula.is_meta_var_or_all_def_in_env at *,
      exact φ_ih h2,
    },
    case formula.imp_ : φ ψ φ_ih ψ_ih
    {
      unfold formula.is_meta_var_or_all_def_in_env at *,
      cases h2,
      split,
      {
        exact φ_ih h2_left,
      },
      {
        exact ψ_ih h2_right,
      }
    },
    case formula.eq_ : x y
    {
      unfold formula.is_meta_var_or_all_def_in_env,
    },
    case formula.forall_ : x φ φ_ih
    {
      unfold formula.is_meta_var_or_all_def_in_env at *,
      exact φ_ih h2,
    },
    case formula.def_ : name args
    {
      apply exists.elim h1,
      intros E1 h1_1,

      unfold formula.is_meta_var_or_all_def_in_env at h2,
      apply exists.elim h2,
      intros d h2_1,

      cases h2_1,
      cases h2_1_left,
      {
        unfold formula.is_meta_var_or_all_def_in_env,
        apply exists.intro E_hd,
        rewrite h1_1,
        split,
        {
          simp only [list.mem_append, list.mem_cons_iff, eq_self_iff_true, true_or, or_true],
        },
        {
          rewrite <- h2_1_left,
          exact h2_1_right,
        },
      },
      {
        have s1 : (∃ (E1 : env), (E' = (E1 ++ E_tl))),
        apply exists.intro (E1 ++ [E_hd]),
        simp only [list.append_assoc, list.singleton_append],
        exact h1_1,

        specialize E_ih s1,

        apply E_ih,

        unfold formula.is_meta_var_or_all_def_in_env,
        apply exists.intro d,
        split,
        {
          exact h2_1_left,
        },
        {
          exact h2_1_right,
        },
      }
    },
  },
end


lemma def_in_env_imp_is_meta_var_or_all_def_in_env
  (E : env)
  (d : definition_)
  (h1 : E.well_formed)
  (h2 : d ∈ E) :
  d.q.is_meta_var_or_all_def_in_env E :=
begin
  induction E,
  case list.nil
  {
    simp only [list.not_mem_nil] at h2,
    contradiction,
  },
  case list.cons : hd tl ih
  {
    unfold env.well_formed at h1,
    cases h1,
    cases h1_right,

    apply is_meta_var_or_all_def_in_env_ext tl (hd :: tl),
    {
      apply exists.intro [hd],
      simp only [list.singleton_append],
    },
    {
      cases h2,
      {
        rewrite h2,
        exact h1_right_left,
      },
      {
        exact ih h1_right_right h2,
      },
    },
  },
end


inductive is_conv (E : env) : formula → formula → Prop
| conv_refl (φ : formula) : is_conv φ φ

| conv_symm (φ φ' : formula) :
  is_conv φ φ' → is_conv φ' φ

| conv_trans (φ φ' φ'' : formula) :
  is_conv φ φ' → is_conv φ' φ'' → is_conv φ φ''

| conv_not (φ φ' : formula) :
  is_conv φ φ' → is_conv (not_ φ) (not_ φ')

| conv_imp (φ φ' ψ ψ' : formula) :
  is_conv φ φ' → is_conv ψ ψ' →  is_conv (imp_ φ ψ) (imp_ φ' ψ')

| conv_forall (x : var_name) (φ φ' : formula) :
  is_conv φ φ' → is_conv (forall_ x φ) (forall_ x φ')

| conv_unfold (d : definition_) (σ : instantiation) :
  d ∈ E →
  is_conv (def_ d.name (d.args.map σ.1)) (d.q.subst σ meta_var_)


def exists_ (x : var_name) (φ : formula) : formula := not_ (forall_ x (not_ φ))


-- (v, X) ∈ Γ if and only if v is not free in meta_var_ X.
-- Δ is a list of hypotheses.
inductive is_proof
  (E : env) :
  list (var_name × meta_var_name) → list formula → formula → Prop
| hyp (Γ : list (var_name × meta_var_name)) (Δ : list formula)
  (φ : formula) :
  φ.is_meta_var_or_all_def_in_env E →
  φ ∈ Δ → is_proof Γ Δ φ

| mp (Γ : list (var_name × meta_var_name)) (Δ : list formula)
  (φ ψ : formula) :
  is_proof Γ Δ φ → is_proof Γ Δ (φ.imp_ ψ) → is_proof Γ Δ ψ

| prop_1 (Γ : list (var_name × meta_var_name)) (Δ : list formula)
  (φ ψ : formula) :
  φ.is_meta_var_or_all_def_in_env E →
  ψ.is_meta_var_or_all_def_in_env E →
  is_proof Γ Δ (φ.imp_ (ψ.imp_ φ))

| prop_2 (Γ : list (var_name × meta_var_name)) (Δ : list formula)
  (φ ψ χ : formula) :
  φ.is_meta_var_or_all_def_in_env E →
  ψ.is_meta_var_or_all_def_in_env E →
  χ.is_meta_var_or_all_def_in_env E →
  is_proof Γ Δ ((φ.imp_ (ψ.imp_ χ)).imp_ ((φ.imp_ ψ).imp_ (φ.imp_ χ)))

| prop_3 (Γ : list (var_name × meta_var_name)) (Δ : list formula)
  (φ ψ : formula) :
  φ.is_meta_var_or_all_def_in_env E →
  ψ.is_meta_var_or_all_def_in_env E →
  is_proof Γ Δ (((not_ φ).imp_ (not_ ψ)).imp_ (ψ.imp_ φ))

| gen (Γ : list (var_name × meta_var_name)) (Δ : list formula)
  (φ : formula) (x : var_name) :
  is_proof Γ Δ φ → is_proof Γ Δ (forall_ x φ)

| pred_1 (Γ : list (var_name × meta_var_name)) (Δ : list formula)
  (φ ψ : formula) (x : var_name) :
  φ.is_meta_var_or_all_def_in_env E →
  ψ.is_meta_var_or_all_def_in_env E →
  is_proof Γ Δ ((forall_ x (φ.imp_ ψ)).imp_ ((forall_ x φ).imp_ (forall_ x ψ)))

| pred_2 (Γ : list (var_name × meta_var_name)) (Δ : list formula)
  (φ : formula) (x : var_name) :
  φ.is_meta_var_or_all_def_in_env E →
  not_free Γ x φ → is_proof Γ Δ (φ.imp_ (forall_ x φ))

| eq_1 (Γ : list (var_name × meta_var_name)) (Δ : list formula)
  (x y : var_name) :
  x ≠ y → is_proof Γ Δ (exists_ x (eq_ x y))

| eq_2 (Γ : list (var_name × meta_var_name)) (Δ : list formula)
  (x y z : var_name) :
  is_proof Γ Δ ((eq_ x y).imp_ ((eq_ x z).imp_ (eq_ y z)))

| thm (Γ Γ' : list (var_name × meta_var_name)) (Δ Δ' : list formula)
  (φ : formula) (σ : instantiation) (τ : meta_instantiation) :
  (∀ (X : meta_var_name), X ∈ φ.meta_var_set → (τ X).is_meta_var_or_all_def_in_env E) →
  (∀ (x : var_name) (X : meta_var_name), (x, X) ∈ Γ → not_free Γ' (σ.1 x) (τ X)) →
  (∀ (ψ : formula), ψ ∈ Δ → is_proof Γ' Δ' (ψ.subst σ τ)) →
  is_proof Γ Δ φ →
  is_proof Γ' Δ' (φ.subst σ τ)

| conv (Γ : list (var_name × meta_var_name)) (Δ : list formula)
  (φ φ' : formula) :
  φ'.is_meta_var_or_all_def_in_env E →
  is_proof Γ Δ φ → is_conv E φ φ' → is_proof Γ Δ φ'


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


lemma holds_valuation_ext
  {D : Type}
  (M : meta_valuation D)
  (E : env)
  (V1 V2 : valuation D)
  (φ : formula)
  (S : list var_name)
  (hf : φ.no_meta_var_and_all_free_in_list S)
  (h1 : ∀ (v : var_name), v ∈ S → V1 v = V2 v) :
  holds D M E φ V1 ↔ holds D M E φ V2 :=
begin
  induction E generalizing S φ V1 V2,
  case list.nil : S φ V1 V2 hf h1
  {
    induction φ generalizing S V1 V2,
    case formula.meta_var_ : X S V1 V2 hf h1
    {
      unfold formula.no_meta_var_and_all_free_in_list at hf,
      contradiction,
    },
    case formula.not_ : φ φ_ih S V1 V2 hf h1
    {
      unfold formula.no_meta_var_and_all_free_in_list at hf,
      simp only [holds_not],
      apply not_congr,
      exact φ_ih S V1 V2 hf h1,
    },
    case formula.imp_ : φ ψ φ_ih ψ_ih S V1 V2 hf h1
    {
      unfold formula.no_meta_var_and_all_free_in_list at hf,
      cases hf,
      simp only [holds_imp],
      apply imp_congr,
      {
        exact φ_ih S V1 V2 hf_left h1,
      },
      {
        exact ψ_ih S V1 V2 hf_right h1,
      }
    },
    case formula.eq_ : x y S V1 V2 hf h1
    {
      unfold formula.no_meta_var_and_all_free_in_list at hf,
      cases hf,
      simp only [holds_eq],
      rewrite h1 x hf_left,
      rewrite h1 y hf_right,
    },
    case formula.forall_ : x φ φ_ih S V1 V2 hf h1
    {
      unfold formula.no_meta_var_and_all_free_in_list at hf,
      simp only [holds_forall],
      apply forall_congr, intros a,
      apply φ_ih (x :: S),
      {
        exact hf,
      },
      {
        intros v a1,
        by_cases c1 : v = x,
        {
          rewrite c1,
          simp only [function.update_same],
        },
        {
          simp only [function.update_noteq c1],
          simp only [list.mem_cons_iff] at a1,
          cases a1,
          {
            contradiction,
          },
          {
            exact h1 v a1,
          }
        },
      },
    },
    case formula.def_ : name args S V1 V2 hf h1
    {
      unfold formula.no_meta_var_and_all_free_in_list at hf,
      simp only [holds_nil_def],
    },
  },
  case list.cons : E_hd E_tl E_ih S φ V1 V2 hf h1
  {
    induction φ generalizing S V1 V2,
    case formula.meta_var_ : X S V1 V2 hf h1
    {
      unfold formula.no_meta_var_and_all_free_in_list at hf,
      contradiction,
    },
    case formula.not_ : φ φ_ih S V1 V2 hf h1
    {
      unfold formula.no_meta_var_and_all_free_in_list at hf,
      simp only [holds_not],
      apply not_congr,
      exact φ_ih S V1 V2 hf h1,
    },
    case formula.imp_ : φ ψ φ_ih ψ_ih S V1 V2 hf h1
    {
      unfold formula.no_meta_var_and_all_free_in_list at hf,
      cases hf,
      simp only [holds_imp],
      apply imp_congr,
      {
        exact φ_ih S V1 V2 hf_left h1,
      },
      {
        exact ψ_ih S V1 V2 hf_right h1,
      }
    },
    case formula.eq_ : x y S V1 V2 hf h1
    {
      unfold formula.no_meta_var_and_all_free_in_list at hf,
      cases hf,
      simp only [holds_eq],
      rewrite h1 x hf_left,
      rewrite h1 y hf_right,
    },
    case formula.forall_ : x φ φ_ih S V1 V2 hf h1
    {
      unfold formula.no_meta_var_and_all_free_in_list at hf,
      simp only [holds_forall],
      apply forall_congr, intros a,
      apply φ_ih (x :: S),
      {
        exact hf,
      },
      {
        intros v a1,
        by_cases c1 : v = x,
        {
          rewrite c1,
          simp only [function.update_same],
        },
        {
          simp only [function.update_noteq c1],
          simp only [list.mem_cons_iff] at a1,
          cases a1,
          {
            contradiction,
          },
          {
            exact h1 v a1,
          }
        },
      },
    },
    case formula.def_ : name args S V1 V2 hf h1
    {
      unfold formula.no_meta_var_and_all_free_in_list at hf,
      simp only [holds_not_nil_def],
      split_ifs,
      {
        have s1 : ∀ (v : var_name), (v ∈ E_hd.args) →
          function.update_list V1 (E_hd.args.zip (list.map V1 args)) v =
            function.update_list V2 (E_hd.args.zip (list.map V2 args)) v,
        {
          intros v a1,
          apply function.update_list_zip_map_mem_ext',
          {
            intros y a2,
            apply h1,
            apply set.mem_of_subset_of_mem hf a2,
          },
          {
            cases h,
            rewrite h_right,
          },
          {
            exact a1,
          },
        },

        exact E_ih E_hd.args E_hd.q (function.update_list V1 (E_hd.args.zip (list.map V1 args)))
          (function.update_list V2 (E_hd.args.zip (list.map V2 args))) E_hd.nf s1,
      },
      {
        apply E_ih S,
        {
          unfold formula.no_meta_var_and_all_free_in_list,
          exact hf,
        },
        {
          exact h1,
        }
      },
    },
  },
end


lemma holds_meta_valuation_ext
  {D : Type}
  (M1 M2 : meta_valuation D)
  (E : env)
  (V : valuation D)
  (φ : formula)
  (h1 : ∀ (V' : valuation D) (X : meta_var_name), X ∈ φ.meta_var_set → (M1 X V' ↔ M2 X V')) :
  holds D M1 E φ V ↔ holds D M2 E φ V :=
begin
  induction E generalizing φ M1 M2 V,
  case list.nil : φ M1 M2 V h1
  {
    induction φ generalizing M1 M2 V,
    case formula.meta_var_ : X M1 M2 V h1
    {
      unfold formula.meta_var_set at h1,
      simp only [finset.mem_singleton] at h1,
      simp only [holds_meta_var],
      apply h1 V X,
      refl,
    },
    case formula.not_ : φ φ_ih M1 M2 V h1
    {
      unfold formula.meta_var_set at h1,
      simp only [holds_not],
      apply not_congr,
      exact φ_ih M1 M2 V h1,
    },
    case formula.imp_ : φ ψ φ_ih ψ_ih M1 M2 V h1
    {
      unfold formula.meta_var_set at h1,
      simp only [finset.mem_union] at h1,
      simp only [holds_imp],
      apply imp_congr,
      {
        apply φ_ih,
        intros V' X a1,
        apply h1,
        apply or.intro_left,
        exact a1,
      },
      {
        apply ψ_ih,
        intros V' X a1,
        apply h1,
        apply or.intro_right,
        exact a1,
      }
    },
    case formula.eq_ : x y M1 M2 V h1
    {
      simp only [holds_eq],
    },
    case formula.forall_ : x φ φ_ih M1 M2 V h1
    {
      unfold formula.meta_var_set at h1,
      simp only [holds_forall],
      apply forall_congr,
      intros a,
      exact φ_ih M1 M2 (function.update V x a) h1,
    },
    case formula.def_ : name args M1 M2 V h1
    {
      simp only [holds_nil_def],
    },
  },
  case list.cons : E_hd E_tl E_ih φ M1 M2 V h1
  {
    induction φ generalizing M1 M2 V,
    case formula.meta_var_ : X M1 M2 V h1
    {
      unfold formula.meta_var_set at h1,
      simp only [finset.mem_singleton] at h1,
      simp only [holds_meta_var],
      apply h1 V X,
      refl,
    },
    case formula.not_ : φ φ_ih M1 M2 V h1
    {
      unfold formula.meta_var_set at h1,
      simp only [holds_not],
      apply not_congr,
      exact φ_ih M1 M2 V h1,
    },
    case formula.imp_ : φ ψ φ_ih ψ_ih M1 M2 V h1
    {
      unfold formula.meta_var_set at h1,
      simp only [finset.mem_union] at h1,
      simp only [holds_imp],
      apply imp_congr,
      {
        apply φ_ih,
        intros V' X a1,
        apply h1,
        apply or.intro_left,
        exact a1,
      },
      {
        apply ψ_ih,
        intros V' X a1,
        apply h1,
        apply or.intro_right,
        exact a1,
      }
    },
    case formula.eq_ : x y M1 M2 V h1
    {
      simp only [holds_eq],
    },
    case formula.forall_ : x φ φ_ih M1 M2 V h1
    {
      unfold formula.meta_var_set at h1,
      simp only [holds_forall],
      apply forall_congr,
      intros a,
      exact φ_ih M1 M2 (function.update V x a) h1,
    },
    case formula.def_ : name args M1 M2 V h1
    {
      simp only [holds_not_nil_def],
      split_ifs,
      {
        have s1 : E_hd.q.meta_var_set = ∅,
        exact no_meta_var_imp_meta_var_set_is_empty E_hd.q E_hd.args E_hd.nf,

        apply E_ih,
        rewrite s1,
        simp only [finset.not_mem_empty, is_empty.forall_iff, forall_forall_const, implies_true_iff],
      },
      {
        apply E_ih,
        unfold formula.meta_var_set,
        simp only [finset.not_mem_empty, is_empty.forall_iff, forall_forall_const, implies_true_iff],
      }
    },
  },
end


lemma holds_meta_valuation_ext_no_meta_var
  {D : Type}
  (M1 M2 : meta_valuation D)
  (E : env)
  (V : valuation D)
  (φ : formula)
  (h1 : φ.meta_var_set = ∅) :
  holds D M1 E φ V ↔ holds D M2 E φ V :=
begin
  apply holds_meta_valuation_ext,
  rewrite h1,
  simp only [finset.not_mem_empty, is_empty.forall_iff, forall_forall_const, implies_true_iff],
end

--

lemma holds_env_ext
  {D : Type}
  (M : meta_valuation D)
  (E E' : env)
  (φ : formula)
  (V : valuation D)
  (h1 : ∃ (E1 : env), E' = E1 ++ E)
  (h2 : φ.is_meta_var_or_all_def_in_env E)
  (h3 : E'.nodup_) :
  holds D M E' φ V ↔ holds D M E φ V :=
begin
  induction φ generalizing V,
  case formula.meta_var_ : X V
  {
    simp only [holds_meta_var],
  },
  case formula.not_ : φ φ_ih V
  {
    unfold formula.is_meta_var_or_all_def_in_env at h2,
    simp only [holds_not],
    apply not_congr,
    exact φ_ih h2 V,
  },
  case formula.imp_ : φ ψ φ_ih ψ_ih V
  {
    unfold formula.is_meta_var_or_all_def_in_env at h2,
    cases h2,
    simp only [holds_imp],
    apply imp_congr,
    {
      exact φ_ih h2_left V,
    },
    {
      exact ψ_ih h2_right V,
    }
  },
  case formula.eq_ : x y V
  {
    simp only [holds_eq],
  },
  case formula.forall_ : x φ φ_ih V
  {
    unfold formula.is_meta_var_or_all_def_in_env at h2,
    simp only [holds_forall],
    apply forall_congr,
    intros a,
    exact φ_ih h2 (function.update V x a),
  },
  case formula.def_ : name args V
  {
    apply exists.elim h1,
    intros E1 h1_1,
    clear h1,

    unfold formula.is_meta_var_or_all_def_in_env at h2,
    apply exists.elim h2,
    intros a h2_1,
    cases h2_1,
    cases h2_1_right,
    clear h2,

    unfold env.nodup_ at h3,

    subst h1_1,

    induction E1,
    case list.nil
    {
      simp only [list.nil_append],
    },
    case list.cons : E1_hd E1_tl E1_ih
    {
      simp only [list.cons_append, list.pairwise_cons, list.mem_append] at h3,
      cases h3,

      simp only [list.cons_append, holds_not_nil_def],
      split_ifs,
      {
        cases h,

        exfalso,
        apply h3_left a,
        {
          apply or.intro_right,
          exact h2_1_left,
        },
        {
          rewrite <- h2_1_right_left,
          rewrite h_left,
        },
        {
          rewrite <- h2_1_right_right,
          rewrite h_right,
        },
      },
      {
        apply E1_ih,
        exact h3_right,
      }
    },
  },
end


lemma holds_subst
  {D : Type}
  (V : valuation D)
  (M : meta_valuation D)
  (E : env)
  (σ : instantiation)
  (σ' : var_name → var_name)
  (τ : meta_instantiation)
  (φ : formula)
  (h1 : φ.is_meta_var_or_all_def_in_env E)
  (h2 : σ.1 ∘ σ' = id ∧ σ' ∘ σ.1 = id) :
  holds D (fun (X' : meta_var_name) (V' : valuation D), holds D M E (τ X') (V' ∘ σ')) E φ (V ∘ σ.1) ↔
    holds D M E (φ.subst σ τ) V :=
begin
  induction φ generalizing V,
  case formula.meta_var_ : X V
  {
    cases h2,
    unfold formula.subst,
    simp only [holds_meta_var],
    rewrite function.comp.assoc,
    rewrite h2_left,
    rewrite function.comp.right_id,
  },
  case formula.not_ : φ φ_ih V
  {
    unfold formula.is_meta_var_or_all_def_in_env at h1,
    unfold formula.subst,
    simp only [holds_not],
    apply not_congr,
    exact φ_ih h1 V,
  },
  case formula.imp_ : φ ψ φ_ih ψ_ih V
  {
    unfold formula.is_meta_var_or_all_def_in_env at h1,
    cases h1,
    unfold formula.subst,
    simp only [holds_imp],
    apply imp_congr,
    {
      exact φ_ih h1_left V,
    },
    {
      exact ψ_ih h1_right V,
    }
  },
  case formula.eq_ : x y V
  {
    unfold formula.subst,
    simp only [holds_eq],
  },
  case formula.forall_ : x φ φ_ih V
  {
    unfold formula.is_meta_var_or_all_def_in_env at h1,
    cases h2,
    unfold formula.subst,
    simp only [holds_forall],
    apply forall_congr,
    intros a,
    rewrite <- aux_1 V σ.val σ' x a h2_right,
    exact φ_ih h1 (function.update V (σ.val x) a),
  },
  case formula.def_ : name args V
  {
    induction E,
    case list.nil
    {
      unfold formula.is_meta_var_or_all_def_in_env at h1,
      simp only [list.not_mem_nil, false_and, exists_false] at h1,
      contradiction,
    },
    case list.cons : E_hd E_tl E_ih
    {
      have s1 : E_hd.q.meta_var_set = ∅,
      exact no_meta_var_imp_meta_var_set_is_empty E_hd.q E_hd.args E_hd.nf,

      unfold formula.subst,
      simp only [holds_meta_var, holds_not_nil_def, list.length_map, list.map_map],
      split_ifs,
      {
        cases h,

        rewrite holds_valuation_ext
          M E_tl
          (function.update_list V (E_hd.args.zip (list.map (V ∘ σ.val) args)))
          (function.update_list (V ∘ σ.val) (E_hd.args.zip (list.map (V ∘ σ.val) args)))
          E_hd.q E_hd.args E_hd.nf,
        {
          apply holds_meta_valuation_ext,
          rewrite s1,
          simp only [finset.not_mem_empty, is_empty.forall_iff, forall_forall_const, implies_true_iff],
        },
        {
          intros v a1,
          apply function.update_list_zip_map_mem_ext,
          {
            rewrite h_right,
          },
          {
            exact a1,
          }
        },
      },
      {
        unfold formula.is_meta_var_or_all_def_in_env at h1,
        apply exists.elim h1,
        intros d h1_1,
        clear h1,
        cases h1_1,
        simp only [list.mem_cons_iff] at h1_1_left,

        cases h1_1_left,
        {
          rewrite <- h1_1_left at h,
          exfalso,
          apply h,
          exact h1_1_right,
        },
        {
          unfold formula.subst at E_ih,
          rewrite <- E_ih,
          apply holds_meta_valuation_ext,
          unfold formula.meta_var_set,
          simp only [finset.not_mem_empty, is_empty.forall_iff, forall_forall_const, implies_true_iff],

          unfold formula.is_meta_var_or_all_def_in_env,
          apply exists.intro d,
          split,
          {
            exact h1_1_left,
          },
          {
            exact h1_1_right,
          }
        },
      },
    },
  },
end


-- changing v does not cause the value of φ to change

def is_not_free
  (D : Type)
  (M : meta_valuation D)
  (E : env)
  (v : var_name)
  (φ : formula) : Prop :=
  ∀ (V : valuation D) (a : D), holds D M E φ V ↔ holds D M E φ (function.update V v a)


lemma is_not_free_equiv
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
    intros a1 V V' a2,
    rewrite <- aux_3 V V' v a2,
    exact a1 V (V' v),
  },
  {
    intros a1 V a,
    apply a1,
    intros a' a2,
    simp only [function.update_noteq a2],
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
  induction E generalizing φ,
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
      {
        exact φ_ih H_left V a,
      },
      {
        exact ψ_ih H_right V a,
      },
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
          exact φ_ih H (function.update V x a') a,
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
      {
        exact φ_ih H_left V a,
      },
      {
        exact ψ_ih H_right V a,
      },
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
          exact φ_ih H (function.update V x a') a,
        }
      }
    },
    case formula.def_ : name args
    {
      unfold not_free at *,
      unfold is_not_free at *,
      simp only [holds_not_nil_def, holds_meta_var] at *,
      specialize E_ih nf,
      intros V a,
      split_ifs,
      {
        apply holds_valuation_ext M E_tl _ _ E_hd.q E_hd.args,
        {
          exact E_hd.nf,
        },
        {
          intros x h1,
          symmetry,
          apply function.update_list_update V (function.update V v a),
          {
            exact H,
          },
          {
            cases h,
            rewrite h_right,
          },
          {
            exact h1,
          },
        },
      },
      {
        apply E_ih,
        unfold not_free,
        exact H,
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
  rewrite aux_2 V σ' σ.1 v a left right,
  apply not_free_imp_is_not_free M E Γ',
  {
    exact H v X h1,
  },
  {
    intros X' h2,
    exact nf (σ.1 v) X' h2,
  },
end


lemma lem_3
  (E : env)
  (σ : instantiation)
  (τ : meta_instantiation)
  (φ : formula)
  (h1 : φ.is_meta_var_or_all_def_in_env E)
  (h2 : ∀ (X : meta_var_name), X ∈ φ.meta_var_set → (τ X).is_meta_var_or_all_def_in_env E) :
  (φ.subst σ τ).is_meta_var_or_all_def_in_env E :=
begin
  induction φ,
  case formula.meta_var_ : X
  {
    unfold formula.subst,
    apply h2,
    unfold formula.meta_var_set,
    simp only [finset.mem_singleton],
  },
  case formula.not_ : φ φ_ih
  {
    unfold formula.subst,
    unfold formula.is_meta_var_or_all_def_in_env at *,
    exact φ_ih h1 h2,
  },
  case formula.imp_ : φ ψ φ_ih ψ_ih
  {
    unfold formula.subst,
    unfold formula.is_meta_var_or_all_def_in_env at *,
    cases h1,
    unfold formula.meta_var_set at h2,
    simp only [finset.mem_union] at h2,
    split,
    {
      apply φ_ih h1_left,
      intros x a1,
      apply h2,
      apply or.intro_left,
      exact a1,
    },
    {
      apply ψ_ih h1_right,
      intros x a1,
      apply h2,
      apply or.intro_right,
      exact a1,
    },
  },
  case formula.eq_ : x y
  {
    unfold formula.subst,
  },
  case formula.forall_ : x φ φ_ih
  {
    unfold formula.subst,
    unfold formula.is_meta_var_or_all_def_in_env at *,
    unfold formula.meta_var_set at h2,
    apply φ_ih h1 h2,
  },
  case formula.def_ : name args
  {
    unfold formula.subst,
    unfold formula.is_meta_var_or_all_def_in_env at *,
    unfold formula.meta_var_set at h2,
    simp only [list.length_map],
    exact h1,
  },
end


lemma lem_4
  (E : env)
  (Γ : list (var_name × meta_var_name))
  (Δ : list formula)
  (φ : formula)
  (H : is_proof E Γ Δ φ) :
  φ.is_meta_var_or_all_def_in_env E :=
begin
  induction H,
  case is_proof.hyp : H_Γ H_Δ H_φ H_ᾰ H_ᾰ_1
  {
    exact H_ᾰ,
  },
  case is_proof.mp : H_Γ H_Δ H_φ H_ψ H_ᾰ H_ᾰ_1 H_ih_ᾰ H_ih_ᾰ_1
  {
    unfold formula.is_meta_var_or_all_def_in_env at *,
    cases H_ih_ᾰ_1,
    exact H_ih_ᾰ_1_right,
  },
  case is_proof.prop_1 : H_Γ H_Δ H_φ H_ψ H_ᾰ H_ᾰ_1
  {
    unfold formula.is_meta_var_or_all_def_in_env at *,
    repeat {split <|> assumption},
  },
  case is_proof.prop_2 : H_Γ H_Δ H_φ H_ψ H_χ H_ᾰ H_ᾰ_1 H_ᾰ_2
  {
    unfold formula.is_meta_var_or_all_def_in_env at *,
    repeat {split <|> assumption},
  },
  case is_proof.prop_3 : H_Γ H_Δ H_φ H_ψ H_ᾰ H_ᾰ_1
  {
    unfold formula.is_meta_var_or_all_def_in_env at *,
    repeat {split <|> assumption},
  },
  case is_proof.gen : H_Γ H_Δ H_φ H_x H_ᾰ H_ih
  {
    unfold formula.is_meta_var_or_all_def_in_env at *,
    assumption,
  },
  case is_proof.pred_1 : H_Γ H_Δ H_φ H_ψ H_x H_ᾰ H_ᾰ_1
  {
    unfold formula.is_meta_var_or_all_def_in_env at *,
    repeat {split <|> assumption},
  },
  case is_proof.pred_2 : H_Γ H_Δ H_φ H_x H_ᾰ H_ᾰ_1
  {
    unfold formula.is_meta_var_or_all_def_in_env at *,
    repeat {split <|> assumption},
  },
  case is_proof.eq_1 : H_Γ H_Δ H_x H_y H_ᾰ
  {
    unfold exists_,
  },
  case is_proof.eq_2 : H_Γ H_Δ H_x H_y H_z
  {
    unfold formula.is_meta_var_or_all_def_in_env at *,
    simp only [and_self],
  },
  case is_proof.thm : H_Γ H_Γ' H_Δ H_Δ' H_φ H_σ H_τ H_ᾰ H_ᾰ_1 H_ᾰ_2 H_ᾰ_3 H_ih_ᾰ H_ih_ᾰ_1
  {
    apply lem_3 E H_σ,
    assumption,
    apply H_ᾰ,
  },
  case is_proof.conv : H_Γ H_Δ H_φ H_φ' H_ᾰ H_ᾰ_1 H_ᾰ_2 H_ih
  {
    assumption,
  },
end


lemma lem_5
  (E : env)
  (σ : instantiation)
  (τ : meta_instantiation)
  (φ : formula)
  (h1 : (φ.subst σ τ).is_meta_var_or_all_def_in_env E) :
  φ.is_meta_var_or_all_def_in_env E :=
begin
  induction φ,
  case formula.meta_var_ : X
  {
    unfold formula.subst at h1,
  },
  case formula.not_ : φ φ_ih
  {
    unfold formula.subst at h1,
    unfold formula.is_meta_var_or_all_def_in_env at *,
    exact φ_ih h1,
  },
  case formula.imp_ : φ ψ φ_ih ψ_ih
  {
    unfold formula.subst at h1,
    cases h1,
    unfold formula.is_meta_var_or_all_def_in_env at *,
    split,
    {
      exact φ_ih h1_left,
    },
    {
      exact ψ_ih h1_right,
    },
  },
  case formula.eq_ : x y
  {
    unfold formula.subst at h1,
  },
  case formula.forall_ : x φ φ_ih
  {
    unfold formula.subst at h1,
    unfold formula.is_meta_var_or_all_def_in_env at *,
    exact φ_ih h1,
  },
  case formula.def_ : name args
  {
    unfold formula.subst at h1,
    unfold formula.is_meta_var_or_all_def_in_env at *,
    simp only [list.length_map] at h1,
    exact h1,
  },
end


lemma lem_6
  (E : env)
  (σ : instantiation)
  (τ : meta_instantiation)
  (φ : formula)
  (X : meta_var_name)
  (h1 : (φ.subst σ τ).is_meta_var_or_all_def_in_env E)
  (h2 : X ∈ φ.meta_var_set) :
  (τ X).is_meta_var_or_all_def_in_env E :=
begin
  induction φ,
  case formula.meta_var_ : X'
  {
    unfold formula.subst at *,
    unfold formula.meta_var_set at h2,
    simp only [finset.mem_singleton] at h2,
    subst h2,
    exact h1,
  },
  case formula.not_ : φ φ_ih
  {
    unfold formula.subst at *,
    unfold formula.meta_var_set at h2,
    unfold formula.is_meta_var_or_all_def_in_env at *,
    exact φ_ih h1 h2,
  },
  case formula.imp_ : φ ψ φ_ih ψ_ih
  {
    unfold formula.subst at *,
    unfold formula.meta_var_set at h2,
    unfold formula.is_meta_var_or_all_def_in_env at *,
    cases h1,
    simp only [finset.mem_union] at h2,
    cases h2,
    {
      exact φ_ih h1_left h2,
    },
    {
      exact ψ_ih h1_right h2,
    }
  },
  case formula.eq_ : x y
  {
    unfold formula.meta_var_set at h2,
    simp only [finset.not_mem_empty] at h2,
    contradiction,
  },
  case formula.forall_ : x φ φ_ih
  {
    unfold formula.subst at *,
    unfold formula.meta_var_set at h2,
    unfold formula.is_meta_var_or_all_def_in_env at *,
    exact φ_ih h1 h2,
  },
  case formula.def_ : name args
  {
    unfold formula.meta_var_set at h2,
    simp only [finset.not_mem_empty] at h2,
    contradiction,
  },
end


lemma lem_8
  {D : Type}
  (M : meta_valuation D)
  (E : env)
  (d : definition_)
  (args : list var_name)
  (V : valuation D)
  (h1 : E.well_formed)
  (h2 : d ∈ E)
  (h3 : args.length = d.args.length) :
  holds D M E (def_ d.name args) V ↔
    holds D M E d.q (function.update_list V (list.zip d.args (list.map V args))) :=
begin
  induction E,
  case list.nil
  {
    simp only [list.not_mem_nil] at h2,
    contradiction,
  },
  case list.cons : hd tl ih
  {
    simp only [list.mem_cons_iff] at h2,

    simp only [holds_not_nil_def],
    split_ifs,
    {
      cases h,

      cases h2,
      {
        rewrite h2,
        rewrite <- holds_env_ext,
        {
          apply exists.intro [hd],
          simp only [list.singleton_append],
        },
        {
          unfold env.well_formed at h1,
          cases h1,
          cases h1_right,
          exact h1_right_left,
        },
        {
          apply env_well_formed_imp_nodup,
          exact h1,
        }
      },
      {
        unfold env.well_formed at h1,
        simp only [list.pairwise_cons] at h1,
        cases h1,

        specialize h1_left d h2,
        exfalso,
        apply h1_left,
        rewrite h_left,
        rewrite <- h3,
        rewrite h_right,
      },
    },
    {
      cases h2,
      {
        subst h2,
        simp only [eq_self_iff_true, true_and] at h,
        exfalso,
        apply h,
        exact h3,
      },
      {
        have s1 : env.well_formed tl,
        unfold env.well_formed at h1,
        cases h1,
        cases h1_right,
        exact h1_right_right,

        specialize ih s1 h2,
        rewrite ih,

        rewrite <- holds_env_ext,
        {
          apply exists.intro [hd],
          simp only [list.singleton_append],
        },
        {
          unfold env.well_formed at h1,
          cases h1,
          cases h1_right,
          apply def_in_env_imp_is_meta_var_or_all_def_in_env,
          exact h1_right_right,
          exact h2,
        },
        {
          apply env_well_formed_imp_nodup,
          exact h1,
        }
      }
    }
  },
end


lemma lem_7
  (D : Type)
  (M : meta_valuation D)
  (E : env)
  (φ φ' : formula)
  (V : valuation D)
  (h1 : E.well_formed)
  (h2 : is_conv E φ φ') :
  holds D M E φ V ↔ holds D M E φ' V :=
begin
  induction h2 generalizing V,
  case is_conv.conv_refl : h2 V
  {
    refl,
  },
  case is_conv.conv_symm : φ φ' h2 ih V
  {
    symmetry,
    apply ih,
  },
  case is_conv.conv_trans : h2_φ h2_φ' h2_φ'' h2_ᾰ h2_ᾰ_1 h2_ih_ᾰ h2_ih_ᾰ_1 V
  {
    transitivity (holds D M E h2_φ' V),
    exact h2_ih_ᾰ V,
    exact h2_ih_ᾰ_1 V,
  },
  case is_conv.conv_not : h2_φ h2_φ' h2_ᾰ h2_ih V
  {
    simp only [holds_not],
    apply not_congr,
    exact h2_ih V,
  },
  case is_conv.conv_imp : h2_φ h2_φ' h2_ψ h2_ψ' h2_ᾰ h2_ᾰ_1 h2_ih_ᾰ h2_ih_ᾰ_1 V
  {
    simp only [holds_imp],
    apply imp_congr,
    {
      exact h2_ih_ᾰ V,
    },
    {
      exact h2_ih_ᾰ_1 V,
    }
  },
  case is_conv.conv_forall : h2_x h2_φ h2_φ' h2_ᾰ h2_ih V
  {
    simp only [holds_forall],
    apply forall_congr, intros a,
    exact h2_ih (function.update V h2_x a),
  },
  case is_conv.conv_unfold : d σ h2 V
  {
    obtain ⟨σ', left, right⟩ := σ.2,

    rewrite lem_8 M E d (list.map σ.val d.args) V h1 h2,

    rewrite <- holds_subst V M E σ σ' meta_var_ d.q,

    have s1 : holds D (fun (X' : meta_var_name) (V' : valuation D), holds D M E (meta_var_ X') (V' ∘ σ')) E d.q (V ∘ σ.val)
      ↔ holds D M E d.q (V ∘ σ.val),
    apply holds_meta_valuation_ext_no_meta_var,
    apply no_meta_var_imp_meta_var_set_is_empty d.q d.args d.nf,

    rewrite s1,
    apply holds_valuation_ext M E
    (function.update_list V (d.args.zip (list.map V (list.map σ.val d.args)))) (V ∘ σ.val)
    d.q d.args d.nf,
    simp only [list.map_map, function.comp_app],
    intros v h3,
    apply function.update_list_zip_map_mem, exact h3,
    apply def_in_env_imp_is_meta_var_or_all_def_in_env, exact h1, exact h2,
    split,
    exact left,
    exact right,
    simp only [list.length_map],
  },
end


example
  (D : Type)
  (M : meta_valuation D)
  (E : env)
  (Γ : list (var_name × meta_var_name))
  (Δ : list formula)
  (φ : formula)
  (H : is_proof E Γ Δ φ)
  (h1 : E.well_formed)
  (nf : ∀ v X, (v, X) ∈ Γ → is_not_free D M E v (meta_var_ X))
  (hyp : ∀ (ψ ∈ Δ) (V : valuation D), holds D M E ψ V) :
  ∀ (V : valuation D), holds D M E φ V :=
begin
  induction H generalizing M,
  case is_proof.hyp : H_Γ H_Δ H_φ H_ᾰ H_ᾰ_1 M nf hyp
  {
    intros V,
    exact hyp H_φ H_ᾰ_1 V,
  },
  case is_proof.mp : H_Γ H_Δ H_φ H_ψ H_ᾰ H_ᾰ_1 H_ih_ᾰ H_ih_ᾰ_1 M nf hyp
  {
    intros V,
    simp only [holds_imp] at *,
    apply H_ih_ᾰ_1 M nf hyp,
    apply H_ih_ᾰ M nf hyp,
  },
  case is_proof.prop_1 : H_Γ H_Δ H_φ H_ψ H_ᾰ H_ᾰ_1 M nf hyp
  {
    simp only [holds_imp],
    intros V h1 h2, exact h1,
  },
  case is_proof.prop_2 : H_Γ H_Δ H_φ H_ψ H_χ H_ᾰ H_ᾰ_1 H_ᾰ_2 M nf hyp
  {
    simp only [holds_imp],
    intros V h1 h2 h3,
    apply h1, exact h3, apply h2, exact h3,
  },
  case is_proof.prop_3 : H_Γ H_Δ H_φ H_ψ H_ᾰ H_ᾰ_1 M nf hyp
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
  case is_proof.pred_1 : H_Γ H_Δ H_φ H_ψ H_x H_ᾰ H_ᾰ_1 M nf hyp
  {
    simp only [holds_imp, holds_forall],
    intros V h1 h2 a,
    apply h1,
    apply h2,
  },
  case is_proof.pred_2 : H_Γ H_Δ H_φ H_x H_ᾰ H_ᾰ_1 M nf hyp
  {
    have s1 : is_not_free D M E H_x H_φ,
    apply not_free_imp_is_not_free M E H_Γ H_x H_φ H_ᾰ_1,
    intros X h2, apply nf, exact h2,

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
  case is_proof.thm : Γ Γ' Δ Δ' φ σ τ H1 H2 H3 H4 IH1 IH2 M nf hyp
  {
    dsimp only at *,
    obtain ⟨σ', left, right⟩ := σ.2,
    have s1 : E.nodup_,
    apply env_well_formed_imp_nodup E h1,
    have IH1' := fun φ b M d e V, (holds_subst _ _ _ _ _ _ _ _ (and.intro left right)).2 (IH1 φ b M d e V),
    {
      intros V,
      rewrite <- holds_subst _ _ _ _ _ _ _ _ (and.intro left right),
      {
        apply IH2,
        {
          intros v X a1,
          exact lem_2 M E Γ_1 Γ' σ σ' τ left right nf H2 v X a1,
        },
        {
          intros ψ a1 V',
          specialize IH1' ψ a1 M nf hyp (V' ∘ σ'),
          rewrite function.comp.assoc at IH1',
          rewrite right at IH1',
          simp only [function.comp.right_id] at IH1',
          exact IH1',
        },
      },
      {
        exact lem_4 E Γ_1 Δ_1 φ_1 H4,
      },
    },
    {
      specialize H3 φ b,
      apply lem_5 E σ τ,
      exact lem_4 E Γ' Δ' (formula.subst σ τ φ) H3,
    },
  },
  case is_proof.conv : Γ Δ φ φ' H1 H2 H3 ih M nf hyp
  {
    intros V,
    rewrite <- lem_7 D M E φ φ',
    apply ih,
    exact nf,
    exact hyp,
    exact h1,
    exact H3,
  },
end
