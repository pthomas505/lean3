import data.hash_map
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


def list.option_to_option_list {α : Type} [decidable_eq α] (l : list (option α)) : option (list α) :=
  if none ∈ l then none else some l.reduce_option


-- Syntax


namespace mm0


abbreviation var_name := string
abbreviation meta_var_name := string
abbreviation pred_name := string
abbreviation def_name := string


@[derive decidable_eq]
inductive formula : Type
| meta_var_ : meta_var_name → formula
| pred_ : pred_name → list var_name → formula
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
| (pred_ name args) := v ∉ args
| (not_ φ) := not_free φ
| (imp_ φ ψ) := not_free φ ∧ not_free ψ
| (eq_ x y) := x ≠ v ∧ y ≠ v
| (forall_ x φ) := x = v ∨ not_free φ
| (def_ name args) := v ∉ args


instance
  (Γ : list (var_name × meta_var_name))
  (v : var_name)
  (φ : formula) :
  decidable (not_free Γ v φ) :=
begin
  induction φ; unfold not_free; resetI; apply_instance,
end


def formula.meta_var_set : formula → finset meta_var_name
| (meta_var_ X) := {X}
| (pred_ name args) := ∅
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
| (pred_ name args) S := args ⊆ S
| (not_ φ) S := φ.no_meta_var_and_all_free_in_list S
| (imp_ φ ψ) S := φ.no_meta_var_and_all_free_in_list S ∧ ψ.no_meta_var_and_all_free_in_list S
| (eq_ x y) S := x ∈ S ∧ y ∈ S
| (forall_ x φ) S := φ.no_meta_var_and_all_free_in_list (x :: S)
| (def_ name args) S := args ⊆ S


example
  (φ : formula)
  (S T : list var_name)
  (h1 : S ⊆ T)
  (h2 : φ.no_meta_var_and_all_free_in_list S) :
  φ.no_meta_var_and_all_free_in_list T :=
begin
  induction φ generalizing S T,
  case formula.meta_var_ : X S T h1 h2
  {
    unfold formula.no_meta_var_and_all_free_in_list at h2,
    contradiction,
  },
  case formula.pred_ : name args S T h1 h2
  {
    unfold formula.no_meta_var_and_all_free_in_list at h2,
    unfold formula.no_meta_var_and_all_free_in_list,
    exact set.subset.trans h2 h1,
  },
  case formula.not_ : φ φ_ih S T h1 h2
  {
    unfold formula.no_meta_var_and_all_free_in_list at h2,
    unfold formula.no_meta_var_and_all_free_in_list,
    exact φ_ih S T h1 h2,
  },
  case formula.imp_ : φ ψ φ_ih ψ_ih S T h1 h2
  {
    unfold formula.no_meta_var_and_all_free_in_list at h2,
    cases h2,
    unfold formula.no_meta_var_and_all_free_in_list,
    split,
    {
      exact φ_ih S T h1 h2_left,
    },
    {
      exact ψ_ih S T h1 h2_right,
    }
  },
  case formula.eq_ : x y S T h1 h2
  {
    unfold formula.no_meta_var_and_all_free_in_list at h2,
    cases h2,
    unfold formula.no_meta_var_and_all_free_in_list,
    split,
    {
      exact h1 h2_left,
    },
    {
      exact h1 h2_right,
    }
  },
  case formula.forall_ : x φ φ_ih S T h1 h2
  {
    unfold formula.no_meta_var_and_all_free_in_list at h2,
    unfold formula.no_meta_var_and_all_free_in_list,
    apply φ_ih (x :: S),
    {
      exact list.cons_subset_cons x h1,
    },
    {
      exact h2
    }
  },
  case formula.def_ : name args S T h1 h2
  {
    unfold formula.no_meta_var_and_all_free_in_list at h2,
    unfold formula.no_meta_var_and_all_free_in_list,
    exact set.subset.trans h2 h1,
  },
end


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
  case formula.pred_ : name args l h1
  {
    unfold formula.meta_var_set,
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
| (pred_ name args) := pred_ name (list.map σ.1 args)
| (not_ φ) := not_ φ.subst
| (imp_ φ ψ) := imp_ φ.subst ψ.subst
| (eq_ x y) := eq_ (σ.1 x) (σ.1 y)
| (forall_ x φ) := forall_ (σ.1 x) φ.subst
| (def_ name args) := def_ name (list.map σ.1 args)


@[derive decidable_eq]
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
| (pred_ name args) := true
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
    case formula.pred_ : name args
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
    case formula.pred_ : name args
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
        have s1 : ∃ (E1 : env), E' = E1 ++ E_tl,
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
  is_conv φ φ' → is_conv ψ ψ' → is_conv (imp_ φ ψ) (imp_ φ' ψ')

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
  y ≠ x → is_proof Γ Δ (exists_ x (eq_ x y))

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


def pred_interpretation (D : Type) : Type := pred_name → list D → Prop

def valuation (D : Type) : Type := var_name → D
def meta_valuation (D : Type) : Type := meta_var_name → valuation D → Prop

/-
def holds
  (D : Type)
  (P : pred_interpretation D)
  (M : meta_valuation D) :
  env → formula → valuation D → Prop
| E (meta_var_ X) V := M X V
| E (pred_ name args) V := P name (list.map V args)
| E (not_ φ) V := ¬ holds E φ V
| E (imp_ φ ψ) V := holds E φ V → holds E ψ V
| E (eq_ x y) V := V x = V y
| E (forall_ x φ) V := ∀ (a : D), holds E φ (function.update V x a)
| [] (def_ _ _) V := false
| (d :: E) (def_ name args) V :=
    if name = d.name ∧ args.length = d.args.length
    then holds E d.q (function.update_list V (list.zip d.args (list.map V args)))
    else holds E (def_ name args) V
-/

/-
Lean is unable to determine that the above definition of holds is decreasing,
so it needs to be broken into this pair of mutually recursive definitions.
-/

def holds'
  (D : Type)
  (P : pred_interpretation D)
  (M : meta_valuation D)
  (holds : formula → valuation D → Prop)
  (d : option definition_) :
  formula → valuation D → Prop
| (meta_var_ X) V := M X V
| (pred_ name args) V := P name (list.map V args)
| (not_ φ) V := ¬ holds' φ V
| (imp_ φ ψ) V := holds' φ V → holds' ψ V
| (eq_ x y) V := V x = V y
| (forall_ x φ) V := ∀ (a : D), holds' φ (function.update V x a)
| (def_ name args) V :=
    option.elim
      false
      (
        fun (d : definition_),
        if name = d.name ∧ args.length = d.args.length
        then holds d.q (function.update_list V (list.zip d.args (list.map V args)))
        else holds (def_ name args) V
      )
      d

def holds
  (D : Type)
  (P : pred_interpretation D)
  (M : meta_valuation D) :
  env → formula → valuation D → Prop
| [] := holds' D P M (fun _ _, false) option.none
| (d :: E) := holds' D P M (holds E) (option.some d)


/-
These lemmas demonstrate that the pair of mutually recursive definitions
is equivalent to the version that Lean is unable to determine is decreasing.
-/

@[simp]
lemma holds_meta_var
  {D : Type}
  (P : pred_interpretation D)
  (M : meta_valuation D)
  (E : env)
  (X : meta_var_name)
  (V : valuation D) :
  holds D P M E (meta_var_ X) V ↔ M X V := by {cases E; refl}

@[simp]
lemma holds_pred
  {D : Type}
  (P : pred_interpretation D)
  (M : meta_valuation D)
  (E : env)
  (name : pred_name)
  (args : list var_name)
  (V : valuation D) :
  holds D P M E (pred_ name args) V ↔ P name (list.map V args) := by {cases E; refl}

@[simp]
lemma holds_not
  {D : Type}
  (P : pred_interpretation D)
  (M : meta_valuation D)
  (E : env)
  (φ : formula)
  (V : valuation D) :
  holds D P M E (not_ φ) V ↔ ¬ holds D P M E φ V := by {cases E; refl}

@[simp]
lemma holds_imp
  {D : Type}
  (P : pred_interpretation D)
  (M : meta_valuation D)
  (E : env)
  (φ ψ : formula)
  (V : valuation D) :
  holds D P M E (imp_ φ ψ) V ↔ holds D P M E φ V → holds D P M E ψ V := by {cases E; refl}

@[simp]
lemma holds_eq
  {D : Type}
  (P : pred_interpretation D)
  (M : meta_valuation D)
  (E : env)
  (x y : var_name)
  (V : valuation D) :
  holds D P M E (eq_ x y) V ↔ V x = V y := by {cases E; refl}

@[simp]
lemma holds_forall
  {D : Type}
  (P : pred_interpretation D)
  (M : meta_valuation D)
  (E : env)
  (φ : formula)
  (x : var_name)
  (V : valuation D) :
  holds D P M E (forall_ x φ) V ↔ ∀ (a : D), holds D P M E φ (function.update V x a) := by {cases E; refl}

@[simp]
lemma holds_nil_def
  {D : Type}
  (P : pred_interpretation D)
  (M : meta_valuation D)
  (name : def_name)
  (args : list var_name)
  (V : valuation D) :
  holds D P M [] (def_ name args) V ↔ false := by {refl}

@[simp]
lemma holds_not_nil_def
  {D : Type}
  (P : pred_interpretation D)
  (M : meta_valuation D)
  (d : definition_)
  (E : env)
  (name : def_name)
  (args : list var_name)
  (V : valuation D) :
  holds D P M (d :: E) (def_ name args) V ↔
    if name = d.name ∧ args.length = d.args.length
    then holds D P M E d.q (function.update_list V (list.zip d.args (list.map V args)))
    else holds D P M E (def_ name args) V :=
begin
  unfold holds, unfold holds', simp only [option.elim],
end


lemma holds_valuation_ext
  {D : Type}
  (P : pred_interpretation D)
  (M : meta_valuation D)
  (E : env)
  (V1 V2 : valuation D)
  (φ : formula)
  (S : list var_name)
  (h1 : φ.no_meta_var_and_all_free_in_list S)
  (h2 : ∀ (v : var_name), v ∈ S → V1 v = V2 v) :
  holds D P M E φ V1 ↔ holds D P M E φ V2 :=
begin
  induction E generalizing S φ V1 V2,
  case list.nil : S φ V1 V2 h1 h2
  {
    induction φ generalizing S V1 V2,
    case formula.meta_var_ : X S V1 V2 h1 h2
    {
      unfold formula.no_meta_var_and_all_free_in_list at h1,
      contradiction,
    },
    case formula.pred_ : name args S V1 V2 h1 h2
    {
      unfold formula.no_meta_var_and_all_free_in_list at h1,
      simp only [holds_pred],

      have s1 : list.map V1 args = list.map V2 args,
      apply list.map_congr,
      intros x a1,
      apply h2,
      exact h1 a1,

      rewrite s1,
    },
    case formula.not_ : φ φ_ih S V1 V2 h1 h2
    {
      unfold formula.no_meta_var_and_all_free_in_list at h1,
      simp only [holds_not],
      apply not_congr,
      exact φ_ih S V1 V2 h1 h2,
    },
    case formula.imp_ : φ ψ φ_ih ψ_ih S V1 V2 h1 h2
    {
      unfold formula.no_meta_var_and_all_free_in_list at h1,
      cases h1,
      simp only [holds_imp],
      apply imp_congr,
      {
        exact φ_ih S V1 V2 h1_left h2,
      },
      {
        exact ψ_ih S V1 V2 h1_right h2,
      }
    },
    case formula.eq_ : x y S V1 V2 h1 h2
    {
      unfold formula.no_meta_var_and_all_free_in_list at h1,
      cases h1,
      simp only [holds_eq],
      rewrite h2 x h1_left,
      rewrite h2 y h1_right,
    },
    case formula.forall_ : x φ φ_ih S V1 V2 h1 h2
    {
      unfold formula.no_meta_var_and_all_free_in_list at h1,
      simp only [holds_forall],
      apply forall_congr, intros a,
      apply φ_ih (x :: S),
      {
        exact h1,
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
            exact h2 v a1,
          }
        },
      },
    },
    case formula.def_ : name args S V1 V2 h1 h2
    {
      unfold formula.no_meta_var_and_all_free_in_list at h1,
      simp only [holds_nil_def],
    },
  },
  case list.cons : E_hd E_tl E_ih S φ V1 V2 h1 h2
  {
    induction φ generalizing S V1 V2,
    case formula.meta_var_ : X S V1 V2 h1 h2
    {
      unfold formula.no_meta_var_and_all_free_in_list at h1,
      contradiction,
    },
    case formula.pred_ : name args S V1 V2 h1 h2
    {
      unfold formula.no_meta_var_and_all_free_in_list at h1,
      simp only [holds_pred],

      have s1 : list.map V1 args = list.map V2 args,
      apply list.map_congr,
      intros x a1,
      apply h2,
      exact h1 a1,

      rewrite s1,
    },
    case formula.not_ : φ φ_ih S V1 V2 h1 h2
    {
      unfold formula.no_meta_var_and_all_free_in_list at h1,
      simp only [holds_not],
      apply not_congr,
      exact φ_ih S V1 V2 h1 h2,
    },
    case formula.imp_ : φ ψ φ_ih ψ_ih S V1 V2 h1 h2
    {
      unfold formula.no_meta_var_and_all_free_in_list at h1,
      cases h1,
      simp only [holds_imp],
      apply imp_congr,
      {
        exact φ_ih S V1 V2 h1_left h2,
      },
      {
        exact ψ_ih S V1 V2 h1_right h2,
      }
    },
    case formula.eq_ : x y S V1 V2 h1 h2
    {
      unfold formula.no_meta_var_and_all_free_in_list at h1,
      cases h1,
      simp only [holds_eq],
      rewrite h2 x h1_left,
      rewrite h2 y h1_right,
    },
    case formula.forall_ : x φ φ_ih S V1 V2 h1 h2
    {
      unfold formula.no_meta_var_and_all_free_in_list at h1,
      simp only [holds_forall],
      apply forall_congr, intros a,
      apply φ_ih (x :: S),
      {
        exact h1,
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
            exact h2 v a1,
          }
        },
      },
    },
    case formula.def_ : name args S V1 V2 h1 h2
    {
      unfold formula.no_meta_var_and_all_free_in_list at h1,
      simp only [holds_not_nil_def],
      split_ifs,
      {
        have s1 : ∀ (v : var_name), v ∈ E_hd.args →
          function.update_list V1 (E_hd.args.zip (list.map V1 args)) v =
            function.update_list V2 (E_hd.args.zip (list.map V2 args)) v,
        {
          intros v a1,
          apply function.update_list_zip_map_mem_ext',
          {
            intros y a2,
            apply h2,
            apply set.mem_of_subset_of_mem h1 a2,
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
          exact h1,
        },
        {
          exact h2,
        }
      },
    },
  },
end


lemma holds_meta_valuation_ext
  {D : Type}
  (P : pred_interpretation D)
  (M1 M2 : meta_valuation D)
  (E : env)
  (V : valuation D)
  (φ : formula)
  (h1 : ∀ (V' : valuation D) (X : meta_var_name), X ∈ φ.meta_var_set → (M1 X V' ↔ M2 X V')) :
  holds D P M1 E φ V ↔ holds D P M2 E φ V :=
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
    case formula.pred_ : name args M1 M2 V h1
    {
      simp only [holds_pred],
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
    case formula.pred_ : name args M1 M2 V h1
    {
      simp only [holds_pred],
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
  (P : pred_interpretation D)
  (M1 M2 : meta_valuation D)
  (E : env)
  (V : valuation D)
  (φ : formula)
  (h1 : φ.meta_var_set = ∅) :
  holds D P M1 E φ V ↔ holds D P M2 E φ V :=
begin
  apply holds_meta_valuation_ext,
  rewrite h1,
  simp only [finset.not_mem_empty, is_empty.forall_iff, forall_forall_const, implies_true_iff],
end


lemma holds_def_imp_ex_def
  {D : Type}
  (P : pred_interpretation D)
  (M : meta_valuation D)
  (E : env)
  (V : valuation D)
  (name : var_name)
  (args : list var_name)
  (h1 : holds D P M E (def_ name args) V) :
  ∃ (d : definition_), d ∈ E ∧ name = d.name ∧ args.length = d.args.length :=
begin
  induction E,
  case list.nil
  {
    simp only [holds_nil_def] at h1,
    contradiction,
  },
  case list.cons : E_hd E_tl E_ih
  {
    simp only [holds_not_nil_def] at h1,
    split_ifs at h1,
    {
      apply exists.intro E_hd,
      simp only [list.mem_cons_iff, eq_self_iff_true, true_or, true_and],
      exact h,
    },
    {
      specialize E_ih h1,
      apply exists.elim E_ih,
      intros d E_ih_1,
      cases E_ih_1,
      apply exists.intro d,
      split,
      {
        simp only [list.mem_cons_iff],
        apply or.intro_right,
        exact E_ih_1_left,
      },
      {
        exact E_ih_1_right,
      }
    }
  },
end


example
  {D : Type}
  (P : pred_interpretation D)
  (M : meta_valuation D)
  (E E' : env)
  (name : var_name)
  (args : list var_name)
  (V : valuation D)
  (h1 : ∃ (E1 : env), E' = E1 ++ E)
  (h2 : E'.nodup_)
  (h3 : holds D P M E (def_ name args) V) :
  holds D P M E' (def_ name args) V :=
begin
  apply exists.elim h1,
  intros E1 h1_1,
  clear h1,

  unfold env.nodup_ at h2,

  subst h1_1,

  induction E1,
  case list.nil
  {
    simp only [list.nil_append],
    exact h3,
  },
  case list.cons : E1_hd E1_tl E1_ih
  {
    simp only [list.cons_append, list.pairwise_cons, list.mem_append] at h2,
    cases h2,

    specialize E1_ih h2_right,

    simp only [list.cons_append, holds_not_nil_def],
    split_ifs,
    {
      have s1 : ∃ (d : definition_), d ∈ (E1_tl ++ E) ∧ name = d.name ∧ args.length = d.args.length,
      exact holds_def_imp_ex_def P M (E1_tl ++ E) V name args E1_ih,

      apply exists.elim s1,
      intros d s1_1,
      cases s1_1,
      simp only [list.mem_append] at s1_1_left,
      cases s1_1_right,

      cases h,
      exfalso,
      apply h2_left d s1_1_left,
      {
        rewrite <- h_left,
        exact s1_1_right_left,
      },
      {
        rewrite <- h_right,
        exact s1_1_right_right,
      }
    },
    {
      exact E1_ih,
    }
  },
end


lemma holds_env_ext
  {D : Type}
  (P : pred_interpretation D)
  (M : meta_valuation D)
  (E E' : env)
  (φ : formula)
  (V : valuation D)
  (h1 : ∃ (E1 : env), E' = E1 ++ E)
  (h2 : φ.is_meta_var_or_all_def_in_env E)
  (h3 : E'.nodup_) :
  holds D P M E' φ V ↔ holds D P M E φ V :=
begin
  induction φ generalizing V,
  case formula.meta_var_ : X V
  {
    simp only [holds_meta_var],
  },
  case formula.pred_ : name args V
  {
    simp only [holds_pred],
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
        exact E1_ih h3_right,
      }
    },
  },
end


lemma holds_subst
  {D : Type}
  (P : pred_interpretation D)
  (M : meta_valuation D)
  (E : env)
  (σ : instantiation)
  (σ' : var_name → var_name)
  (τ : meta_instantiation)
  (φ : formula)
  (V : valuation D)
  (h1 : φ.is_meta_var_or_all_def_in_env E)
  (h2 : σ.1 ∘ σ' = id ∧ σ' ∘ σ.1 = id) :
  holds D P (fun (X' : meta_var_name) (V' : valuation D), holds D P M E (τ X') (V' ∘ σ')) E φ (V ∘ σ.1) ↔
    holds D P M E (φ.subst σ τ) V :=
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
  case formula.pred_ : name args V
  {
    unfold formula.subst,
    simp only [holds_pred, list.map_map],
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
          P M E_tl
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


/-
  Changing v does not cause the value of φ to change.
-/
def is_not_free
  (D : Type)
  (P : pred_interpretation D)
  (M : meta_valuation D)
  (E : env)
  (v : var_name)
  (φ : formula) : Prop :=
  ∀ (V : valuation D) (a : D), holds D P M E φ V ↔ holds D P M E φ (function.update V v a)


example
  {D : Type}
  (P : pred_interpretation D)
  (M : meta_valuation D)
  (E : env)
  (v : var_name)
  (φ : formula) :
  is_not_free D P M E v φ ↔
    ∀ (V V' : valuation D),
      (∀ (y : var_name), (¬ y = v) → (V y = V' y)) →
        (holds D P M E φ V ↔ holds D P M E φ V') :=
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
  (P : pred_interpretation D)
  (M : meta_valuation D)
  (E : env)
  (Γ : list (var_name × meta_var_name))
  (v : var_name)
  (φ : formula)
  (h1 : not_free Γ v φ)
  (h2 : ∀ (X : meta_var_name), (v, X) ∈ Γ → is_not_free D P M E v (meta_var_ X)) :
  is_not_free D P M E v φ :=
begin
  induction φ,
  case formula.meta_var_ : X
  {
    unfold not_free at h1,
    exact h2 X h1,
  },
  case formula.pred_ : name args
  {
    unfold not_free at h1,

    unfold is_not_free at *,

    simp only [holds_pred],
    intros V a,

    have s1 : list.map (function.update V v a) args = list.map V args,
    apply list.map_congr,
    intros x a1,
    have s2 : ¬ x = v,
    intros contra,
    apply h1,
    rewrite <- contra,
    exact a1,
    simp only [function.update_noteq s2],

    rewrite s1,
  },
  case formula.not_ : φ φ_ih
  {
    unfold not_free at h1,

    unfold is_not_free at *,

    simp only [holds_not],
    intros V a,
    apply not_congr,
    exact φ_ih h1 V a,
  },
  case formula.imp_ : φ ψ φ_ih ψ_ih
  {
    unfold not_free at h1,
    cases h1,

    unfold is_not_free at *,

    simp only [holds_imp],
    intros V a,
    apply imp_congr,
    {
      exact φ_ih h1_left V a,
    },
    {
      exact ψ_ih h1_right V a,
    },
  },
  case formula.eq_ : x y
  {
    unfold not_free at h1,
    cases h1,

    unfold is_not_free at *,

    simp only [holds_eq],
    intros V a,
    simp only [function.update_noteq h1_left, function.update_noteq h1_right],
  },
  case formula.forall_ : x φ φ_ih
  {
    unfold not_free at h1,

    unfold is_not_free at *,

    simp only [holds_forall],
    intros V a,
    apply forall_congr,
    intros a',
    cases h1,
    {
      rewrite h1,
      simp only [function.update_idem],
    },
    {
      by_cases c1 : v = x,
      {
        rewrite c1,
        simp only [function.update_idem],
      },
      {
        simp only [function.update_comm c1],
        exact φ_ih h1 (function.update V x a') a,
      }
    }
  },
  case formula.def_ : name args
  {
    induction E,
    case list.nil
    {
      intros V a,
      simp only [holds_nil_def],
    },
    case list.cons : E_hd E_tl E_ih
    {
      unfold is_not_free at *,

      simp only [holds_not_nil_def, holds_meta_var] at *,
      intros V a,
      split_ifs,
      {
        apply holds_valuation_ext P M E_tl
          (function.update_list V (E_hd.args.zip (list.map V args)))
          (function.update_list (function.update V v a) (E_hd.args.zip (list.map (function.update V v a) args)))
          E_hd.q E_hd.args E_hd.nf,
        {
          intros v' a1,
          symmetry,
          apply function.update_list_update V (function.update V v a),
          {
            unfold not_free at h1,
            intros y a2 contra,
            apply h1,
            rewrite <- contra,
            exact a2,
          },
          {
            cases h,
            rewrite h_right,
          },
          {
            exact a1,
          },
        },
      },
      {
        exact E_ih h2 V a,
      }
    },
  },
end


lemma lem_1
  {D : Type}
  (P : pred_interpretation D)
  (M : meta_valuation D)
  (E : env)
  (Γ Γ' : list (var_name × meta_var_name))
  (σ : instantiation)
  (σ' : var_name → var_name)
  (τ : meta_instantiation)
  (h1 : σ.1 ∘ σ' = id ∧ σ' ∘ σ.1 = id)
  (h2 : ∀ (v : var_name) (X : meta_var_name), (v, X) ∈ Γ' → is_not_free D P M E v (meta_var_ X))
  (h3 : ∀ (v : var_name) (X : meta_var_name), (v, X) ∈ Γ → not_free Γ' (σ.1 v) (τ X)) :
  ∀ (v : var_name) (X : meta_var_name),
    (v, X) ∈ Γ →
      is_not_free D P (fun (X : meta_var_name) (V' : valuation D), holds D P M E (τ X) (V' ∘ σ'))
        E v (meta_var_ X) :=
begin
  cases h1,
  intros v X a1,
  unfold is_not_free,
  simp only [holds_meta_var],
  intros V a,
  rewrite aux_2 V σ' σ.1 v a h1_left h1_right,
  apply not_free_imp_is_not_free P M E Γ',
  {
    exact h3 v X a1,
  },
  {
    intros X' a2,
    exact h2 (σ.1 v) X' a2,
  },
end


lemma lem_2_a
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
    unfold formula.meta_var_set at h2,
    simp only [finset.mem_singleton, forall_eq] at h2,

    unfold formula.subst,
    exact h2,
  },
  case formula.pred_ : name args
  {
    unfold formula.subst,
  },
  case formula.not_ : φ φ_ih
  {
    unfold formula.is_meta_var_or_all_def_in_env at h1,
    unfold formula.meta_var_set at h2,

    unfold formula.subst,
    unfold formula.is_meta_var_or_all_def_in_env,
    exact φ_ih h1 h2,
  },
  case formula.imp_ : φ ψ φ_ih ψ_ih
  {
    unfold formula.is_meta_var_or_all_def_in_env at h1,
    cases h1,

    unfold formula.meta_var_set at h2,
    simp only [finset.mem_union] at h2,

    unfold formula.subst,
    unfold formula.is_meta_var_or_all_def_in_env,
    split,
    {
      apply φ_ih h1_left,
      intros X a1,
      apply h2,
      apply or.intro_left,
      exact a1,
    },
    {
      apply ψ_ih h1_right,
      intros X a1,
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
    unfold formula.is_meta_var_or_all_def_in_env at h1,
    unfold formula.meta_var_set at h2,

    unfold formula.subst,
    unfold formula.is_meta_var_or_all_def_in_env,
    exact φ_ih h1 h2,
  },
  case formula.def_ : name args
  {
    unfold formula.is_meta_var_or_all_def_in_env at h1,

    unfold formula.subst,
    unfold formula.is_meta_var_or_all_def_in_env,
    simp only [list.length_map],
    exact h1,
  },
end


lemma lem_2_b
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
  case formula.pred_ : name args
  {
    unfold formula.subst at h1,
  },
  case formula.not_ : φ φ_ih
  {
    unfold formula.subst at h1,
    unfold formula.is_meta_var_or_all_def_in_env at h1,

    unfold formula.is_meta_var_or_all_def_in_env,
    exact φ_ih h1,
  },
  case formula.imp_ : φ ψ φ_ih ψ_ih
  {
    unfold formula.subst at h1,
    unfold formula.is_meta_var_or_all_def_in_env at h1,

    cases h1,
    unfold formula.is_meta_var_or_all_def_in_env,
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
    unfold formula.is_meta_var_or_all_def_in_env at h1,

    unfold formula.is_meta_var_or_all_def_in_env,
    exact φ_ih h1,
  },
  case formula.def_ : name args
  {
    unfold formula.subst at h1,
    unfold formula.is_meta_var_or_all_def_in_env at h1,
    simp only [list.length_map] at h1,

    unfold formula.is_meta_var_or_all_def_in_env,
    exact h1,
  },
end


lemma lem_3
  (E : env)
  (Γ : list (var_name × meta_var_name))
  (Δ : list formula)
  (φ : formula)
  (h1 : is_proof E Γ Δ φ) :
  φ.is_meta_var_or_all_def_in_env E :=
begin
  induction h1,
  case is_proof.hyp : h1_Γ h1_Δ h1_φ h1_1 h1_2
  {
    exact h1_1,
  },
  case is_proof.mp : h1_Γ h1_Δ h1_φ h1_ψ h1_1 h1_2 h1_ih_1 h1_ih_2
  {
    unfold formula.is_meta_var_or_all_def_in_env at h1_ih_2,
    cases h1_ih_2,
    exact h1_ih_2_right,
  },
  case is_proof.prop_1 : h1_Γ h1_Δ h1_φ h1_ψ h1_1 h1_2
  {
    unfold formula.is_meta_var_or_all_def_in_env at *,
    repeat {split <|> assumption},
  },
  case is_proof.prop_2 : h1_Γ h1_Δ h1_φ h1_ψ h1_χ h1_1 h1_2 h1_3
  {
    unfold formula.is_meta_var_or_all_def_in_env at *,
    repeat {split <|> assumption},
  },
  case is_proof.prop_3 : h1_Γ h1_Δ h1_φ h1_ψ h1_1 h1_2
  {
    unfold formula.is_meta_var_or_all_def_in_env at *,
    repeat {split <|> assumption},
  },
  case is_proof.gen : h1_Γ h1_Δ h1_φ h1_x h1_1 h1_ih
  {
    unfold formula.is_meta_var_or_all_def_in_env at *,
    repeat {split <|> assumption},
  },
  case is_proof.pred_1 : h1_Γ h1_Δ h1_φ h1_ψ h1_x h1_1 h1_2
  {
    unfold formula.is_meta_var_or_all_def_in_env at *,
    repeat {split <|> assumption},
  },
  case is_proof.pred_2 : h1_Γ h1_Δ h1_φ h1_x h1_1 h1_2
  {
    unfold formula.is_meta_var_or_all_def_in_env at *,
    repeat {split <|> assumption},
  },
  case is_proof.eq_1 : h1_Γ h1_Δ h1_x h1_y h1_1
  {
    unfold exists_,
  },
  case is_proof.eq_2 : h1_Γ h1_Δ h1_x h1_y h1_z
  {
    unfold formula.is_meta_var_or_all_def_in_env,
    simp only [and_self],
  },
  case is_proof.thm : h1_Γ h1_Γ' h1_Δ h1_Δ' h1_φ h1_σ h1_τ h1_1 h1_2 h1_3 h1_4 h1_ih_1 h1_ih_2
  {
    exact lem_2_a E h1_σ h1_τ h1_φ h1_ih_2 h1_1,
  },
  case is_proof.conv : h1_Γ h1_Δ h1_φ h1_φ' h1_1 h1_2 h1_3 h1_ih
  {
    exact h1_1,
  },
end


lemma lem_4
  {D : Type}
  (P : pred_interpretation D)
  (M : meta_valuation D)
  (E : env)
  (d : definition_)
  (name : var_name)
  (args : list var_name)
  (V : valuation D)
  (h1 : E.well_formed)
  (h2 : d ∈ E)
  (h3 : name = d.name ∧ args.length = d.args.length) :
  holds D P M E d.q (function.update_list V (list.zip d.args (list.map V args)))
    ↔ holds D P M E (def_ name args) V :=
begin
  induction E,
  case list.nil
  {
    simp only [list.not_mem_nil] at h2,
    contradiction,
  },
  case list.cons : hd tl ih
  {
    have s1 : env.nodup_ (hd :: tl),
    exact env_well_formed_imp_nodup (hd :: tl) h1,

    unfold env.well_formed at h1,
    cases h1,
    cases h1_right,

    simp only [list.mem_cons_iff] at h2,

    have s2 : ∃ (E1 : env), ((hd :: tl) = (E1 ++ tl)),
    apply exists.intro [hd],
    simp only [list.singleton_append, eq_self_iff_true, and_self],

    simp only [holds_not_nil_def],
    split_ifs,
    {
      cases h2,
      {
        rewrite h2,
        exact holds_env_ext P M tl (hd :: tl) hd.q (function.update_list V (hd.args.zip (list.map V args))) s2 h1_right_left s1,
      },
      {
        cases h,

        cases h3,

        have s3 : hd.name = d.name,
        rewrite <- h_left,
        exact h3_left,

        have s4 : hd.args.length = d.args.length,
        rewrite <- h_right,
        exact h3_right,

        exfalso,
        exact h1_left d h2 s3 s4,
      },
    },
    {
      cases h2,
      {
        simp only [not_and] at h,
        rewrite <- h2 at h,

        cases h3,

        exfalso,
        exact h h3_left h3_right,
      },
      {
        specialize ih h1_right_right h2,
        rewrite <- ih,

        exact holds_env_ext P M tl (hd :: tl) d.q (function.update_list V (d.args.zip (list.map V args))) s2
  (def_in_env_imp_is_meta_var_or_all_def_in_env tl d h1_right_right h2)
  s1,
      }
    }
  },
end


lemma holds_conv
  {D : Type}
  (P : pred_interpretation D)
  (M : meta_valuation D)
  (E : env)
  (φ φ' : formula)
  (V : valuation D)
  (h1 : E.well_formed)
  (h2 : is_conv E φ φ') :
  holds D P M E φ V ↔ holds D P M E φ' V :=
begin
  induction h2 generalizing V,
  case is_conv.conv_refl : h2 V
  {
    refl,
  },
  case is_conv.conv_symm : h2_φ h2_φ' h2_1 h2_ih V
  {
    symmetry,
    exact h2_ih V,
  },
  case is_conv.conv_trans : h2_φ h2_φ' h2_φ'' h2_1 h2_2 h2_ih_1 h2_ih_2 V
  {
    transitivity (holds D P M E h2_φ' V),
    exact h2_ih_1 V,
    exact h2_ih_2 V,
  },
  case is_conv.conv_not : h2_φ h2_φ' h2_1 h2_ih V
  {
    simp only [holds_not],
    apply not_congr,
    exact h2_ih V,
  },
  case is_conv.conv_imp : h2_φ h2_φ' h2_ψ h2_ψ' h2_1 h2_2 h2_ih_1 h2_ih_2 V
  {
    simp only [holds_imp],
    apply imp_congr,
    {
      exact h2_ih_1 V,
    },
    {
      exact h2_ih_2 V,
    }
  },
  case is_conv.conv_forall : h2_x h2_φ h2_φ' h2_1 h2_ih V
  {
    simp only [holds_forall],
    apply forall_congr,
    intros a,
    exact h2_ih (function.update V h2_x a),
  },
  case is_conv.conv_unfold : d σ h2 V
  {
    obtain ⟨σ', a1⟩ := σ.2,

    have s1 : formula.is_meta_var_or_all_def_in_env E d.q,
    exact def_in_env_imp_is_meta_var_or_all_def_in_env E d h1 h2,

    rewrite <- holds_subst P M E σ σ' meta_var_ d.q V s1 a1,

    have s2 : ((d.name = d.name) ∧ ((list.map σ.val d.args).length = d.args.length)),
    simp only [eq_self_iff_true, list.length_map, and_self],

    rewrite <- lem_4 P M E d d.name (list.map σ.val d.args) V h1 h2 s2,

    have s3 : d.q.meta_var_set = ∅,
    exact no_meta_var_imp_meta_var_set_is_empty d.q d.args d.nf,

    rewrite holds_meta_valuation_ext_no_meta_var P
      (fun (X' : meta_var_name) (V' : valuation D), holds D P M E (meta_var_ X') (V' ∘ σ'))
        M E (V ∘ σ.val) d.q s3,

    apply holds_valuation_ext P M E (function.update_list V (d.args.zip (list.map V (list.map σ.val d.args))))
      (V ∘ σ.val) d.q d.args d.nf,
    intros v a2,
    simp only [list.map_map, function.comp_app],
    exact function.update_list_zip_map_mem V (V ∘ σ.val) d.args v a2,
  },
end


theorem holds_is_proof
  {D : Type}
  (P : pred_interpretation D)
  (M : meta_valuation D)
  (E : env)
  (Γ : list (var_name × meta_var_name))
  (Δ : list formula)
  (φ : formula)
  (h1 : is_proof E Γ Δ φ)
  (h2 : E.well_formed)
  (nf : ∀ (v : var_name) (X : meta_var_name), (v, X) ∈ Γ → is_not_free D P M E v (meta_var_ X))
  (hyp : ∀ (ψ : formula) (V : valuation D), ψ ∈ Δ → holds D P M E ψ V) :
  ∀ (V : valuation D), holds D P M E φ V :=
begin
  induction h1 generalizing M,
  case is_proof.hyp : h1_Γ h1_Δ h1_φ h1_1 h1_2 M nf hyp
  {
    intros V,
    exact hyp h1_φ V h1_2,
  },
  case is_proof.mp : h1_Γ h1_Δ h1_φ h1_ψ h1_1 h1_2 h1_ih_1 h1_ih_2 M nf hyp
  {
    simp only [holds_imp] at h1_ih_2,
    intros V,
    exact h1_ih_2 M nf hyp V (h1_ih_1 M nf hyp V),
  },
  case is_proof.prop_1 : h1_Γ h1_Δ h1_φ h1_ψ h1_1 h1_2 M nf hyp
  {
    simp only [holds_imp],
    intros V a1 a2,
    exact a1,
  },
  case is_proof.prop_2 : h1_Γ h1_Δ h1_φ h1_ψ h1_χ h1_1 h1_2 h1_3 M nf hyp
  {
    simp only [holds_imp],
    intros V a1 a2 a3,
    exact a1 a3 (a2 a3),
  },
  case is_proof.prop_3 : h1_Γ h1_Δ h1_φ h1_ψ h1_1 h1_2 M nf hyp
  {
    simp only [holds_imp, holds_not],
    intros V a1 a2,
    by_contradiction contra,
    exact a1 contra a2,
  },
  case is_proof.gen : h1_Γ h1_Δ h1_φ h1_x h1_1 h1_ih M nf hyp
  {
    simp only [holds_forall],
    intros V a,
    exact h1_ih M nf hyp (function.update V h1_x a),
  },
  case is_proof.pred_1 : h1_Γ h1_Δ h1_φ h1_ψ h1_x h1_1 h1_2 M nf hyp
  {
    simp only [holds_imp, holds_forall],
    intros V a1 a2 a,
    exact a1 a (a2 a),
  },
  case is_proof.pred_2 : h1_Γ h1_Δ h1_φ h1_x h1_1 h1_2 M nf hyp
  {
    have s1 : is_not_free D P M E h1_x h1_φ,
    exact not_free_imp_is_not_free P M E h1_Γ h1_x h1_φ h1_2 (nf h1_x),

    simp only [holds_imp, holds_forall],
    intros V a1 a,
    unfold is_not_free at s1,
    rewrite <- s1 V a,
    exact a1,
  },
  case is_proof.eq_1 : h1_Γ h1_Δ h1_x h1_y h1_1 M nf hyp
  {
    unfold exists_,
    simp only [holds_not, holds_forall, holds_eq, function.update_same, not_forall, not_not],
    intros V,
    apply exists.intro (V h1_y),
    symmetry,
    exact function.update_noteq h1_1 (V h1_y) V,
  },
  case is_proof.eq_2 : h1_Γ h1_Δ h1_x h1_y h1_z M nf hyp
  {
    simp only [holds_imp, holds_eq],
    intros V a1 a2,
    transitivity V h1_x,
    {
      symmetry,
      exact a1,
    },
    {
      exact a2,
    }
  },
  case is_proof.thm : h1_Γ h1_Γ' h1_Δ h1_Δ' h1_φ h1_σ h1_τ h1_1 h1_2 h1_3 h1_4 h1_ih_1 h1_ih_2 M nf hyp
  {
    obtain ⟨σ', a1⟩ := h1_σ.2,

    dsimp only at h1_ih_1,

    have s1 : formula.is_meta_var_or_all_def_in_env E h1_φ,
    exact lem_3 E h1_Γ h1_Δ h1_φ h1_4,

    intros V,
    rewrite <- holds_subst P M E h1_σ σ' h1_τ h1_φ V s1 a1,

    apply h1_ih_2,
    {
      intros v X a2,
      exact lem_1 P M E h1_Γ h1_Γ' h1_σ σ' h1_τ a1 nf h1_2 v X a2,
    },
    {
      intros ψ V' a2,

      have s2 : formula.is_meta_var_or_all_def_in_env E ψ,
      apply lem_2_b E h1_σ h1_τ,
      apply lem_3 E h1_Γ' h1_Δ' (formula.subst h1_σ h1_τ ψ),
      exact h1_3 ψ a2,

      have s3 : ∀ (V'' : valuation D),
        holds D P (fun (X' : meta_var_name) (V' : valuation D), holds D P M E (h1_τ X') (V' ∘ σ'))
          E ψ (V'' ∘ h1_σ.val),
      intros V'',
      rewrite holds_subst P M E h1_σ σ' h1_τ ψ V'' s2 a1,
      exact h1_ih_1 ψ a2 M nf hyp V'',

      specialize s3 (V' ∘ σ'),
      rewrite function.comp.assoc at s3,
      rewrite a1.right at s3,
      simp only [function.comp.right_id] at s3,
      exact s3,
    },
  },
  case is_proof.conv : h1_Γ h1_Δ h1_φ h1_φ' h1_1 h1_2 h1_3 h1_ih M nf hyp
  {
    intros V,

    have s1 : holds D P M E h1_φ V,
    exact h1_ih M nf hyp V,

    rewrite <- holds_conv P M E h1_φ h1_φ' V h2 h1_3,
    exact s1,
  },
end


-- Proof Checker


def definition_map : Type := hash_map string (fun _, definition_)


def formula.is_meta_var_or_all_def_in_map (m : definition_map) : formula → option unit

| (meta_var_ _) := some ()

| (pred_ _ _) := some ()

| (not_ φ) := φ.is_meta_var_or_all_def_in_map

| (imp_ φ ψ) := do
  φ.is_meta_var_or_all_def_in_map,
  ψ.is_meta_var_or_all_def_in_map

| (eq_ _ _) := some ()

| (forall_ _ φ) := φ.is_meta_var_or_all_def_in_map

| (def_ name args) := do
  d <- m.find name,
  guard (args.length = d.args.length)


structure theorem_ : Type :=
(Γ : list (var_name × meta_var_name))
(Δ : list formula)
(φ : formula)

def theorem_map : Type := hash_map string (fun _, theorem_)


inductive conv_step
| refl_conv : conv_step
| symm_conv : conv_step → conv_step
| trans_conv : formula → conv_step → conv_step → conv_step
| conv_not : conv_step → conv_step
| conv_imp : conv_step → conv_step → conv_step
| conv_forall : conv_step → conv_step
| conv_unfold : string → instantiation → conv_step

open conv_step


def check_conv_step
  (global_definition_map : definition_map) :
  conv_step → formula → formula → option unit

| refl_conv φ φ' := guard (φ = φ')

| (symm_conv step) φ φ' := check_conv_step step φ' φ

| (trans_conv φ' step_1 step_2) φ φ'' := do
  check_conv_step step_1 φ φ',
  check_conv_step step_2 φ' φ''

| (conv_not step) (not_ φ) (not_ φ') := check_conv_step step φ φ'

| (conv_imp step_1 step_2) (imp_ φ ψ) (imp_ φ' ψ') := do
  check_conv_step step_1 φ φ',
  check_conv_step step_2 ψ ψ'

| (conv_forall step) (forall_ x φ) (forall_ x' φ') := do
  check_conv_step step φ φ',
  guard (x = x')

| (conv_unfold name σ) φ φ' := do
  d <- global_definition_map.find name,
  guard (φ = def_ d.name (d.args.map σ.1)),
  guard (φ' = d.q.subst σ meta_var_)

| _ _ _ := none


inductive proof_step : Type
| hyp : ℕ → proof_step
| thm : string → list ℕ → instantiation → meta_instantiation → proof_step
| conv : ℕ → formula → conv_step → proof_step

open proof_step


instance
  (α : Type)
  [decidable_eq α]
  (f : α → α)
  (l1 l2 : list α) :
  decidable (l1.map f ⊆ l2) :=
begin
  exact list.decidable_ball (fun (x : α), (x ∈ l2)) (list.map f l1),
end


def check_proof_step
  (Γ : list (var_name × meta_var_name))
  (Δ : list formula)
  (global_definition_map : definition_map)
  (global_theorem_map : theorem_map)
  (local_proof_list : list formula) :
  proof_step → option formula

| (hyp index) := Δ.nth index

| (thm name hyp_index_list σ τ) := do
  (theorem_.mk Γ' Δ' φ') <- global_theorem_map.find name,
  Δ <- (hyp_index_list.map (fun (i : ℕ), local_proof_list.nth i)).option_to_option_list,
  if
    (Γ'.all (fun (p : (var_name × meta_var_name)), not_free Γ (σ.1 p.fst) (τ p.snd)))
    ∧ Δ'.map (formula.subst σ τ) = Δ
  then φ'.subst σ τ
  else none

| (conv φ_index φ' step) := do
  φ <- local_proof_list.nth φ_index,
  check_conv_step global_definition_map step φ φ',
  pure φ'


def check_proof_step_list_aux
  (Γ : list (var_name × meta_var_name))
  (Δ : list formula)
  (global_definition_map : definition_map)
  (global_theorem_map : theorem_map) :
  list formula → list proof_step → option formula

| local_proof_list [] := local_proof_list.last'

| local_proof_list (current_proof_step :: remaining_proof_step_list) := do
  local_proof <- check_proof_step Γ Δ global_definition_map global_theorem_map local_proof_list current_proof_step,
  check_proof_step_list_aux (local_proof_list ++ [local_proof]) remaining_proof_step_list


def check_proof_step_list
  (Γ : list (var_name × meta_var_name))
  (Δ : list formula)
  (global_definition_map : definition_map)
  (global_theorem_map : theorem_map)
  (proof_step_list : list proof_step) :
  option formula :=
  check_proof_step_list_aux Γ Δ global_definition_map global_theorem_map [] proof_step_list


structure proof : Type :=
  (Γ : list (var_name × meta_var_name))
  (Δ : list formula)
  (step_list : list proof_step)
  (name : string)


def check_proof
  (global_definition_map : definition_map)
  (global_theorem_map : theorem_map)
  (P : proof) :
  option theorem_ := do
  φ <- check_proof_step_list P.Γ P.Δ global_definition_map global_theorem_map P.step_list,
  some {Γ := P.Γ, Δ := P.Δ, φ := φ}


inductive command_ : Type
| add_definition : definition_ → command_
| add_proof : proof → command_

open command_


def check_command
  (global_definition_map : definition_map)
  (global_theorem_map : theorem_map) :
  command_ → option (definition_map × theorem_map)

| (add_definition d) := do
  d.q.is_meta_var_or_all_def_in_map global_definition_map,
  if ¬ global_definition_map.contains d.name
  then some (global_definition_map.insert d.name d, global_theorem_map)
  else none

| (add_proof P) := do
  (P.Δ.mmap' (formula.is_meta_var_or_all_def_in_map global_definition_map)),
  T <- check_proof global_definition_map global_theorem_map P,
  T.φ.is_meta_var_or_all_def_in_map global_definition_map,
  some (global_definition_map, global_theorem_map.insert P.name T)


def check_command_list_aux :
  definition_map → theorem_map → list command_ → option (definition_map × theorem_map)

| global_definition_map global_theorem_map [] := some (global_definition_map, global_theorem_map)

| global_definition_map global_theorem_map (current_command :: remaining_command_list) := do
  (global_definition_map', global_theorem_map') <- check_command global_definition_map global_theorem_map current_command,
  check_command_list_aux global_definition_map' global_theorem_map' remaining_command_list


def check_command_list
  (axiom_map : theorem_map)
  (command_list : list command_) :
  option (definition_map × theorem_map) :=
  check_command_list_aux (mk_hash_map string.hash) axiom_map command_list


-- First Order Logic


def mp_axiom : theorem_ := {
  Γ := [],
  Δ := [((meta_var_ "φ").imp_ (meta_var_ "ψ")), (meta_var_ "φ")],
  φ := (meta_var_ "ψ")
}

def prop_1_axiom : theorem_ := {
  Γ := [],
  Δ := [],
  φ := ((meta_var_ "φ").imp_ ((meta_var_ "ψ").imp_ (meta_var_ "φ")))
}

def prop_2_axiom : theorem_ := {
  Γ := [],
  Δ := [],
  φ := (((meta_var_ "φ").imp_ ((meta_var_ "ψ").imp_ (meta_var_ "χ"))).imp_ (((meta_var_ "φ").imp_ (meta_var_ "ψ")).imp_ ((meta_var_ "φ").imp_ (meta_var_ "χ"))))
}

def prop_3_axiom : theorem_ := {
  Γ := [],
  Δ := [],
  φ := (((not_ (meta_var_ "φ")).imp_ (not_ (meta_var_ "ψ"))).imp_ ((meta_var_ "ψ").imp_ (meta_var_ "φ")))
}

def gen_axiom : theorem_ := {
  Γ := [],
  Δ := [],
  φ := (forall_ "x" (meta_var_ "φ"))
}

def pred_1_axiom : theorem_ := {
  Γ := [],
  Δ := [],
  φ := ((forall_ "x" ((meta_var_ "φ").imp_ (meta_var_ "ψ"))).imp_ ((forall_ "x" (meta_var_ "φ")).imp_ (forall_ "x" (meta_var_ "ψ"))))
}

def pred_2_axiom : theorem_ := {
  Γ := [("x", "φ")],
  Δ := [],
  φ := ((meta_var_ "φ").imp_ (forall_ "x" (meta_var_ "φ")))
}

def eq_1_axiom : theorem_ := {
  Γ := [],
  Δ := [not_ (eq_ "y" "x")],
  φ := (exists_ "x" (eq_ "x" "y")),
}

def eq_2_axiom : theorem_ := {
  Γ := [],
  Δ := [],
  φ := ((eq_ "x" "y").imp_ ((eq_ "x" "z").imp_ (eq_ "y" "z")))
}

def fol_axiom_map : hash_map string (fun _, theorem_) :=
  hash_map.of_list
  (
    [
    ("mp", mp_axiom),
    ("prop_1", prop_1_axiom),
    ("prop_2", prop_2_axiom),
    ("prop_3", prop_3_axiom),
    ("gen", gen_axiom),
    ("pred_1", pred_1_axiom),
    ("pred_2", pred_2_axiom),
    ("eq_1", eq_1_axiom),
    ("eq_2", eq_2_axiom)
    ].map prod.to_sigma
  )
  string.hash


end mm0


namespace fol


abbreviation var_name := string
abbreviation pred_name := string


@[derive decidable_eq]
inductive formula : Type
| pred_ : pred_name → list var_name → formula
| not_ : formula → formula
| imp_ : formula → formula → formula
| eq_ : var_name → var_name → formula
| forall_ : var_name → formula → formula

open formula


def not_free (v : var_name) : formula → Prop
| (pred_ name args) := v ∉ args
| (not_ φ) := not_free φ
| (imp_ φ ψ) := not_free φ ∧ not_free ψ
| (eq_ x y) := x ≠ v ∧ y ≠ v
| (forall_ x φ) := x = v ∨ not_free φ


def exists_ (x : var_name) (φ : formula) : formula := not_ (forall_ x (not_ φ))


inductive is_proof : formula → Prop

| mp (φ ψ : formula) :
  is_proof φ → is_proof (φ.imp_ ψ) → is_proof ψ

| prop_1 (φ ψ : formula) :
  is_proof (φ.imp_ (ψ.imp_ φ))

| prop_2 (φ ψ χ : formula) :
  is_proof ((φ.imp_ (ψ.imp_ χ)).imp_ ((φ.imp_ ψ).imp_ (φ.imp_ χ)))

| prop_3 (φ ψ : formula) :
  is_proof (((not_ φ).imp_ (not_ ψ)).imp_ (ψ.imp_ φ))

| gen (φ : formula) (x : var_name) :
  is_proof φ → is_proof (forall_ x φ)

| pred_1 (φ ψ : formula) (x : var_name) :
  is_proof ((forall_ x (φ.imp_ ψ)).imp_ ((forall_ x φ).imp_ (forall_ x ψ)))

| pred_2 (φ : formula) (x : var_name) :
  not_free x φ → is_proof (φ.imp_ (forall_ x φ))

| eq_1 (x y : var_name) :
  y ≠ x → is_proof (exists_ x (eq_ x y))

| eq_2 (x y z : var_name) :
  is_proof ((eq_ x y).imp_ ((eq_ x z).imp_ (eq_ y z)))


end fol


def mm0.formula.to_fol_formula
  (M : mm0.meta_var_name → fol.formula) :
  mm0.formula → fol.formula
| (mm0.formula.meta_var_ X) := M X
| (mm0.formula.pred_ name args) := fol.formula.pred_ name args
| (mm0.formula.not_ φ) := fol.formula.not_ φ.to_fol_formula
| (mm0.formula.imp_ φ ψ) := fol.formula.imp_ φ.to_fol_formula ψ.to_fol_formula
| (mm0.formula.eq_ x y) := fol.formula.eq_ x y
| (mm0.formula.forall_ x φ) := fol.formula.forall_ x φ.to_fol_formula
| (mm0.formula.def_ name args) := fol.formula.pred_ name args


def fol.formula.to_mm0_formula : fol.formula → mm0.formula
| (fol.formula.pred_ name args) := mm0.formula.pred_ name args
| (fol.formula.not_ φ) := mm0.formula.not_ φ.to_mm0_formula
| (fol.formula.imp_ φ ψ) := mm0.formula.imp_ φ.to_mm0_formula ψ.to_mm0_formula
| (fol.formula.eq_ x y) := mm0.formula.eq_ x y
| (fol.formula.forall_ x φ) := mm0.formula.forall_ x φ.to_mm0_formula


example
  (φ : fol.formula)
  (M : mm0.meta_var_name → fol.formula) :
  mm0.formula.to_fol_formula M (fol.formula.to_mm0_formula φ) = φ :=
begin
  induction φ,
  case fol.formula.pred_ : name args
  {
    unfold fol.formula.to_mm0_formula,
    unfold mm0.formula.to_fol_formula,
  },
  case fol.formula.not_ : φ φ_ih
  {
    unfold fol.formula.to_mm0_formula,
    unfold mm0.formula.to_fol_formula,
    rewrite φ_ih,
  },
  case fol.formula.imp_ : φ ψ φ_ih ψ_ih
  {
    unfold fol.formula.to_mm0_formula,
    unfold mm0.formula.to_fol_formula,
    rewrite φ_ih,
    rewrite ψ_ih,
  },
  case fol.formula.eq_ : x y
  {
    unfold fol.formula.to_mm0_formula,
    unfold mm0.formula.to_fol_formula,
  },
  case fol.formula.forall_ : x φ φ_ih
  {
    unfold fol.formula.to_mm0_formula,
    unfold mm0.formula.to_fol_formula,
    rewrite φ_ih,
  },
end


example
  (M : mm0.meta_var_name → fol.formula)
  (Γ : list (mm0.var_name × mm0.meta_var_name))
  (v : mm0.var_name)
  (φ : mm0.formula)
  (h1 : mm0.not_free Γ v φ)
  (h2 : ∀ (x : mm0.var_name) (X : mm0.meta_var_name),
    ((x, X) ∈ Γ) → fol.not_free x (M X)) :
  fol.not_free v (mm0.formula.to_fol_formula M φ) :=
begin
  induction φ generalizing v,
  case mm0.formula.meta_var_ : X x h1
  {
    unfold mm0.not_free at h1,
    unfold mm0.formula.to_fol_formula,
    exact h2 x X h1,
  },
  case mm0.formula.pred_ : name args x h1
  {
    unfold mm0.not_free at h1,
    unfold mm0.formula.to_fol_formula,
    unfold fol.not_free,
    exact h1,
  },
  case mm0.formula.not_ : φ φ_ih x h1
  {
    unfold mm0.not_free at h1,
    unfold mm0.formula.to_fol_formula,
    unfold fol.not_free,
    exact φ_ih x h1,
  },
  case mm0.formula.imp_ : φ ψ φ_ih ψ_ih x h1
  {
    unfold mm0.not_free at h1,
    cases h1,

    unfold mm0.formula.to_fol_formula,
    unfold fol.not_free,
    split,
    {
      exact φ_ih x h1_left,
    },
    {
      exact ψ_ih x h1_right,
    }
  },
  case mm0.formula.eq_ : x y x' h1
  {
    unfold mm0.not_free at h1,
    unfold mm0.formula.to_fol_formula,
    unfold fol.not_free,
    exact h1,
  },
  case mm0.formula.forall_ : x φ φ_ih x' h1
  {
    unfold mm0.not_free at h1,
    unfold mm0.formula.to_fol_formula,
    unfold fol.not_free,
    cases h1,
    {
      apply or.intro_left,
      exact h1,
    },
    {
      apply or.intro_right,
      exact φ_ih x' h1,
    }
  },
  case mm0.formula.def_ : name args x h1
  {
    unfold mm0.not_free at h1,
    unfold mm0.formula.to_fol_formula,
    unfold fol.not_free,
    exact h1,
  },
end


theorem conservative
  (E : mm0.env)
  (Γ : list (mm0.var_name × mm0.meta_var_name))
  (Δ : list mm0.formula)
  (φ : mm0.formula)
  (M : mm0.meta_var_name → fol.formula)
  (h1 : mm0.is_proof E Γ Δ φ)
  (h2 : ∀ (x : mm0.var_name) (X : mm0.meta_var_name), (x, X) ∈ Γ → fol.not_free x (M X))
  (h3 : ∀ (ψ : mm0.formula), ψ ∈ Δ → fol.is_proof (mm0.formula.to_fol_formula M ψ)) :
  fol.is_proof (mm0.formula.to_fol_formula M φ) :=
begin
  induction h1,
  case is_proof.hyp : h1_Γ h1_Δ h1_φ h1_1 h1_2
  {
    exact h3 h1_φ h1_2,
  },
  case is_proof.mp : h1_Γ h1_Δ h1_φ h1_ψ h1_1 h1_2 h1_ih_1 h1_ih_2
  {
    unfold mm0.formula.to_fol_formula at h1_ih_2,

    apply fol.is_proof.mp (mm0.formula.to_fol_formula M h1_φ) (mm0.formula.to_fol_formula M h1_ψ),
    {
      exact h1_ih_1 h2 h3,
    },
    {
      exact h1_ih_2 h2 h3,
    }
  },
  case is_proof.prop_1 : h1_Γ h1_Δ h1_φ h1_ψ h1_1 h1_2
  {
    apply fol.is_proof.prop_1,
  },
  case is_proof.prop_2 : h1_Γ h1_Δ h1_φ h1_ψ h1_χ h1_1 h1_2 h1_3
  {
    apply fol.is_proof.prop_2,
  },
  case is_proof.prop_3 : h1_Γ h1_Δ h1_φ h1_ψ h1_1 h1_2
  {
    apply fol.is_proof.prop_3,
  },
  case is_proof.gen : h1_Γ h1_Δ h1_φ h1_x h1_1 h1_ih
  {
    apply fol.is_proof.gen,
    exact h1_ih h2 h3,
  },
  case is_proof.pred_1 : h1_Γ h1_Δ h1_φ h1_ψ h1_x h1_1 h1_2
  {
    apply fol.is_proof.pred_1,
  },
  case is_proof.pred_2 : h1_Γ h1_Δ h1_φ h1_x h1_1 h1_2
  {
    apply fol.is_proof.pred_2,
    induction h1_φ generalizing h1_x,
    case mm0.formula.meta_var_ : X
    {
      unfold mm0.not_free at h1_2,

      exact h2 h1_x X h1_2,
    },
    case mm0.formula.pred_ : h1_name h1_args
    {
      unfold mm0.not_free at h1_2,

      unfold mm0.formula.to_fol_formula,
      unfold fol.not_free,
      exact h1_2,
    },
    case mm0.formula.not_ : h1_φ h1_φ_ih
    {
      unfold mm0.formula.is_meta_var_or_all_def_in_env at h1_1,
      unfold mm0.not_free at h1_2,

      unfold mm0.formula.to_fol_formula,
      unfold fol.not_free,
      exact h1_φ_ih h1_1 h1_x h1_2,
    },
    case mm0.formula.imp_ : h1_φ h1_ψ h1_φ_ih h1_ψ_ih
    {
      unfold mm0.formula.is_meta_var_or_all_def_in_env at h1_1,
      cases h1_1,

      unfold mm0.not_free at h1_2,
      cases h1_2,

      unfold mm0.formula.to_fol_formula,
      unfold fol.not_free,
      split,
      {
        exact h1_φ_ih h1_1_left h1_x h1_2_left,
      },
      {
        exact h1_ψ_ih h1_1_right h1_x h1_2_right,
      }
    },
    case mm0.formula.eq_ : h1_x h1_y
    {
      unfold mm0.not_free at h1_2,

      unfold mm0.formula.to_fol_formula,
      unfold fol.not_free,
      exact h1_2,
    },
    case mm0.formula.forall_ : h1_x h1_φ h1_φ_ih
    {
      unfold mm0.formula.is_meta_var_or_all_def_in_env at h1_1,
      unfold mm0.not_free at h1_2,

      unfold mm0.formula.to_fol_formula,
      unfold fol.not_free,
      cases h1_2,
      {
        apply or.intro_left,
        exact h1_2,
      },
      {
        apply or.intro_right,
        exact h1_φ_ih h1_1 h1_x h1_2,
      }
    },
    case mm0.formula.def_ : h1_name h1_args
    {
      unfold mm0.not_free at h1_2,

      unfold mm0.formula.to_fol_formula,
      unfold fol.not_free,
      exact h1_2,
    },
  },
  case is_proof.eq_1 : h1_Γ h1_Δ h1_x h1_y h1_1
  {
    apply fol.is_proof.eq_1,
    exact h1_1,
  },
  case is_proof.eq_2 : h1_Γ h1_Δ h1_x h1_y h1_z
  {
    apply fol.is_proof.eq_2,
  },
  case is_proof.thm : h1_Γ h1_Γ' h1_Δ h1_Δ' h1_φ h1_σ h1_τ h1_1 h1_2 h1_3 h1_4 h1_ih_1 h1_ih_2
  {
    dsimp at *,
    sorry,
  },
  case is_proof.conv : h1_Γ h1_Δ h1_φ h1_φ' h1_1 h1_2 h1_3 h1_ih
  {
    specialize h1_ih h2 h3,
    sorry,
  },
end
