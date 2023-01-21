import logic.function.basic
import tactic


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


lemma nodup_eq_len_imp_eqv
  {α : Type}
  [decidable_eq α]
  (l1 l2 : list α)
  (h1 : l1.length = l2.length)
  (h2 : l1.nodup)
  (h3 : l2.nodup) :
  ∃ (f : α ≃ α), l1.map f.to_fun = l2 :=
begin
  have s1 : {x // (x ∈ l1)} ≃ {x // (x ∈ l2)},
  transitivity,
  symmetry,
  exact list.nodup.nth_le_equiv l1 h2,
  rewrite h1,
  exact list.nodup.nth_le_equiv l2 h3,
  sorry,
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
