import tactic


/--
  Specialized version of function.update.
-/
def function.update_ite
  {α β : Type}
  [decidable_eq α]
  (f : α → β)
  (a' : α) (b : β) (a : α) :=
  if a = a' then b else f a


lemma function.update_ite_comp
  {α α' β : Sort*}
  [decidable_eq α]
  (f : α' → β)
  (g : α → α')
  (i : α)
  (v : α') :
  f ∘ (function.update_ite g i v) =
    function.update_ite (f ∘ g) i (f v) :=
begin
  funext,
  simp only [function.comp_app],
  unfold function.update_ite,
  split_ifs; refl,
end


@[simp]
lemma function.update_ite_idem
  {α β : Type}
  [decidable_eq α]
  (f : α → β)
  (a : α)
  (x y : β)  :
  function.update_ite (function.update_ite f a x) a y =
    function.update_ite f a y :=
begin
  funext,
  unfold function.update_ite,
  split_ifs,
  {
    refl,
  },
  {
    refl,
  }
end


lemma function.update_ite_id
  {α : Type}
  [decidable_eq α]
  (x : α) :
  function.update_ite (id : α → α) x x = id :=
begin
  funext,
  unfold function.update_ite,
  split_ifs,
  {
    subst h,
    simp only [id.def],
  },
  {
    refl,
  }
end


lemma function.update_ite_not_mem_list
  {α β : Type}
  [decidable_eq α]
  (l : list α)
  (f : α → β)
  (a : α)
  (b : β)
  (h1 : a ∉ l) :
  l.map (function.update_ite f a b) = l.map f :=
begin
  induction l,
  case list.nil
  {
    simp only [list.map_nil],
  },
  case list.cons : l_hd l_tl l_ih
  {
    simp only [list.mem_cons_iff] at h1,
    push_neg at h1,
    dsimp at h1,
    cases h1,

    simp only [list.map],
    split,
    {
      unfold function.update_ite,
      split_ifs; tauto,
    },
    {
      exact l_ih h1_right,
    }
  },
end


lemma function.update_ite_not_mem_set
  {α β : Type}
  [decidable_eq α] [decidable_eq β]
  (S : finset α)
  (f : α → β)
  (a : α)
  (b : β)
  (h1 : a ∉ S) :
  finset.image (function.update_ite f a b) S = finset.image f S :=
begin
  induction S using finset.induction_on,
  case h₁
  {
    simp only [finset.image_empty],
  },
  case h₂ : S_a S_S S_1 S_ih
  {
    simp only [finset.mem_insert] at h1,
    push_neg at h1,
    dsimp at h1,
    cases h1,


    simp only [finset.image_insert],
    congr' 1,
    {
      unfold function.update_ite,
      split_ifs; tauto,
    },
    {
      exact S_ih h1_right,
    }
  },
end

#lint
