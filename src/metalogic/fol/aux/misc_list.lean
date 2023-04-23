import data.list.basic


@[simp]
lemma list.map_eq_self_iff
  {α : Type}
  {f : α → α}
  (l : list α) :
  (list.map f l = l) ↔ ∀ (x : α), x ∈ l → f x = x :=
begin
  induction l,
  case list.nil
  {
    simp only [list.map_nil, eq_self_iff_true, list.not_mem_nil, is_empty.forall_iff, implies_true_iff],
  },
  case list.cons : l_hd l_tl l_ih
  {
    simp only [list.map, list.mem_cons_iff, forall_eq_or_imp, and.congr_right_iff],
    intros a1,
    exact l_ih,
  },
end


lemma list_map₂_of_map
  {α β γ : Type}
  (l : list α)
  (f : α → β)
  (g : α → β → γ) :
  list.map₂ g l (list.map f l) =
    list.map (fun (x : α), g x (f x)) l :=
begin
  induction l,
  case list.nil
  {
    simp only [list.map₂, list.map_nil],
  },
  case list.cons : hd tl ih
  {
    simp only [list.map₂, list.map, eq_self_iff_true, true_and],
    exact ih,
  },
end


#lint
