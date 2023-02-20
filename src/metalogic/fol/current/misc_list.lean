import data.list.basic


lemma list.map_id''''
  {α : Type}
  {f : α → α}
  (l : list α)
  (h1 : ∀ (x : α), x ∈ l → f x = x) :
  list.map f l = l :=
begin
  induction l,
  case list.nil
  {
    simp only [list.map_nil],
  },
  case list.cons : l_hd l_tl l_ih
  {
    simp only [list.mem_cons_iff, forall_eq_or_imp] at h1,
    cases h1,

    simp only [list.map],
    split,
    {
      exact h1_left,
    },
    {
      exact l_ih h1_right,
    }
  },
end
