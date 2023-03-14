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
