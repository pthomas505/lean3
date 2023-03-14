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


lemma comp_update_ite
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
