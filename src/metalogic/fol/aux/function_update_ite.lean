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


lemma function.update_ite_symm
  {α β : Sort*}
  [decidable_eq α]
  (f : α → β)
  (x y : α)
  (d d' : β)
  (h1 : ¬ x = y) :
  function.update_ite (function.update_ite f x d) y d' =
    function.update_ite (function.update_ite f y d') x d :=
begin
  funext,
  unfold function.update_ite,
  by_cases c1 : a = x,
  {
    by_cases c2 : a = y,
    {
      subst c1,
      subst c2,
      contradiction,
    },
    {
      subst c1,
      simp only [eq_self_iff_true, if_true, ite_eq_right_iff],
      intros a1,
      contradiction,
    }
  },
  {
    by_cases c2 : a = y,
    {
      subst c2,
      simp only [eq_self_iff_true, if_true],
      simp only [if_neg c1],
    },
    {
      simp only [if_neg c1],
    }
  }
end


def function.update_list_ite
  {α β : Type}
  [decidable_eq α]
  (f : α → β) :
  list α → list β → α → β
| (x :: xs) (y :: ys) := function.update_ite (function.update_list_ite xs ys) x y 
| _ _ := f


def function.update_list_ite'
  {α β : Type}
  [decidable_eq α]
  (f : α → β)
  (xs : list α)
  (ys : list β) :
  α → β :=
  list.foldr (fun (p : α × β) (g : α → β), function.update_ite f p.fst p.snd) f (list.zip xs ys) 

#eval function.update_list_ite' (fun (n : ℕ), n) [0, 3, 0] [10, 2, 2] 0


lemma function.update_list_ite_comp
  {α β γ : Type}
  [decidable_eq α]
  [decidable_eq β]
  (f : α → β)
  (g : β → γ)
  (xs : list α)
  (ys : list β) :
  g ∘ (function.update_list_ite f xs ys) =
  function.update_list_ite (g ∘ f) xs (ys.map g) :=
begin
  induction xs generalizing ys,
  case list.nil : ys
  {
    unfold function.update_list_ite,
  },
  case list.cons : xs_hd xs_tl xs_ih ys
  {
    cases ys,
    case list.nil
    {
      simp only [list.map_nil],
      unfold function.update_list_ite,
    },
    case list.cons : ys_hd ys_tl
    {
      simp only [list.map],
      unfold function.update_list_ite,
      rewrite <- xs_ih,
      apply function.update_ite_comp,
    },
  },
end


lemma function.update_list_ite_mem
  {α β : Type}
  [decidable_eq α]
  (f g : α → β)
  (v : α)
  (xs : list α)
  (ys : list β)
  (h1 : v ∈ xs)
  (h2 : f v = g v) :
  function.update_list_ite f xs ys v =
  function.update_list_ite g xs ys v :=
begin
  induction xs generalizing ys,
  case list.nil : ys
  {
    squeeze_simp at h1,
    contradiction,
  },
  case list.cons : xs_hd xs_tl xs_ih ys
  {
    cases ys,
    case list.nil
    {
      squeeze_simp at h1,
      unfold function.update_list_ite,
      exact h2,
    },
    case list.cons : ys_hd ys_tl
    {
      squeeze_simp at h1,

      unfold function.update_list_ite,
      unfold function.update_ite,
      split_ifs,
      refl,
      cases h1,
      contradiction,
      apply xs_ih,
      exact h1,
    },
  },
end

lemma function.update_list_ite_not_mem
  {α β : Type}
  [decidable_eq α]
  (f : α → β)
  (v : α)
  (xs : list α)
  (ys : list β)
  (h1 : v ∉ xs) :
  function.update_list_ite f xs ys v = f v :=
begin
  induction xs generalizing ys,
  case list.nil : ys
  {
    unfold function.update_list_ite,
  },
  case list.cons : xs_hd xs_tl xs_ih ys
  {
    cases ys,
    case list.nil
    {
      unfold function.update_list_ite,
    },
    case list.cons : ys_hd ys_tl
    {
      unfold function.update_list_ite,
      unfold function.update_ite,
      split_ifs,
      {
        subst h,
        simp only [list.mem_cons_iff, eq_self_iff_true, true_or, not_true] at h1,
        contradiction,
      },
      {
        simp only [list.mem_cons_iff] at h1,
        push_neg at h1,
        cases h1,
        apply xs_ih,
        exact h1_right,
      },
    },
  },
end


def function.update_vector_ite
  {α β : Type}
  [decidable_eq α]
  (f : α → β) :
  Π (m : ℕ), vector α m → Π (n : ℕ), vector β n → α → β
| (m + 1) ⟨x :: xs, hx⟩ (n + 1) ⟨y :: ys, hy⟩ :=
    function.update_ite (function.update_vector_ite
      m
      ⟨xs, begin squeeze_simp at hx, exact hx end⟩
      n
      ⟨ys, begin squeeze_simp at hy, exact hy end⟩) x y 
| _ _ _ _ := f


#lint
