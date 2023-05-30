/-
References:

Lectures on the Curry-Howard Isomorphism
Morten Heine Sørensen
Pawel Urzyczyn
Jul 2006
Elsevier
https://play.google.com/store/books/details/Morten_Heine_S%C3%B8rensen_Lectures_on_the_Curry_Howard?id=_mtnm-9KtbEC&hl=en
-/

import tactic

def var := ℕ

inductive term : Type
| var : var → term
| app : term → term → term
-- term.abs y P = λ y . P
| abs : var → term → term


def FV : term → set var
| (term.var x) := {x}
| (term.app P Q) := (FV P) ∪ (FV Q)
| (term.abs x P) := (FV P) \ {x}


lemma simp_term_var
(x : var) (y : var) :
x ∈ FV (term.var y) ↔ x = y :=
begin
unfold FV,
simp only [set.mem_singleton_iff]
end

lemma simp_term_app
(x : var) (P : term) (Q : term) :
x ∈ FV (term.app P Q) ↔ x ∈ FV P ∨ x ∈ FV Q :=
begin
unfold FV,
squeeze_simp,
end

lemma simp_term_app_not
(x : var) (P : term) (Q : term) :
x ∉ FV (term.app P Q) ↔ x ∉ FV P ∧ x ∉ FV Q :=
begin
unfold FV,
squeeze_simp,
push_neg,
exact iff.rfl
end

lemma simp_term_abs
(x : var) (y : var) (P : term) :
x ∈ FV (term.abs y P) ↔ x ∈ FV P ∧ x ≠ y :=
begin
unfold FV,
simp only [set.mem_diff, set.mem_singleton_iff]
end

lemma misc_1
{x : var} {y : var} {P : term}
(H1 : x ∈ FV P)
(H2 : x ≠ y) :
x ∈ FV (term.abs y P) :=
begin
simp only [simp_term_abs],
exact and.intro H1 H2
end

lemma misc_2
{x : var} {y : var} {P : term}
(H1 : x ∈ FV (term.abs y P)) :
x ∈ FV P :=
begin
simp only [simp_term_abs] at H1,
cases H1,
exact H1_left
end

lemma misc_3
{x : var} {y : var} {P : term}
(H1 : x ∈ FV (term.abs y P)) :
x ≠ y :=
begin
simp only [simp_term_abs] at H1,
cases H1,
exact H1_right
end

lemma misc_4
{x : var} {y : var} {P : term}
(H1 : x = y) :
x ∉ FV (term.abs y P) :=
begin
simp only [simp_term_abs],
push_neg,
intro, exact H1
end

lemma misc_5
{x : var} {y : var} {P : term}
(H1 : x ∉ FV P) :
x ∉ FV (term.abs y P) :=
begin
simp only [simp_term_abs],
push_neg,
intro H2, by_contradiction, apply H1, exact H2
end

lemma misc_6
{x : var} {y : var} {P : term}
(H1 : x ∉ FV (term.abs y P))
(H2 : x ∈ FV P) :
x = y :=
begin
simp only [simp_term_abs] at H1,
push_neg at H1,
exact H1 H2
end

lemma misc_7
{x : var} {y : var} {P : term}
(H1 : x ∉ FV (term.abs y P))
(H2 : x ≠ y) :
x ∉ FV P :=
begin
simp only [simp_term_abs] at H1,
push_neg at H1,
intro H3, apply H2, exact H1 H3
end


-- sub_is_def M x N means M [ x := N ] is defined
inductive sub_is_def : term → var → term → Prop

-- y [ x := N ] is defined
| var {y : var} {x : var} {N : term} :
  sub_is_def (term.var y) x N

-- P [ x := N ] is defined → Q [ x := N ] is defined → (P Q) [ x := N ] is defined
| app {P : term} {Q : term} {x : var} {N : term} :
  sub_is_def P x N → sub_is_def Q x N → sub_is_def (term.app P Q) x N

-- x = y → ( λ y . P ) [ x := N ] is defined
| abs_same {y : var} {P : term} {x : var} {N : term} :
  x = y → sub_is_def (term.abs y P) x N

-- x ≠ y → x ∉ FV ( λ y . P ) → ( λ y . P ) [ x := N ] is defined
| abs_diff_nel {y : var} {P : term} {x : var} {N : term} :
  x ≠ y → x ∉ FV (term.abs y P) → sub_is_def (term.abs y P) x N

-- x ≠ y → y ∉ FV ( N ) → P [ x := N ] is defined → ( λ y . P ) [ x := N ] is defined
| abs_diff {y : var} {P : term} {x : var} {N : term} :
  x ≠ y → y ∉ FV N → sub_is_def P x N → sub_is_def (term.abs y P) x N

notation M `[` x `:=` N `]` `is_def` := sub_is_def M x N


-- M [ x := N ]
def sub : term → var → term → term
-- if x = y then y [ x := N ] = N else y [ x := N ] = y
| (term.var y) x N := if x = y then N else term.var y

-- (P Q) [ x := N ] = (P [ x := N ] Q [ x := N ])
| (term.app P Q) x N := term.app (sub P x N) (sub Q x N)

-- if x = y then ( λ y . P ) [ x := N ] = ( λ y . P ) else ( λ y . P ) [ x := N ] = ( λ y . P [ x := N ] )
| (term.abs y P) x N := if x = y then term.abs y P else term.abs y (sub P x N)

notation M `[` x `:=` N `]` := sub M x N


-- is_sub M x N L means M [ x := N ] = L
inductive is_sub : term → var → term → term → Prop

-- if x = y then y [ x := N ] = N
| var_same {y : var} {x : var} {N : term} :
  x = y → is_sub (term.var y) x N N

-- if x ≠ y then y [ x := N ] = y
| var_diff {y : var} {x : var} {N : term} :
  x ≠ y → is_sub (term.var y) x N (term.var y)

-- (P Q) [ x := N ] = (P [ x := N ] Q [ x := N ])
| app {P : term} {Q : term} {x : var} {N : term} {P' : term} {Q' : term} :
  is_sub P x N P' → is_sub Q x N Q' → is_sub (term.app P Q) x N (term.app P' Q')

-- if x = y then ( λ y . P ) [ x := N ] = ( λ y . P )
| abs_same {y : var} {P : term} {x : var} {N : term} :
  x = y → is_sub (term.abs y P) x N (term.abs y P)

-- if x ≠ y then ( λ y . P ) [ x := N ] = ( λ y . P [ x := N ] )

| abs_diff_nel {y : var} {P : term} {x : var} {N : term} {P' : term} :
  x ≠ y → x ∉ FV (term.abs y P) → is_sub P x N P' → is_sub (term.abs y P) x N (term.abs y P')

| abs_diff {y : var} {P : term} {x : var} {N : term} {P' : term} :
  x ≠ y → y ∉ FV N → is_sub P x N P' → is_sub (term.abs y P) x N (term.abs y P')


lemma simp_var_same
{y : var} {x : var} {N : term}
(H1 : x = y) :
(term.var y) [ x := N ] = N := if_pos H1

lemma simp_var_diff
{y : var} {x : var} {N : term}
(H1 : x ≠ y) :
(term.var y) [ x := N ] = term.var y := if_neg H1

lemma simp_abs_same
{y : var} {P : term} {x : var} {N : term}
(H1 : x = y) :
(term.abs y P) [ x := N ] = term.abs y P := if_pos H1

lemma simp_abs_diff
{y : var} {P : term} {x : var} {N : term}
(H1 : x ≠ y) :
(term.abs y P) [ x := N ] = term.abs y (P [ x := N ]) := if_neg H1


lemma lemma_1_2_5_i_a
{M : term} {x : var} {N : term}
(H1 : x ∉ FV M) :
M [ x := N ] is_def :=
begin
induction M,
case term.var : y
{
  exact sub_is_def.var
},
case term.app : P Q IH_P IH_Q
{
  simp only [simp_term_app_not] at H1,
  cases H1,
  specialize IH_P H1_left,
  specialize IH_Q H1_right,
  exact sub_is_def.app IH_P IH_Q
},
case term.abs : y P
{
  by_cases h_xy : x = y,
  exact sub_is_def.abs_same h_xy,
  exact sub_is_def.abs_diff_nel h_xy H1
}
end


lemma lemma_1_2_5_i_b
{M : term} {x : var} {N : term}
(H1 : x ∉ FV M) :
M [ x := N ] = M :=
begin
induction M,
case term.var : y
{
  exact if_neg H1
},
case term.app : P Q IH_P IH_Q
{
  unfold sub,
  simp only [simp_term_app_not] at H1,
  cases H1,
  specialize IH_P H1_left,
  specialize IH_Q H1_right,
  rewrite IH_P, rewrite IH_Q
},
case term.abs : y P IH
{
  by_cases h_xy : x = y,
  {
    exact if_pos h_xy
  },
  {
    have s1 : x ∉ FV P, exact misc_7 H1 h_xy,
    specialize IH s1,
    rewrite simp_abs_diff h_xy,
    rewrite IH
  }
}
end


lemma lemma_1_2_5_i
{M : term} {x : var} {N : term}
(H1 : x ∉ FV M) :
is_sub M x N M :=
begin
induction M,
case term.var : y
{
  simp only [simp_term_var] at H1,
  exact is_sub.var_diff H1
},
case term.app : P Q IH_P IH_Q
{
  simp only [simp_term_app_not] at H1,
  cases H1,
  specialize IH_P H1_left,
  specialize IH_Q H1_right,
  exact is_sub.app IH_P IH_Q
},
case term.abs : y P IH
{
  by_cases h_xy : x = y,
  {
    exact is_sub.abs_same h_xy
  },
  {
    have s1 : x ∉ FV P, exact misc_7 H1 h_xy,
    specialize IH s1,
    exact is_sub.abs_diff_nel h_xy H1 IH
  }
}
end


example
(M : term) (x : var) (N : term) (L : term)
(H1 : is_sub M x N L) :
M [ x := N ] = L :=
begin
induction H1,
exact if_pos H1_ᾰ,
exact if_neg H1_ᾰ,
unfold sub, rewrite H1_ih_ᾰ, rewrite H1_ih_ᾰ_1,
exact if_pos H1_ᾰ,
rewrite <- H1_ih, exact if_neg H1_ᾰ,
rewrite <- H1_ih, exact if_neg H1_ᾰ,
end


example
(M : term) (x : var) (N : term)
(H1 : ∃ (L : term), is_sub M x N L) :
M [ x := N ] is_def :=
begin
apply exists.elim H1,
intros L,
intros h,
induction h,
case is_sub.var_same : y x N h
{
  exact sub_is_def.var
},
case is_sub.var_diff : y x N h
{
  exact sub_is_def.var
},
case is_sub.app : P Q x N P' Q' IH_P' IH_Q' IH_P IH_Q
{
  apply sub_is_def.app, apply IH_P, existsi P', exact IH_P', apply IH_Q, existsi Q', exact IH_Q'
},
case is_sub.abs_same : y P x N h
{
  exact sub_is_def.abs_same h
},
case is_sub.abs_diff_nel : y P x N P' h1 h2 h3 IH
{
  exact sub_is_def.abs_diff_nel h1 h2
},
case is_sub.abs_diff : y P x N P' h1 h2 h3 IH
{
  apply sub_is_def.abs_diff h1 h2, apply IH, existsi P', exact h3
}
end


example
(M : term) (x : var) (N : term)
(H1 : M [ x := N ] is_def) :
is_sub M x N (M [ x := N ]) :=
begin
induction M,
case term.var : y
{
  by_cases h_xy : x = y,
  {
    rewrite simp_var_same h_xy,
    exact is_sub.var_same h_xy
  },
  {
    rewrite simp_var_diff h_xy,
    exact is_sub.var_diff h_xy
  }
},
case term.app : P Q IH_P IH_Q
{
  unfold sub,
  cases H1,
  specialize IH_P H1_ᾰ,
  specialize IH_Q H1_ᾰ_1,
  exact is_sub.app IH_P IH_Q
},
case term.abs : y P IH
{
  cases H1,
  {
    rewrite simp_abs_same H1_ᾰ,
    exact is_sub.abs_same H1_ᾰ
  },
  {
    rewrite simp_abs_diff H1_ᾰ,
    have s1 : x ∉ FV P, exact misc_7 H1_ᾰ_1 H1_ᾰ,
    have s2 : P [ x := N ] is_def, exact lemma_1_2_5_i_a s1,
    specialize IH s2,
    exact is_sub.abs_diff_nel H1_ᾰ H1_ᾰ_1 IH
  },
  {
    rewrite simp_abs_diff H1_ᾰ,
    specialize IH H1_ᾰ_2,
    exact is_sub.abs_diff H1_ᾰ H1_ᾰ_1 IH
  }
}
end


lemma misc_5'
{x : var} {y : var} {P : term} {N : term}
(H1 : x ∉ FV P) :
(term.abs y P) [ x := N ] = term.abs y P :=
begin
have s1 : x ∉ FV (term.abs y P), exact misc_5 H1,
exact lemma_1_2_5_i_b s1
end

lemma misc_7'
{x : var} {y : var} {P : term} {N : term}
(H1 : x ∉ FV (term.abs y P))
(H2 : x ≠ y) :
P [ x := N ] = P :=
begin
have s1 : x ∉ FV P, exact misc_7 H1 H2,
exact lemma_1_2_5_i_b s1
end


lemma lemma_1_2_5_ii_right
(M : term) (x : var) (N : term) (z : var)
(H1 : M [ x := N ] is_def)
(H2 : z ∈ FV (M [ x := N ])) :
(z ∈ FV M ∧ x ≠ z) ∨ (z ∈ FV N ∧ x ∈ FV M) :=
begin
induction H1,
case sub_is_def.var : y x N
{
  simp only [simp_term_var],
  by_cases h_xy : x = y,
  {
    rewrite simp_var_same h_xy at H2,
    apply or.intro_right, exact and.intro H2 h_xy,
  },
  {
    rewrite simp_var_diff h_xy at H2,
    simp only [simp_term_var] at H2,
    rewrite <- H2 at h_xy,
    apply or.intro_left, exact and.intro H2 h_xy,
  }
},
case sub_is_def.app : P Q x N H1_P H1_Q IH_P IH_Q
{
  unfold sub at H2,
  simp only [simp_term_app] at H2,
  simp only [simp_term_app],
  cases H2,
  {
    specialize IH_P H2,
    cases IH_P,
    {
      cases IH_P,
      apply or.intro_left,
      apply and.intro,
      apply or.intro_left, exact IH_P_left,
      exact IH_P_right
    },
    {
      cases IH_P,
      apply or.intro_right,
      apply and.intro,
      exact IH_P_left,
      apply or.intro_left, exact IH_P_right
    }
  },
  {
    specialize IH_Q H2,
    cases IH_Q,
    {
      cases IH_Q,
      apply or.intro_left,
      apply and.intro,
      apply or.intro_right, exact IH_Q_left,
      exact IH_Q_right
    },
    {
      cases IH_Q,
      apply or.intro_right,
      apply and.intro,
      exact IH_Q_left,
      apply or.intro_right, exact IH_Q_right
    }
  }
},
case sub_is_def.abs_same : y P x N IH_1
{
  rewrite simp_abs_same IH_1 at H2,
  apply or.intro_left,
  apply and.intro,
  exact H2,
  rewrite IH_1, symmetry, exact misc_3 H2
},
case sub_is_def.abs_diff_nel : y P x N IH_1 IH_2
{
  rewrite lemma_1_2_5_i_b IH_2 at H2,
  apply or.intro_left,
  apply and.intro,
  exact H2,
  intros h, apply IH_2, rewrite h, exact H2
},
case sub_is_def.abs_diff : y P x N IH_1 IH_2 IH_3 IH_4
{
  simp only [simp_term_abs],
  rewrite simp_abs_diff IH_1 at H2,
  simp only [simp_term_abs] at H2,
  cases H2,
  specialize IH_4 H2_left,
  cases IH_4,
  {
    cases IH_4,
    apply or.intro_left,
    apply and.intro,
    exact and.intro IH_4_left H2_right,
    exact IH_4_right
  },
  {
    cases IH_4,
    apply or.intro_right,
    apply and.intro,
    exact IH_4_left,
    exact and.intro IH_4_right IH_1
  }
}
end

lemma lemma_1_2_5_ii_left
(M : term) (x : var) (N : term) (z : var)
(H1 : M [ x := N ] is_def)
(H2 : (z ∈ FV M ∧ x ≠ z) ∨ (z ∈ FV N ∧ x ∈ FV M)) :
z ∈ FV (M [ x := N ]) :=
begin
induction H1,
case sub_is_def.var : y x N
{
  simp only [simp_term_var] at H2,
  cases H2,
  {
    cases H2,
    rewrite H2_left at H2_right,
    rewrite simp_var_diff H2_right,
    simp only [simp_term_var],
    exact H2_left,
  },
  {
    cases H2,
    rewrite simp_var_same H2_right,
    exact H2_left
  }
},
case sub_is_def.app : P Q x N H1_P H1_Q IH_P IH_Q
{
  unfold sub,
  simp only [simp_term_app],
  simp only [simp_term_app] at H2,
  cases H2,
  {
    cases H2,
    cases H2_left,
    {
      apply or.intro_left,
      apply IH_P,
      apply or.intro_left, exact and.intro H2_left H2_right
    },
    {
      apply or.intro_right,
      apply IH_Q,
      apply or.intro_left, exact and.intro H2_left H2_right
    }
  },
  {
    cases H2,
    cases H2_right,
    {
      apply or.intro_left,
      apply IH_P,
      apply or.intro_right, exact and.intro H2_left H2_right
    },
    {
      apply or.intro_right,
      apply IH_Q,
      apply or.intro_right, exact and.intro H2_left H2_right
    }
  }
},
case sub_is_def.abs_same : y P x N IH_1
{
  rewrite simp_abs_same IH_1,
  cases H2,
  {
    cases H2, exact H2_left
  },
  {
    cases H2,
    simp only [simp_term_abs] at H2_right,
    cases H2_right, specialize H2_right_right IH_1, contradiction
  }
},
case sub_is_def.abs_diff_nel : y P x N IH_1 IH_2
{
  rewrite lemma_1_2_5_i_b IH_2,
  cases H2,
  cases H2, exact H2_left,
  cases H2, specialize IH_2 H2_right, contradiction
},
case sub_is_def.abs_diff : y P x N IH_1 IH_2 IH_3 IH_4
{
  rewrite simp_abs_diff IH_1,
  simp only [simp_term_abs] at H2,
  simp only [simp_term_abs],
  cases H2,
  {
    cases H2, cases H2_left,
    apply and.intro,
    apply IH_4, apply or.intro_left, exact and.intro H2_left_left H2_right,
    exact H2_left_right
  },
  {
    cases H2, cases H2_right,
    apply and.intro,
    apply IH_4, apply or.intro_right, exact and.intro H2_left H2_right_left,
    intros h, apply IH_2, rewrite <- h, exact H2_left
  }
}
end

lemma lemma_1_2_5_ii
{M : term} {x : var} {N : term} {z : var}
(H1 : M [ x := N ] is_def) :
z ∈ FV (M [ x := N ]) ↔ (z ∈ FV M ∧ x ≠ z) ∨ (z ∈ FV N ∧ x ∈ FV M) :=
iff.intro (lemma_1_2_5_ii_right M x N z H1) (lemma_1_2_5_ii_left M x N z H1)


lemma lemma_1_2_5_iii_a
{M : term} {x : var} :
M [ x  := (term.var x) ] is_def :=
begin
induction M,
case term.var : y
{
  exact sub_is_def.var
},
case term.app : P Q IH_P IH_Q
{
  exact sub_is_def.app IH_P IH_Q
},
case term.abs : y P IH
{
  by_cases h_xy : x = y,
  {
    exact sub_is_def.abs_same h_xy
  },
  {
    have s1 : y ≠ x, intro h2, apply h_xy, symmetry, exact h2,
    have s2 : y ∉ FV (term.var x), simp only [simp_term_var], exact s1,
    exact sub_is_def.abs_diff h_xy s2 IH
  }
}
end

lemma lemma_1_2_5_iii_b
{M : term} {x : var} :
M [ x := (term.var x) ] = M :=
begin
induction M,
case term.var : y
{
  by_cases h_xy : x = y,
  rewrite h_xy, apply if_pos, reflexivity,
  exact if_neg h_xy
},
case term.app : P Q IH_P IH_Q
{
  unfold sub, rewrite IH_P, rewrite IH_Q
},
case term.abs : y P IH
{
  by_cases h_xy : x = y,
  {
    rewrite <- IH,
    exact if_pos h_xy
  },
  {
    rewrite simp_abs_diff h_xy,
    rewrite IH
  }
}
end

lemma lemma_1_2_5_iii
{M : term} {x : var} :
is_sub M x (term.var x) M :=
begin
induction M,
case term.var : y
{
  by_cases h_xy : x = y,
  rewrite h_xy, apply is_sub.var_same, reflexivity,
  exact is_sub.var_diff h_xy
},
case term.app : P Q IH_P IH_Q
{
  exact is_sub.app IH_P IH_Q
},
case term.abs : y P IH
{
  by_cases h_xy : x = y,
  exact is_sub.abs_same h_xy,
  apply is_sub.abs_diff h_xy,
  intro h, apply h_xy, symmetry, simp only [simp_term_var] at h, exact h, exact IH
}
end


lemma lemma_1_2_6_a_left
(M N L : term) (x y : var)
(H1 : M [ x := N ] is_def)
(H2 : N [ y := L ] is_def)
(H3 : (M [ x := N ]) [ y := L ] is_def)
(H4 : x ≠ y)
(H5 : x ∉ FV L ∨ y ∉ FV M) :
M [ y := L ] is_def :=
begin
induction M,
case term.var : z
{
  exact sub_is_def.var
},
case term.app : P Q IH_P IH_Q
{
  cases H1,
  cases H3,
  simp only [simp_term_app_not] at H5,
  apply sub_is_def.app,
  {
    apply IH_P H1_ᾰ H3_ᾰ,
    cases H5,
    apply or.intro_left, exact H5,
    cases H5, apply or.intro_right, exact H5_left,
  },
  {
    apply IH_Q H1_ᾰ_1 H3_ᾰ_1,
    cases H5,
    apply or.intro_left, exact H5,
    cases H5, apply or.intro_right, exact H5_right
  }
},
case term.abs : z P
{
  cases H1,
  {
    rewrite simp_abs_same H1_ᾰ at H3,
    exact H3
  },
  {
    rewrite simp_abs_diff H1_ᾰ at H3,
    have s1 : P [ x := N ] = P, exact misc_7' H1_ᾰ_1 H1_ᾰ,
    rewrite s1 at H3,
    exact H3
  },
  {
    rewrite simp_abs_diff H1_ᾰ at H3,
    cases H3,
    {
      exact sub_is_def.abs_same H3_ᾰ
    },
    {
      apply sub_is_def.abs_diff_nel H3_ᾰ,
      have s1 : y ∉ FV (P [ x := N ]), exact misc_7 H3_ᾰ_1 H3_ᾰ,
      have s2 : y ∉ FV P,
      simp only [lemma_1_2_5_ii H1_ᾰ_2] at s1,
      push_neg at s1,
      cases s1, intros h, specialize s1_left h, apply H4, exact s1_left,
      exact misc_5 s2
    },
    {
      apply sub_is_def.abs_diff H3_ᾰ H3_ᾰ_1,
      apply M_ih H1_ᾰ_2 H3_ᾰ_2,
      cases H5,
      apply or.intro_left, exact H5,
      apply or.intro_right, exact misc_7 H5 H3_ᾰ
    }
  }
}
end

lemma lemma_1_2_6_a_right
(M N L : term) (x y : var)
(H1 : M [ x := N ] is_def)
(H2 : N [ y := L ] is_def)
(H3 : (M [ x := N ]) [ y := L ] is_def)
(H4 : x ≠ y)
(H5 : x ∉ FV L ∨ y ∉ FV M) :
(M [ y := L ]) [ x := N [ y := L ] ] is_def :=
begin
induction M,
case term.var : z
{
  by_cases h_yz : y = z,
  {
    rewrite simp_var_same h_yz,
    cases H5,
    exact lemma_1_2_5_i_a H5,
    simp only [simp_term_var] at H5, specialize H5 h_yz, contradiction
  },
  {
    rewrite simp_var_diff h_yz,
    exact sub_is_def.var
  }
},
case term.app : P Q IH_1 IH_2
{
  cases H1,
  cases H3,
  simp only [simp_term_app_not] at H5,
  apply sub_is_def.app,
  apply IH_1 H1_ᾰ H3_ᾰ,
  cases H5,
  apply or.intro_left, exact H5,
  cases H5, apply or.intro_right, exact H5_left,
  apply IH_2 H1_ᾰ_1 H3_ᾰ_1,
  cases H5,
  apply or.intro_left, exact H5,
  cases H5, apply or.intro_right, exact H5_right
},
case term.abs : z P
{
  cases H1,
  {
    have s1 : y ≠ z, rewrite H1_ᾰ at H4, symmetry, exact H4,
    rewrite simp_abs_diff s1,
    exact sub_is_def.abs_same H1_ᾰ
  },
  {
    rewrite simp_abs_diff H1_ᾰ at H3,
    have s1 : x ∉ FV P, exact misc_7 H1_ᾰ_1 H1_ᾰ,
    rewrite lemma_1_2_5_i_b s1 at H3,
    cases H3,
    {
      rewrite simp_abs_same H3_ᾰ,
      apply sub_is_def.abs_diff_nel H1_ᾰ, exact misc_5 s1
    },
    {
      rewrite lemma_1_2_5_i_b H3_ᾰ_1,
      exact lemma_1_2_5_i_a H1_ᾰ_1
    },
    {
      rewrite simp_abs_diff H3_ᾰ,
      apply sub_is_def.abs_diff_nel H1_ᾰ,
      apply misc_5,
      simp only [lemma_1_2_5_ii H3_ᾰ_2], push_neg,
      apply and.intro,
      intros, specialize s1 ᾰ, contradiction,
      intros,
      cases H5,
      specialize H5 ᾰ, contradiction,
      exact misc_7 H5 H3_ᾰ
    }
  },
  {
    rewrite simp_abs_diff H1_ᾰ at H3,
    cases H3,
    {
      rewrite simp_abs_same H3_ᾰ,
      apply sub_is_def.abs_diff H1_ᾰ,
      rewrite H3_ᾰ, rewrite lemma_1_2_5_i_b H1_ᾰ_1, exact H1_ᾰ_1,
      rewrite H3_ᾰ, rewrite lemma_1_2_5_i_b H1_ᾰ_1, exact H1_ᾰ_2
    },
    {
      rewrite simp_abs_diff H3_ᾰ,
      have s1 : y ∉ FV (P [ x := N ]), exact misc_7 H3_ᾰ_1 H3_ᾰ,
      simp only [lemma_1_2_5_ii H1_ᾰ_2] at s1, push_neg at s1, cases s1,
      have s2 : y ∉ FV P, intros h, specialize s1_left h, apply H4, exact s1_left,
      rewrite lemma_1_2_5_i_b s2,
      by_cases y ∈ FV N,
      {
        specialize s1_right h,
        have s3 : x ∉ FV (term.abs z P), exact misc_5 s1_right,
        exact lemma_1_2_5_i_a s3
      },
      {
        rewrite lemma_1_2_5_i_b h,
        exact sub_is_def.abs_diff H1_ᾰ H1_ᾰ_1 H1_ᾰ_2
      }
    },
    {
      rewrite simp_abs_diff H3_ᾰ,
      apply sub_is_def.abs_diff H1_ᾰ,
      simp only [lemma_1_2_5_ii H2], push_neg,
      apply and.intro,
      intros, specialize H1_ᾰ_1 ᾰ, contradiction,
      intros, specialize H3_ᾰ_1 ᾰ, contradiction,
      apply M_ih H1_ᾰ_2 H3_ᾰ_2,
      cases H5,
      apply or.intro_left, exact H5,
      apply or.intro_right, exact misc_7 H5 H3_ᾰ
    }
  }
}
end


lemma lemma_1_2_6_b
(M N L : term) (x y : var)
(H1 : M [ x := N ] is_def)
(H2 : N [ y := L ] is_def)
(H3 : (M [ x := N ]) [ y := L ] is_def)
(H4 : x ≠ y)
(H5 : x ∉ FV L ∨ y ∉ FV M) :
M [ x := N ] [ y := L ] = M [ y := L ] [ x := N [ y := L ] ] :=
begin
induction M,
case term.var : z
{
  by_cases h_xz : x = z,
  {
    have s1 : y ≠ z, rewrite <- h_xz, symmetry, exact H4,
    rewrite simp_var_diff s1,
    rewrite simp_var_same h_xz, rewrite simp_var_same h_xz
  },
  {
    rewrite simp_var_diff h_xz,
    by_cases h_yz : y = z,
    {
      rewrite simp_var_same h_yz,
      cases H5,
      {
        rewrite lemma_1_2_5_i_b H5,
      },
      {
        simp only [simp_term_var] at H5,
        specialize H5 h_yz, contradiction
      }
    },
    {
      rewrite simp_var_diff h_yz,
      rewrite simp_var_diff h_xz
    }
  }
},
case term.app : P Q IH_P IH_Q
{
  cases H1,
  cases H3,
  simp only [simp_term_app_not] at H5,
  cases H5,
  {
    have s1 : P [ x := N ] [ y := L ] = P [ y := L ] [ x:= N [ y:= L ] ],
    apply IH_P H1_ᾰ H3_ᾰ, apply or.intro_left, exact H5,
    have s2 : Q [ x := N ] [ y := L ] = Q [ y := L ] [ x:= N [ y:= L ] ],
    apply IH_Q H1_ᾰ_1 H3_ᾰ_1, apply or.intro_left, exact H5,
    unfold sub, rewrite s1, rewrite s2
  },
  {
    cases H5,
    have s1 : P [ x := N ] [ y := L ] = P [ y := L ] [ x:= N [ y:= L ] ],
    apply IH_P H1_ᾰ H3_ᾰ, apply or.intro_right, exact H5_left,
    have s2 : Q [ x := N ] [ y := L ] = Q [ y := L ] [ x:= N [ y:= L ] ],
    apply IH_Q H1_ᾰ_1 H3_ᾰ_1, apply or.intro_right, exact H5_right,
    unfold sub, rewrite s1, rewrite s2
  }
},
case term.abs : z P
{
  cases H1,
  {
    rewrite simp_abs_same H1_ᾰ,
    have s1 : y ≠ z, rewrite <- H1_ᾰ, symmetry, exact H4,
    rewrite simp_abs_diff s1,
    rewrite simp_abs_same H1_ᾰ
  },
  {
    rewrite simp_abs_diff H1_ᾰ,
    rewrite simp_abs_diff H1_ᾰ at H3,
    cases H3,
    {
      have s1 : x ∉ FV P, exact misc_7 H1_ᾰ_1 H1_ᾰ,
      rewrite lemma_1_2_5_i_b s1,
      rewrite simp_abs_same H3_ᾰ,
      rewrite simp_abs_diff H1_ᾰ,
      rewrite lemma_1_2_5_i_b s1
    },
    {
      have s1 : x ∉ FV P, exact misc_7 H1_ᾰ_1 H1_ᾰ,
      rewrite lemma_1_2_5_i_b s1,
      rewrite lemma_1_2_5_i_b s1 at H3_ᾰ_1,
      rewrite simp_abs_diff H3_ᾰ,
      have s2 : y ∉ FV P, exact misc_7 H3_ᾰ_1 H3_ᾰ,
      rewrite lemma_1_2_5_i_b s2,
      rewrite simp_abs_diff H1_ᾰ,
      rewrite lemma_1_2_5_i_b s1,
    },
    {
      have s1 : x ∉ FV P, exact misc_7 H1_ᾰ_1 H1_ᾰ,
      rewrite lemma_1_2_5_i_b s1,
      rewrite simp_abs_diff H3_ᾰ,
      rewrite simp_abs_diff H1_ᾰ,
      have s2 : P [ x := N ] is_def, exact lemma_1_2_5_i_a s1,
      have s3 : x ∉ FV L ∨ y ∉ FV P, cases H5, apply or.intro_left, exact H5, apply or.intro_right, exact misc_7 H5 H3_ᾰ,
      specialize M_ih s2 H3_ᾰ_2 s3,
      rewrite <- M_ih, rewrite lemma_1_2_5_i_b s1
    }
  },
  {
    rewrite simp_abs_diff H1_ᾰ,
    rewrite simp_abs_diff H1_ᾰ at H3,
    cases H3,
    {
      rewrite simp_abs_same H3_ᾰ,
      rewrite simp_abs_same H3_ᾰ,
      rewrite simp_abs_diff H1_ᾰ,
      rewrite <- H3_ᾰ at H1_ᾰ_1,
      rewrite lemma_1_2_5_i_b H1_ᾰ_1
    },
    {
      rewrite simp_abs_diff H3_ᾰ,
      rewrite simp_abs_diff H3_ᾰ,
      rewrite simp_abs_diff H1_ᾰ,
      have s1 : y ∉ FV (P [ x := N ]), exact misc_7 H3_ᾰ_1 H3_ᾰ,
      have s2 : P [ x := N ] [ y := L ] is_def, exact lemma_1_2_5_i_a s1,
      have s3 : x ∉ FV L ∨ y ∉ FV P, cases H5, apply or.intro_left, exact H5, apply or.intro_right, exact misc_7 H5 H3_ᾰ,
      specialize M_ih H1_ᾰ_2 s2 s3,
      rewrite M_ih
    },
    {
      rewrite simp_abs_diff H3_ᾰ,
      rewrite simp_abs_diff H3_ᾰ,
      rewrite simp_abs_diff H1_ᾰ,
      have s1 : x ∉ FV L ∨ y ∉ FV P, cases H5, apply or.intro_left, exact H5, apply or.intro_right, exact misc_7 H5 H3_ᾰ,
      specialize M_ih H1_ᾰ_2 H3_ᾰ_2 s1,
      rewrite M_ih
    }
  }
}
end
