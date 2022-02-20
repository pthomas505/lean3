import tactic

namespace hidden


lemma not_not_1 {P : Prop} : ¬ ¬ P → P :=
assume a1 :  ¬ ¬ P,
by_contradiction (
  assume a2 : ¬ P,
  show false, from a1 a2
)

lemma not_not_2 {P : Prop} : P → ¬ ¬ P :=
assume a1 : P,
assume a2 : ¬ P,
show false, from a2 a1

lemma not_not {P : Prop} : ¬ ¬ P ↔ P :=
iff.intro not_not_1 not_not_2

--------------------------------------------------------------------------------

lemma contrapose_1 {P Q : Prop} : (P → Q) → (¬ Q → ¬ P) :=
assume a1 : P → Q,
assume a2: ¬ Q,
by_contradiction (
  assume a3 : ¬ ¬ P,
  have s1 : P := not_not_1 a3,
  have s2 : Q := a1 s1,
  show false, from a2 s2
)

lemma contrapose_2 {P Q : Prop} : (P → ¬ Q) → (Q → ¬ P) :=
assume a1 : P → ¬ Q,
assume a2 : Q,
by_contradiction (
  assume a3 : ¬ ¬ P,
  have s1 : P := not_not_1 a3,
  have s2 : ¬ Q := a1 s1,
  show false, from s2 a2
)

lemma contrapose_3 {P Q : Prop} : (¬ P → Q) → (¬ Q → P) :=
assume a1 : ¬ P → Q,
assume a2 : ¬ Q,
by_contradiction (
  assume a3 : ¬ P,
  have s1 : Q := a1 a3,
  show false, from a2 s1
)

lemma contrapose_4 {P Q : Prop} : (¬ P → ¬ Q) → (Q → P) :=
assume a1 : ¬ P → ¬ Q,
assume a2 : Q,
by_contradiction (
  assume a3 : ¬ P,
  have s1 : ¬ Q := a1 a3,
  show false, from s1 a2
)

--------------------------------------------------------------------------------

lemma dm_1_a {P Q : Prop} : ¬ (P ∧ Q) → (¬ P ∨ ¬ Q) :=
assume a1 : ¬ (P ∧ Q),
by_contradiction (
  assume a2 : ¬ (¬ P ∨ ¬ Q),
  have s1 : P := (
    by_contradiction (
      assume a3 : ¬ P,
      have s2 : ¬ P ∨ ¬ Q := or.intro_left (¬ Q) a3,
      show false, from a2 s2
    )
  ),
  have s3 : Q := (
    by_contradiction (
      assume a4 : ¬ Q,
      have s4 : ¬ P ∨ ¬ Q := or.intro_right (¬ P) a4,
      show false, from a2 s4
    )
  ),
  have s5 : P ∧ Q := and.intro s1 s3,
  show false, from a1 s5
)

lemma dm_1_b {P Q : Prop} : ¬ (P ∧ ¬ Q) → (¬ P ∨ Q) :=
assume a1 : ¬ (P ∧ ¬ Q),
by_contradiction (
  assume a2 : ¬ (¬ P ∨ Q),
  have s1 : P := (
    by_contradiction (
      assume a3 : ¬ P,
      have s2 : ¬ P ∨ Q := or.intro_left Q a3,
      show false, from a2 s2
    )
  ),
  have s3 : ¬ Q := (
    by_contradiction (
      assume a4 : ¬ ¬ Q,
      have s4 : Q := not_not_1 a4,
      have s5 : ¬ P ∨ Q := or.intro_right (¬ P) s4,
      show false, from a2 s5
    )
  ),
  have s6 : P ∧ ¬ Q := and.intro s1 s3,
  show false, from a1 s6
)

lemma dm_1_c {P Q : Prop} : ¬ (¬ P ∧ Q) → (P ∨ ¬ Q) :=
assume a1 : ¬ (¬ P ∧ Q),
by_contradiction (
  assume a2 : ¬ (P ∨ ¬ Q),
  have s1 : ¬ P := (
    by_contradiction (
      assume a3 : ¬ ¬ P,
      have s2 : P := not_not_1 a3,
      have s3 : P ∨ ¬ Q := or.intro_left (¬ Q) s2,
      show false, from a2 s3
    )
  ),
  have s4 : Q := (
    by_contradiction (
      assume a4 : ¬ Q,
      have s5 : P ∨ ¬ Q := or.intro_right P a4,
      show false, from a2 s5
    )
  ),
  have s6 : ¬ P ∧ Q := and.intro s1 s4,
  show false, from a1 s6
)

lemma dm_1_d {P Q : Prop} : ¬ (¬ P ∧ ¬ Q) → (P ∨ Q) :=
assume a1 : ¬ (¬ P ∧ ¬ Q),
by_contradiction (
  assume a2 : ¬ (P ∨ Q),
  have s1 : ¬ P := (
    by_contradiction (
      assume a3 : ¬ ¬ P,
      have s2 : P := not_not_1 a3,
      have s3 : P ∨ Q := or.intro_left Q s2,
      show false, from a2 s3
    )
  ),
  have s4 : ¬ Q := (
    by_contradiction (
      assume a4 : ¬ ¬ Q,
      have s5 : Q := not_not_1 a4,
      have s6 : P ∨ Q := or.intro_right P s5,
      show false, from a2 s6
    )
  ),
  have s7 : ¬ P ∧ ¬ Q := and.intro s1 s4,
  show false, from a1 s7
)


lemma dm_2_a {P Q : Prop} : (¬ P ∨ ¬ Q) → ¬ (P ∧ Q) :=
assume a1 : ¬ P ∨ ¬ Q,
assume a2 : P ∧ Q,
or.elim a1
(
  assume a3 : ¬ P,
  have s1 : P := and.left a2,
  show false, from a3 s1
)
(
  assume a4 : ¬ Q,
  have s2 : Q := and.right a2,
  show false, from a4 s2
)

lemma dm_2_b {P Q : Prop} : (¬ P ∨ Q) → ¬ (P ∧ ¬ Q) :=
assume a1 : ¬ P ∨ Q,
assume a2 : P ∧ ¬ Q,
or.elim a1
(
  assume a3 : ¬ P,
  have s1 : P := and.left a2,
  show false, from a3 s1
)
(
  assume a4 : Q,
  have s2 : ¬ Q := and.right a2,
  show false, from s2 a4
)

lemma dm_2_c {P Q : Prop} : (P ∨ ¬ Q) → ¬ (¬ P ∧ Q) :=
assume a1 : P ∨ ¬ Q,
assume a2 : ¬ P ∧ Q,
or.elim a1
(
  assume a3 : P,
  have s1 : ¬ P := and.left a2,
  show false, from s1 a3
)
(
  assume a4 : ¬ Q,
  have s2 : Q := and.right a2,
  show false, from a4 s2
)

lemma dm_2_d {P Q : Prop} : (P ∨ Q) → ¬ (¬ P ∧ ¬ Q) :=
assume a1 : P ∨ Q,
assume a2 : ¬ P ∧ ¬ Q,
or.elim a1
(
  assume a3 : P,
  have s1 : ¬ P := and.left a2,
  show false, from s1 a3
)
(
  assume a4 : Q,
  have s2 : ¬ Q := and.right a2,
  show false, from s2 a4
)

lemma dm_a {P Q : Prop} : ¬ (P ∧ Q) ↔ (¬ P ∨ ¬ Q) :=
iff.intro dm_1_a dm_2_a


lemma dm_3_a {P Q : Prop} : ¬ (P ∨ Q) → (¬ P ∧ ¬ Q) :=
assume a1 : ¬ (P ∨ Q),
have s1 : ¬ P := (
  by_contradiction (
    assume a2 : ¬ ¬ P,
    have s2 : P := not_not_1 a2,
    have s3 : P ∨ Q := or.intro_left Q s2,
    show false, from a1 s3
  )
),
have s4 : ¬ Q := (
  by_contradiction (
    assume a3 : ¬ ¬ Q,
    have s5 : Q := not_not_1 a3,
    have s6 : P ∨ Q := or.intro_right P s5,
    show false, from a1 s6
  )
),
and.intro s1 s4

lemma dm_3_b {P Q : Prop} : ¬ (P ∨ ¬ Q) → (¬ P ∧ Q) :=
assume a1 : ¬ (P ∨ ¬ Q),
have s1 : ¬ P := (
  by_contradiction (
    assume a2 : ¬ ¬ P,
    have s2 : P := not_not_1 a2,
    have s3 : P ∨ ¬ Q := or.intro_left (¬ Q) s2,
    show false, from a1 s3
  )
),
have s4 : Q := (
  by_contradiction (
    assume a3 : ¬ Q,
    have s5 : P ∨ ¬ Q := or.intro_right P a3,
    show false, from a1 s5
  )
),
and.intro s1 s4

lemma dm_3_c {P Q : Prop} : ¬ (¬ P ∨ Q) → (P ∧ ¬ Q) :=
assume a1 : ¬ (¬ P ∨ Q),
have s1 : P := (
  by_contradiction (
    assume a2 : ¬ P,
    have s2 : ¬ P ∨ Q := or.intro_left Q a2,
    show false, from a1 s2
  )
),
have s3 : ¬ Q := (
  by_contradiction (
    assume a3 : ¬ ¬ Q,
    have s4 : Q := not_not_1 a3,
    have s5 : ¬ P ∨ Q := or.intro_right (¬ P) s4,
    show false, from a1 s5
  )
),
and.intro s1 s3

lemma dm_3_d {P Q : Prop} : ¬ (¬ P ∨ ¬ Q) → (P ∧ Q) :=
assume a1 : ¬ (¬ P ∨ ¬ Q),
have s1 : P := (
  by_contradiction (
    assume a2 : ¬ P,
    have s2 : ¬ P ∨ ¬ Q := or.intro_left (¬ Q) a2,
    show false, from a1 s2
  )
),
have s3 : Q := (
  by_contradiction (
    assume a3 : ¬ Q,
    have s4 : ¬ P ∨ ¬ Q := or.intro_right (¬ P) a3,
    show false, from a1 s4
  )
),
and.intro s1 s3


lemma dm_4_a {P Q : Prop} : (¬ P ∧ ¬ Q) → ¬ (P ∨ Q) :=
assume a1 : ¬ P ∧ ¬ Q,
assume a2 : P ∨ Q,
or.elim a2
(
  assume a3 : P,
  have s1 : ¬ P := and.left a1,
  show false, from s1 a3
)
(
  assume a4 : Q,
  have s2 : ¬ Q := and.right a1,
  show false, from s2 a4
)

lemma dm_4_b {P Q : Prop} : (¬ P ∧ Q) → ¬ (P ∨ ¬ Q) :=
assume a1 : ¬ P ∧ Q,
assume a2 : P ∨ ¬ Q,
or.elim a2
(
  assume a3 : P,
  have s1 : ¬ P := and.left a1,
  show false, from s1 a3
)
(
  assume a4 : ¬ Q,
  have s2 : Q := and.right a1,
  show false, from a4 s2
)

lemma dm_4_c {P Q : Prop} : (P ∧ ¬ Q) → ¬ (¬ P ∨ Q) :=
assume a1 : P ∧ ¬ Q,
assume a2 : ¬ P ∨ Q,
or.elim a2
(
  assume a3 : ¬ P,
  have s1 : P := and.left a1,
  show false, from a3 s1
)
(
  assume a4 : Q,
  have s2 : ¬ Q := and.right a1,
  show false, from s2 a4
)

lemma dm_4_d {P Q : Prop} : (P ∧ Q) → ¬ (¬ P ∨ ¬ Q) :=
assume a1 : P ∧ Q,
assume a2 : ¬ P ∨ ¬ Q,
or.elim a2
(
  assume a3 : ¬ P,
  have s1 : P := and.left a1,
  show false, from a3 s1
)
(
  assume a4 : ¬ Q,
  have s2 : Q := and.right a1,
  show false, from a4 s2
)

lemma dm_b {P Q : Prop} : ¬ (P ∨ Q) ↔ (¬ P ∧ ¬ Q) :=
iff.intro dm_3_a dm_4_a

--------------------------------------------------------------------------------

lemma dm_quant_cp_1 {α : Type} {P : α → Prop} : ¬ (∃ x : α, ¬ P x) → (∀ x : α, P x) :=
assume a1 : ¬ (∃ x : α, ¬ P x),
assume x' : α,
by_contradiction (
  assume a2 : ¬ P x',
  have s1 : ∃ x : α, ¬ P x := exists.intro x' a2,
  show false, from a1 s1
)

lemma dm_quant_1 {α : Type} {P : α → Prop} : ¬ (∀ x : α, P x) → (∃ x : α, ¬ P x) :=
contrapose_3 dm_quant_cp_1

lemma dm_quant_2 {α : Type} {P : α → Prop} : (∃ x : α, ¬ P x) → ¬ (∀ x : α, P x) :=
assume a1 : ∃ x : α, ¬ P x,
exists.elim a1 (
  assume x' : α,
  assume a2 : ¬ P x',
  assume a3 : ∀ x : α, P x,
  have s1 : P x' := a3 x',
  show false, from a2 s1
)

lemma dm_quant_a {α : Type} {P : α → Prop} : ¬ (∀ x : α, P x) ↔ (∃ x : α, ¬ P x) :=
iff.intro dm_quant_1 dm_quant_2


lemma dm_quant_3 {α : Type} {P : α → Prop} : ¬ (∃ x : α, P x) → (∀ x : α, ¬ P x) :=
assume a1 : ¬ (∃ x : α, P x),
assume x' : α,
by_contradiction (
  assume a2 : ¬ ¬ P x',
  have s1 : P x' := not_not_1 a2,
  have s2 : ∃ x : α, P x := exists.intro x' s1,
  show false, from a1 s2
)

lemma dm_quant_4 {α : Type} {P : α → Prop} : (∀ x : α, ¬ P x) → ¬ (∃ x : α, P x) :=
assume a1 : ∀ x : α, ¬ P x,
assume a2 : ∃ x : α, P x,
exists.elim a2 (
  assume x' : α,
  assume a3 : P x',
  have s1 : ¬ P x' := a1 x',
  show false, from s1 a3
)

lemma dm_quant_b {α : Type} {P : α → Prop} : ¬ (∃ x : α, P x) ↔ (∀ x : α, ¬ P x) :=
iff.intro dm_quant_3 dm_quant_4

--------------------------------------------------------------------------------

lemma dm_quant_set_cp_1 {α : Type} {S : set α} {P : α → Prop} : ¬ (∃ x ∈ S, ¬ P x) → (∀ x ∈ S, P x) :=
assume a1 : ¬ (∃ x ∈ S, ¬ P x),
assume x' : α,
assume a2 : x' ∈ S,
by_contradiction (
  assume a3 : ¬ P x',
  have s1 : ∃ x ∈ S, ¬ P x := exists.intro x' (exists.intro a2 a3),
  show false, from a1 s1
)

lemma dm_quant_set_1 {α : Type} {S : set α} {P : α → Prop} : ¬ (∀ x ∈ S, P x) → (∃ x ∈ S, ¬ P x) :=
contrapose_3 dm_quant_set_cp_1

lemma dm_quant_set_2 {α : Type} {S : set α} {P : α → Prop} : (∃ x ∈ S, ¬ P x) → ¬ (∀ x ∈ S, P x) :=
assume a1 : ∃ x ∈ S, ¬ P x,
exists.elim a1 (
  assume x' : α,
  assume a2 : ∃ (H : x' ∈ S), ¬ P x',
  exists.elim a2 (
    assume H0 : x' ∈ S,
    assume a3 : ¬ P x',
    assume a4 : ∀ x ∈ S, P x,
    have s1 : P x' := a4 x' H0,
    show false, from a3 s1
  )
)

lemma dm_quant_set_a {α : Type} {S : set α} {P : α → Prop} : ¬ (∀ x ∈ S, P x) ↔ (∃ x ∈ S, ¬ P x) :=
iff.intro dm_quant_set_1 dm_quant_set_2


lemma dm_quant_set_3 {α : Type} {S : set α} {P : α → Prop} : ¬ (∃ x ∈ S, P x) → (∀ x ∈ S, ¬ P x) :=
assume a1 : ¬ (∃ x ∈ S, P x),
assume x' : α,
assume a2 : x' ∈ S,
by_contradiction (
  assume a3 : ¬ ¬ P x',
  have s1 : P x' := not_not_1 a3,
  have s2 : ∃ x ∈ S, P x := exists.intro x' (exists.intro a2 s1),
  show false, from a1 s2
)

lemma dm_quant_set_4 {α : Type} {S : set α} {P : α → Prop} : (∀ x ∈ S, ¬ P x) → ¬ (∃ x ∈ S, P x) :=
assume a1 : ∀ x ∈ S, ¬ P x,
assume a2 : ∃ x ∈ S, P x,
exists.elim a2 (
  assume x' : α,
  assume a3 : ∃ (H : x' ∈ S), P x',
  exists.elim a3 (
    assume H0 : x' ∈ S,
    assume a4 : P x',
    have s1 : ¬ P x' := a1 x' H0,
    show false, from s1 a4
  )
)

lemma dm_quant_set_b {α : Type} {S : set α} {P : α → Prop} : ¬ (∃ x ∈ S, P x) ↔ (∀ x ∈ S, ¬ P x) :=
iff.intro dm_quant_set_3 dm_quant_set_4

--------------------------------------------------------------------------------

example {α : Type} {P Q : α → Prop} (h : ∀ x : α, P x → Q x) : (∀ x : α, P x) → (∀ x : α, Q x) :=
assume a1 : ∀ x : α, P x,
assume x' : α,
have s1 : P x' := a1 x',
have s2 : P x' → Q x' := h x',
s2 s1

example {α : Type} {S : set α} {P Q : α → Prop} (h : ∀ x ∈ S, P x → Q x) : (∀ x ∈ S, P x) → (∀ x ∈ S, Q x) :=
assume a1 : ∀ x ∈ S, P x,
assume x' : α,
assume a2 : x' ∈ S,
have s1 : P x' := a1 x' a2,
have s2 : P x' → Q x' := h x' a2,
s2 s1


example {α : Type} {P Q : α → Prop} (h : ∀ x : α, P x → Q x) : (∃ x : α, P x) → (∃ x : α, Q x) :=
assume a1 : ∃ x : α, P x,
exists.elim a1 (
  assume x' : α,
  assume a2 : P x',
  have s1 : P x' → Q x' := h x',
  have s2 : Q x' := s1 a2,
  exists.intro x' s2
)

example {α : Type} {S : set α} {P Q : α → Prop} (h : ∀ x ∈ S, P x → Q x) : (∃ x ∈ S, P x) → (∃ x ∈ S, Q x) :=
assume a1 : ∃ x ∈ S, P x,
exists.elim a1 (
  assume x' : α,
  assume a2 : ∃ (H : x' ∈ S), P x',
  exists.elim a2 (
    assume H0 : x' ∈ S,
    assume a3 : P x',
    have s1 : P x' → Q x' := h x' H0,
    have s2 : Q x' := s1 a3,
    exists.intro x' (exists.intro H0 s2)
  )
)

--------------------------------------------------------------------------------

lemma or_comm {P Q : Prop} : (P ∨ Q) → (Q ∨ P) :=
assume a1 : P ∨ Q,
or.elim a1
(
  assume a2 : P,
  or.intro_right Q a2
)
(
  assume a3 : Q,
  or.intro_left P a3
)


lemma or_implies_1 {P Q : Prop} : (P ∨ Q) → ¬ P → Q :=
assume a1 : P ∨ Q,
assume a2 : ¬ P,
or.elim a1
(
  assume a3 : P,
  false.elim (a2 a3)
)
(
  assume a4 : Q,
  a4
)

lemma or_implies_2 {P Q : Prop} : (P ∨ ¬ Q) → ¬ P → ¬ Q :=
assume a1 : P ∨ ¬ Q,
assume a2 : ¬ P,
or.elim a1
(
  assume a3 : P,
  false.elim (a2 a3)
)
(
  assume a4 : ¬ Q,
  a4
)

lemma or_implies_3 {P Q : Prop} : (¬ P ∨ Q) → P → Q :=
assume a1 : ¬ P ∨ Q,
assume a2 : P,
or.elim a1
(
  assume a3 : ¬ P,
  false.elim (a3 a2)
)
(
  assume a4 : Q,
  a4
)

lemma or_implies_4 {P Q : Prop} : (¬ P ∨ ¬ Q) → P → ¬ Q :=
assume a1 : ¬ P ∨ ¬ Q,
assume a2 : P,
or.elim a1
(
  assume a3 : ¬ P,
  false.elim (a3 a2)
)
(
  assume a4 : ¬ Q,
  a4
)

--------------------------------------------------------------------------------

lemma not_and_implies_1 {P Q : Prop} : ¬ (P ∧ Q) → P → ¬ Q :=
assume a1 : ¬ (P ∧ Q),
or_implies_4 (dm_1_a a1)

lemma not_and_implies_2 {P Q : Prop} : ¬ (P ∧ Q) → Q → ¬ P :=
assume a1 : ¬ (P ∧ Q),
or_implies_4 (or_comm (dm_1_a a1))


lemma not_and_implies_3 {P Q : Prop} : ¬ (P ∧ ¬ Q) → P → Q :=
assume a1 : ¬ (P ∧ ¬ Q),
or_implies_3 (dm_1_b a1)

lemma not_and_implies_4 {P Q : Prop} : ¬ (P ∧ ¬ Q) → ¬ Q → ¬ P :=
assume a1 : ¬ (P ∧ ¬ Q),
or_implies_2 (or_comm (dm_1_b a1))


lemma not_and_implies_5 {P Q : Prop} : ¬ (¬ P ∧ Q) → ¬ P → ¬ Q :=
assume a1 : ¬ (¬ P ∧ Q),
or_implies_2 (dm_1_c a1)

lemma not_and_implies_6 {P Q : Prop} : ¬ (¬ P ∧ Q) → Q → P :=
assume a1 : ¬ (¬ P ∧ Q),
or_implies_3 (or_comm (dm_1_c a1))


lemma not_and_implies_7 {P Q : Prop} : ¬ (¬ P ∧ ¬ Q) → ¬ P → Q :=
assume a1 : ¬ (¬ P ∧ ¬ Q),
or_implies_1 (dm_1_d a1)

lemma not_and_implies_8 {P Q : Prop} : ¬ (¬ P ∧ ¬ Q) → ¬ Q → P :=
assume a1 : ¬ (¬ P ∧ ¬ Q),
or_implies_1 (or_comm (dm_1_d a1))

--------------------------------------------------------------------------------

def set (α : Type) := α → Prop

-- a is an element of the set s.
def mem {α : Type} (a : α) (s : set α) : Prop := s a

notation x `∈` S := mem x S
notation x `∉` S := ¬ mem x S


-- The set containing only a.
def singleton {α : Type} (a : α) : set α := fun x, x = a

notation `{` x `}` := singleton x

example {α : Type} {a b : α} : mem a (singleton b) = (a = b) := by refl


-- The union of the sets s and t.
def union {α : Type} (s t : set α) : set α :=
fun x, (mem x s) ∨ (mem x t)

notation s `∪`  t := union s t

example {α : Type} {s t : set α} {x : α} : mem x (union s t) = ((mem x s) ∨ (mem x t)) := by refl


-- The intersection of the sets s and t.
def inter {α : Type} (s t : set α) : set α :=
fun x, (mem x s) ∧ (mem x t)

notation s `∩` t := inter s t

example {α : Type} {s t : set α} {x : α} : mem x (inter s t) = ((mem x s) ∧ (mem x t)) := by refl


-- The difference of the sets s and t.
def diff {α : Type} (s t : set α) : set α :=
fun x, (mem x s) ∧ ¬ (mem x t)

notation s `\` t := diff s t

example {α : Type} {s t : set α} {x : α} : mem x (diff s t) = ((mem x s) ∧ ¬ (mem x t)) := by refl


-- The complement of the set s.
def compl {α : Type} (s : set α) : set α :=
fun x, ¬ mem x s

example {α : Type} {s t : set α} {x : α} : mem x (compl s) = ¬ mem x s := by refl

--------------------------------------------------------------------------------

def var := ℕ

inductive pre_term : Type
| var : var → pre_term
| app : pre_term → pre_term → pre_term
| abs : var → pre_term → pre_term

notation `λ` y `.` P := pre_term.abs y P


def FV : pre_term → set var
| (pre_term.var x) := {x}
| (pre_term.app P Q) := (FV P) ∪ (FV Q)
| (pre_term.abs x P) := (FV P) \ {x}


-- sub_is_def M x N means M [ x := N ] is defined
inductive sub_is_def : pre_term → var → pre_term → Prop

-- y [ x := N ] is defined
| var (y : var) (x : var) (N : pre_term) :
  sub_is_def (pre_term.var y) x N

-- P [ x := N ] is defined → Q [ x := N ] is defined → (P Q) [ x := N ] is defined
| app (P : pre_term) (Q : pre_term) (x : var) (N : pre_term) :
  sub_is_def P x N → sub_is_def Q x N → sub_is_def (pre_term.app P Q) x N

-- x = y → ( λ y . P ) [ x := N ] is defined
| abs_same (y : var) (P : pre_term) (x : var) (N : pre_term) :
  x = y → sub_is_def (pre_term.abs y P) x N

-- x ≠ y → x ∉ FV ( λ y . P ) → ( λ y . P ) [ x := N ] is defined
| abs_diff_nel (y : var) (P : pre_term) (x : var) (N : pre_term) :
  x ≠ y → x ∉ FV (pre_term.abs y P) → sub_is_def (pre_term.abs y P) x N

-- x ≠ y → y ∉ FV ( N ) → P [ x := N ] is defined → ( λ y . P ) [ x := N ] is defined
| abs_diff (y : var) (P : pre_term) (x : var) (N : pre_term) :
  x ≠ y → y ∉ FV N → sub_is_def P x N → sub_is_def (pre_term.abs y P) x N

notation M `[` x `:=` N `]` `is_def` := sub_is_def M x N


-- M [ x := N ]
def sub : pre_term → var → pre_term → pre_term
-- if x = y then y [ x := N ] = N else y [ x := N ] = y
| (pre_term.var y) x N := if (x = y) then N else (pre_term.var y)

-- (P Q) [ x := N ] = (P [ x := N ] Q [ x := N ])
| (pre_term.app P Q) x N := pre_term.app (sub P x N) (sub Q x N)

-- if x = y then ( λ y . P ) [ x := N ] = ( λ y . P ) else ( λ y . P ) [ x := N ] = ( λ y . P [ x := N ] )
| (pre_term.abs y P) x N := if x = y then (pre_term.abs y P) else (pre_term.abs y (sub P x N))

notation M `[` x `:=` N `]` := sub M x N


lemma lemma_1_2_5_i_a (M : pre_term) (x : var) (N : pre_term) : x ∉ FV M → M [ x := N ] is_def :=
begin
assume a1 : x ∉ FV M,
induction M,
case pre_term.var : y
{
  -- M = pre_term.var y
  show (pre_term.var y) [ x := N ] is_def, by exact sub_is_def.var y x N
},
case pre_term.app : P Q IH_1 IH_2
{
  -- M = pre_term.app P Q
  have s1 : x ∉ FV (pre_term.app P Q), by exact a1,
  have s2 : x ∉ FV P → P [ x := N ] is_def, by exact IH_1,
  have s3 : x ∉ FV Q → Q [ x := N ] is_def, by exact IH_2,
  have s4 : (x ∉ FV P) ∧ (x ∉ FV Q), by exact dm_3_a s1,
  have s5 : P [ x := N ] is_def, by exact s2 (and.left s4),
  have s6 : Q [ x := N ] is_def, by exact s3 (and.right s4),
  show (pre_term.app P Q) [ x := N ] is_def, by exact sub_is_def.app P Q x N s5 s6
},
case pre_term.abs : y P
{
  -- M = pre_term.abs y P
  by_cases x = y,
  {
    have s7: x = y, by exact h,
    show (pre_term.abs y P) [ x := N ] is_def, by exact (sub_is_def.abs_same y P x N) s7
  },
  {
    have s8 : x ≠ y, by exact h,
    have s9 : x ∉ FV (pre_term.abs y P), by exact a1,
    show (pre_term.abs y P) [ x := N ] is_def, by exact (sub_is_def.abs_diff_nel y P x N) s8 s9
  }
}
end


lemma lemma_1_2_5_i_b (M : pre_term) (x : var) (N : pre_term) : x ∉ FV M → M [ x := N ] = M :=
begin
assume a1 : x ∉ FV M,
induction M,
case pre_term.var : y
{
  -- M = pre_term.var y
  have s1 : x ≠ y, by exact a1,
  show (pre_term.var y) [ x := N ] = (pre_term.var y), by exact if_neg s1
},
case pre_term.app : P Q IH_1 IH_2
{
  -- M = pre_term.app P Q
  have s2 : x ∉ FV (pre_term.app P Q), by exact a1,
  have s3 : x ∉ FV P → P [ x := N ] = P, by exact IH_1,
  have s4 : x ∉ FV Q → Q [ x := N ] = Q, by exact IH_2,
  have s5 : (x ∉ FV P) ∧ (x ∉ FV Q), by exact dm_3_a s2,
  have s6 : P [ x := N ] = P, by exact s3 (and.left s5),
  have s7 : Q [ x := N ] = Q, by exact s4 (and.right s5),
  have s8 : (pre_term.app P Q) [ x := N ] = pre_term.app (P [ x := N ]) (Q [ x := N ]), by refl,
  have s9 : pre_term.app (P [ x := N ]) (Q [ x := N ]) = pre_term.app P (Q [ x := N ]), by rw s6,
  have s10 : pre_term.app P (Q [ x := N ]) = pre_term.app P Q, by rw s7,
  show (pre_term.app P Q) [ x := N ] = pre_term.app P Q, by exact eq.trans (eq.trans s8 s9) s10
},
case pre_term.abs : y P IH
{
  -- M = pre_term.abs y P
  by_cases (x = y),
  {
    have s11 : x = y, by exact h,
    show (pre_term.abs y P) [ x := N ] = pre_term.abs y P, by exact if_pos s11
  },
  {
    have s12 : x ≠ y, by exact h,
    have s13 : x ∉ FV (pre_term.abs y P), by exact a1,
    have s14 : x ∉ FV P → P [ x := N ] = P, by exact IH,
    have s15 : x ∉ FV P, by exact not_and_implies_4 s13 s12,
    have s16 : P [ x := N ] = P, by exact s14 s15,
    have s17 : (pre_term.abs y P) [ x := N ] = pre_term.abs y (P [ x := N ]), by exact if_neg s12,
    have s18 : pre_term.abs y (P [ x := N ]) = pre_term.abs y P, by rw s16,
    show (pre_term.abs y P) [ x := N ] = pre_term.abs y P, by exact eq.trans s17 s18
  }
}
end

--------------------------------------------------------------------------------

class total_order (T : Type*) :=
(le : T → T → Prop)
(le_asymm : ∀ {x y : T}, le x y → le y x → x = y)
(le_trans : ∀ {x y z : T}, le x y → le y z → le x z)
(le_conn : ∀ {x y : T}, le x y ∨ le y x)

open total_order


-- x < y
def lt {T : Type*} [total_order T] (x y : T) : Prop := le x y ∧ ¬ x = y

-- x ≥ y
def ge {T : Type*} [total_order T] (x y : T) : Prop := le y x

-- x > y
def gt {T : Type*} [total_order T] (x y : T) : Prop := ge x y ∧ ¬ x = y


lemma ne_symm {α : Type*} {x y : α} : ¬ x = y → ¬ y = x :=
assume a1 : ¬ x = y,
assume a2 : y = x,
have s1 : x = y := eq.symm a2,
show false, from a1 s1


lemma lt_to_gt {T : Type*} [total_order T] {x y : T} : lt x y → gt y x :=
assume a1 : lt x y,
have s1 : le x y := and.left a1,
have s2 : ge y x := s1,
have s3 : ¬ x = y := and.right a1,
have s4 : ¬ y = x := ne_symm s3,
and.intro s1 s4

lemma gt_to_lt {T : Type*} [total_order T] {x y : T} : gt x y → lt y x :=
assume a1 : gt x y,
have s1 : ge x y := and.left a1,
have s2 : le y x := s1,
have s3 : ¬ x = y := and.right a1,
have s4 : ¬ y = x := ne_symm s3,
and.intro s1 s4


lemma ge_asymm {T : Type*} [total_order T] {x y : T} : ge x y → ge y x → x = y :=
assume a1 : ge x y,
assume a2 : ge y x,
have s1 : le y x := a1,
have s2 : le x y := a2,
le_asymm s2 s1


lemma ge_trans {T : Type*} [total_order T] {x y z : T} : ge x y → ge y z → ge x z :=
assume a1 : ge x y,
assume a2 : ge y z,
have s1 : le y x := a1,
have s2 : le z y := a2,
le_trans s2 s1


lemma ge_conn {T : Type*} [total_order T] {x y : T} : ge x y ∨ ge y x :=
have s1 : le x y ∨ le y x := le_conn,
or.elim s1
(
  assume a1 : le x y,
  have s2 : ge y x := a1,
  or.intro_right (ge x y) s2
)
(
  assume a2 : le y x,
  have s3 : ge x y := a2,
  or.intro_left (ge y x) s3
)


lemma le_refl {T : Type*} [total_order T] {x : T} : le x x :=
have s1 : le x x ∨ le x x := le_conn,
or.elim s1
(
  assume a1 : le x x,
  a1
)
(
  assume a2 : le x x,
  a2
)

lemma ge_refl {T : Type*} [total_order T] {x : T} : ge x x :=
have s1 : ge x x ∨ ge x x := ge_conn,
or.elim s1
(
  assume a1 : ge x x,
  a1
)
(
  assume a2 : ge x x,
  a2
)


lemma not_lt_refl {T : Type*} [total_order T] {x : T} : ¬ lt x x :=
assume a1 : lt x x,
have s1 : ¬ x = x := and.right a1,
have s2 : x = x := eq.refl x,
show false, from s1 s2

lemma not_gt_refl {T : Type*} [total_order T] {x : T} : ¬ gt x x :=
assume a1 : gt x x,
have s1 : ¬ x = x := and.right a1,
have s2 : x = x := eq.refl x,
show false, from s1 s2


lemma le_lt_trans {T : Type*} [total_order T] {x y z : T} : le x y → lt y z → lt x z :=
assume a1 : le x y,
assume a2 : lt y z,
have s1 : le y z := and.left a2,
have s2 : ¬ y = z := and.right a2,
have s3 : le x z := le_trans a1 s1,
have s4 : ¬ x = z :=
by_contradiction (
  assume a3: ¬ ¬ x = z,
  have s5 : x = z := not_not_1 a3,
  have s6 : le z y := eq.subst s5 a1,
  have s7 : y = z := le_asymm s1 s6,
  show false, from s2 s7
),
and.intro s3 s4

lemma lt_le_trans {T : Type*} [total_order T] {x y z : T} : lt x y → le y z → lt x z :=
assume a1 : lt x y,
assume a2 : le y z,
have s1 : le x y := and.left a1,
have s2 : ¬ x = y := and.right a1,
have s3 : le x z := le_trans s1 a2,
have s4 : ¬ x = z :=
by_contradiction (
  assume a3 : ¬ ¬ x = z,
  have s5 : x = z := not_not_1 a3,
  have s6 : le y x := eq.subst (eq.symm s5) a2,
  have s7 : x = y := le_asymm s1 s6,
  show false, from s2 s7
),
and.intro s3 s4

lemma lt_lt_trans {T : Type*} [total_order T] {x y z : T} : lt x y → lt y z → lt x z :=
assume a1 : lt x y,
assume a2 : lt y z,
have s1 : le x y := and.left a1,
le_lt_trans s1 a2


lemma ge_gt_trans {T : Type*} [total_order T] {x y z : T} : ge x y → gt y z → gt x z :=
assume a1 : ge x y,
assume a2 : gt y z,
have s1 : ge y z := and.left a2,
have s2 : ¬ y = z := and.right a2,
have s3 : ge x z := ge_trans a1 s1,
have s4 : ¬ x = z :=
by_contradiction (
  assume a3: ¬ ¬ x = z,
  have s5 : x = z := not_not_1 a3,
  have s6 : ge z y := eq.subst s5 a1,
  have s7 : y = z := ge_asymm s1 s6,
  show false, from s2 s7
),
and.intro s3 s4

lemma gt_ge_trans {T : Type*} [total_order T] {x y z : T} : gt x y → ge y z → gt x z :=
assume a1 : gt x y,
assume a2 : ge y z,
have s1 : ge x y := and.left a1,
have s2 : ¬ x = y := and.right a1,
have s3 : ge x z := ge_trans s1 a2,
have s4 : ¬ x = z :=
by_contradiction (
  assume a3 : ¬ ¬ x = z,
  have s5 : x = z := not_not_1 a3,
  have s6 : ge y x := eq.subst (eq.symm s5) a2,
  have s7 : x = y := ge_asymm s1 s6,
  show false, from s2 s7
),
and.intro s3 s4

lemma gt_gt_trans {T : Type*} [total_order T] {x y z : T} : gt x y → gt y z → gt x z :=
assume a1 : gt x y,
assume a2 : gt y z,
have s1 : ge x y := and.left a1,
ge_gt_trans s1 a2


lemma le_to_or {T : Type*} [total_order T] {x y : T} : le x y → (lt x y ∨ x = y) :=
assume a1 : le x y,
by_contradiction (
  assume a2 : ¬ (lt x y ∨ x = y),
  have s1 : ¬ lt x y ∧ ¬ x = y := dm_3_a a2,
  have s2 : ¬ (le x y ∧ ¬ x = y) := and.left s1,
  have s3 : ¬ x = y := and.right s1,
  have s4 : ¬ le x y ∨ x = y := dm_1_b s2,
  or.elim s4
  (
    assume a3 : ¬ le x y,
    show false, from a3 a1
  )
  (
    assume a4 : x = y,
    show false, from s3 a4
  )
)


lemma or_to_le {T : Type*} [total_order T] {x y : T} : (lt x y ∨ x = y) → le x y :=
assume a1 : lt x y ∨ x = y,
or.elim a1
(
  assume a2 : lt x y,
  have s1 : le x y ∧ ¬ x = y := a2,
  and.left s1
)
(
  assume a3 : x = y,
  have s2 : le x x := le_refl,
  eq.subst a3 s2
)


lemma ge_to_or {T : Type*} [total_order T] {x y : T} : ge x y → (gt x y ∨ x = y) :=
assume a1 : ge x y,
by_contradiction (
  assume a2 : ¬ (gt x y ∨ x = y),
  have s1 : ¬ gt x y ∧ ¬ x = y := dm_3_a a2,
  have s2 : ¬ (ge x y ∧ ¬ x = y) := and.left s1,
  have s3 : ¬ x = y := and.right s1,
  have s4 : ¬ ge x y ∨ x = y := dm_1_b s2,
  or.elim s4
  (
    assume a3 : ¬ ge x y,
    show false, from a3 a1
  )
  (
    assume a4 : x = y,
    show false, from s3 a4
  )
)

lemma or_to_ge {T : Type*} [total_order T] {x y : T} : (gt x y ∨ x = y) → ge x y :=
assume a1 : gt x y ∨ x = y,
or.elim a1
(
  assume a2 : gt x y,
  have s1 : ge x y ∧ ¬ x = y := a2,
  and.left s1
)
(
  assume a3 : x = y,
  have s2 : ge x x := ge_refl,
  eq.subst a3 s2
)


example {T : Type*} [total_order T] {x y : T} : lt x y → ¬ ge x y :=
assume a1 : lt x y,
assume a2 : ge x y,
have s1 : le x y := and.left a1,
have s2 : ¬ x = y := and.right a1,
have s3 : le y x := a2,
have s4 : x = y := le_asymm s1 s3,
show false, from s2 s4


example {T : Type*} [total_order T] {x y : T} : ¬ ge x y → ¬ x = y :=
assume a1 : ¬ ge x y,
assume a2 : x = y,
have s1 : ge x x := ge_refl,
have s2 : ge x y := eq.subst a2 s1,
show false, from a1 s2


example {T : Type*} [total_order T] {x y : T} : ¬ ge x y → le x y :=
assume a1 : ¬ ge x y,
have s1 : ¬ le y x := a1,
have s2 : le x y ∨ le y x := le_conn,
or.elim s2
(
  assume a2 : le x y,
  a2
)
(
  assume a3 : le y x,
  false.elim (s1 a3)
)


example {T : Type*} [total_order T] {x y : T} : gt x y → ¬ le x y :=
assume a1 : gt x y,
assume a2 : le x y,
have s1 : ge x y := and.left a1,
have s2 : ¬ x = y := and.right a1,
have s3 : ge y x := a2,
have s4 : x = y := ge_asymm s1 s3,
show false, from s2 s4


example {T : Type*} [total_order T] {x y : T} : ¬ le x y → ¬ x = y :=
assume a1 : ¬ le x y,
assume a2 : x = y,
have s1 : le x x := le_refl,
have s2 : le x y := eq.subst a2 s1,
show false, from a1 s2


example {T : Type*} [total_order T] {x y : T} : ¬ le x y → ge x y :=
assume a1 : ¬ le x y,
have s1 : ¬ ge y x := a1,
have s2 : ge x y ∨ ge y x := ge_conn,
or.elim s2
(
  assume a2 : ge x y,
  a2
)
(
  assume a3 : ge y x,
  false.elim (s1 a3)
)

--------------------------------------------------------------------------------

class field (F : Type) extends has_add F, has_neg F, has_zero F, has_mul F, has_inv F, has_one F :=
(add_assoc : ∀ x y z : F, x + (y + z) = (x + y) + z)
(add_comm : ∀ x y : F, x + y = y + x)
(add_neg_left : ∀ x : F, -x + x = 0)
(add_zero_left : ∀ x : F, 0 + x = x)
(mul_assoc : ∀ x y z : F, x * (y * z) = (x * y) * z)
(mul_comm : ∀ x y : F, x * y = y * x)
(mul_inv_left : ∀ x : F, ¬ x = 0 → x⁻¹ * x = 1)
(mul_one_left : ∀ x : F, 1 * x = x)
(dist_left : ∀ x y z : F, x * (y + z) = (x * y) + (x * z))
(zero_inv : (0 : F)⁻¹ = 0)

open hidden.field


lemma add_idempotent {F : Type} [field F] : ∀ x : F, x + x = x → x = 0 :=
assume x : F,
assume a1 : x + x = x,
calc
x   = 0 + x        : eq.symm (add_zero_left x)
... = (-x + x) + x : by rw (add_neg_left x)
... = -x + (x + x) : eq.symm (add_assoc (-x) x x)
... = -x + x       : by rw a1
... = 0            : add_neg_left x


lemma add_neg_right {F : Type} [field F] : ∀ x : F, x + -x = 0 :=
assume x : F,
have s1 : (x + -x) + (x + -x) = x + -x := (
calc
(x + -x) + (x + -x) = x + (-x + (x + -x)) : eq.symm (add_assoc x (-x) (x + -x))
                ... = x + ((-x + x) + -x) : by rw (add_assoc (-x) x (-x))
                ... = x + (0 + -x)        : by rw (add_neg_left x)
                ... = x + -x              : by rw (add_zero_left (-x))
),
add_idempotent (x + -x) s1


lemma add_zero_right {F : Type} [field F] : ∀ x : F, x + 0 = x :=
assume x : F,
calc
x + 0 = x + (-x + x) : by rw (add_neg_left x)
  ... = (x + -x) + x : add_assoc x (-x) x
  ... = 0 + x        : by rw add_neg_right
  ... = x            : add_zero_left x


example (F : Type) [field F] (neg' : F → F) (add_neg_left' : ∀ x : F, (neg' x) + x = 0) : ∀ x : F, neg' x = -x :=
assume x : F,
calc
neg' x = neg' x + 0        : eq.symm (add_zero_right (neg' x))
   ... = neg' x + (x + -x) : by rw (add_neg_right x)
   ... = (neg' x + x) + -x : add_assoc (neg' x) x (-x)
   ... = 0 + -x            : by rw (add_neg_left' x)
   ... = -x                : add_zero_left (-x)


example (F : Type) [field F] (zero' : F) (add_zero_left' : ∀ x : F, zero' + x = x) : zero' = 0 :=
have s1 : zero' + zero' = zero' := add_zero_left' zero',
add_idempotent zero' s1


lemma add_left_cancel {F : Type} [field F] : ∀ x y z : F, x + y = x + z → y = z :=
assume x y z : F,
assume a1 : x + y = x + z,
calc
y   = 0 + y        : eq.symm (add_zero_left y)
... = (-x + x) + y : by rw (add_neg_left x)
... = -x + (x + y) : eq.symm (add_assoc (-x) x y)
... = -x + (x + z) : by rw a1
... = (-x + x) + z : add_assoc (-x) x z
... = 0 + z        : by rw (add_neg_left x)
... = z            : add_zero_left z


lemma add_right_cancel {F : Type} [field F] : ∀ x y z : F, y + x = z + x → y = z :=
assume x y z : F,
assume a1 : y + x = z + x,
calc
y   = y + 0        : eq.symm (add_zero_right y)
... = y + (x + -x) : by rw (add_neg_right x)
... = (y + x) + -x : add_assoc y x (-x)
... = (z + x) + -x : by rw a1
... = z + (x + -x) : eq.symm (add_assoc z x (-x))
... = z + 0        : by rw (add_neg_right x)
... = z            : add_zero_right z


lemma add_1 {F : Type} [field F] : ∀ x y : F, x + y = x → y = 0 :=
assume x y : F,
assume a1 : x + y = x,
have s1 : x = x + 0 := eq.symm (add_zero_right x),
have s2 : x + y = x + 0 := eq.trans a1 s1,
add_left_cancel x y 0 s2


lemma add_2 {F : Type} [field F] : ∀ x y : F, x + y = 0 → y = -x :=
assume x y : F,
assume a1 : x + y = 0,
have s1 : 0 = x + -x := eq.symm (add_neg_right x),
have s2 : x + y = x + -x := eq.trans a1 s1,
add_left_cancel x y (-x) s2


lemma neg_neg {F : Type} [field F] : ∀ x : F, x = -(-x) :=
assume x : F,
have s1 : -x + x = 0 := add_neg_left x,
add_2 (-x) x s1


lemma mul_idempotent {F : Type} [field F] : ∀ x : F, ¬ x = 0 → x * x = x → x = 1 :=
assume x : F,
assume a1 : ¬ x = 0,
assume a2 : x * x = x,
calc
x   = 1 * x         : eq.symm (mul_one_left x)
... = (x⁻¹ * x) * x : by rw (mul_inv_left x a1)
... = x⁻¹ * (x * x) : eq.symm (mul_assoc x⁻¹ x x)
... = x⁻¹ * x       : by rw a2
... = 1             : mul_inv_left x a1


lemma mul_zero_right {F : Type} [field F] : ∀ x : F, x * 0 = 0 :=
assume x : F,
calc
x * 0 = 0 + (x * 0)                    : eq.symm (add_zero_left (x * 0))
  ... = (-(x * 0) + (x * 0)) + (x * 0) : by rw (add_neg_left (x * 0))
  ... = -(x * 0) + ((x * 0) + (x * 0)) : eq.symm (add_assoc (-(x * 0)) (x * 0) (x * 0))
  ... = -(x * 0) + (x * (0 + 0))       : by rw (dist_left x 0 0)
  ... = -(x * 0) + (x * 0)             : by rw (add_zero_left (0 : F))
  ... = 0                              : add_neg_left (x * 0)


end hidden

