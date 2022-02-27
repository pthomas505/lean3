import .prop

open formula

/-
Proof schemes.
Proof schemes are semantically valid formula schemes.
-/
inductive proof : Type
| mk : formula → proof

meta def proof.repr : proof → string
| (proof.mk p) := sformat!"⊢ {p.repr}"
meta instance : has_repr proof := ⟨proof.repr⟩


/-
appendFormula ctx f = Appends the formula scheme f to the end of the list of
syntactically checked formula schemes in the local context ctx.
-/
def append_formula :
  (list formula) × (list proof) → formula → (list formula) × (list proof)
| (fs, ps) f := (fs ++ [f], ps)

/-
getFormula ctx idx = Gets the formula scheme at index idx in the list of
syntactically checked formula schemes in the local context ctx.
-/
def get_formula : (list formula) × (list proof) → ℕ → option formula
| (fs, _) idx := list.nth fs idx

/-
appendProof ctx p = Appends the proof scheme p to the end of the list of
proof schemes in the local context ctx.
-/
def append_proof :
  (list formula) × (list proof) → proof → (list formula) × (list proof)
| (fs, ps) p := (fs, ps ++ [p])

/-
getProof ctx idx = Gets the proof scheme at index idx in the list of
proof schemes in the local context ctx.
-/
def get_proof : (list formula) × (list proof) → ℕ → option proof
| (_, ps) idx := list.nth ps idx


def to_fun : list (string × formula) → string → formula
| [] v := atom v
| ((u, f) :: fs) v := if u = v then f else to_fun fs v


inductive step : Type
| is_bottom : step
| is_top : step
| is_atom : string → step
| is_not : ℕ → step
| is_and : ℕ → ℕ → step
| is_or : ℕ → ℕ → step
| is_imp : ℕ → ℕ → step
| is_iff : ℕ → ℕ → step
| mp : ℕ → ℕ → ℕ → ℕ → step
| prop_1 : ℕ → ℕ → step
| prop_2 : ℕ → ℕ → ℕ → step
| prop_3 : ℕ → ℕ → step
| apply_proof : ℕ → list (string × ℕ) → step

open step

def check_step :
list proof →
prod (list formula) (list proof) →
step →
option (prod (list formula) (list proof))

-- Syntax

/-
bottom is a syntactically valid formula scheme.
-/
| glb loc is_bottom := do return (append_formula loc bottom)

/-
top is a syntactically valid formula scheme.
-/
| glb loc is_top := do return (append_formula loc top)

/-
(atom x) is a syntactically valid formula scheme for any name x.
-/
| glb loc (is_atom x) := do return (append_formula loc (atom x))

/-
If P is a syntactically valid formula scheme then ¬ P is a syntactically
valid formula scheme.
-/
| glb loc (is_not p_idx) := do
  p <- get_formula loc p_idx,
  return (append_formula loc (not p))

/-
If P and Q are syntactically valid formula schemes then P ∧ Q is a
syntactically valid formula scheme.
-/
| glb loc (is_and p_idx q_idx) := do
  p <- get_formula loc p_idx,
  q <- get_formula loc q_idx,
  return (append_formula loc (and p q))

/-
If P and Q are syntactically valid formula schemes then P ∨ Q is a
syntactically valid formula scheme.
-/
| glb loc (is_or p_idx q_idx) := do
  p <- get_formula loc p_idx,
  q <- get_formula loc q_idx,
  return (append_formula loc (or p q))

/-
If P and Q are syntactically valid formula schemes then P → Q is a
syntactically valid formula scheme.
-/
| glb loc (is_imp p_idx q_idx) := do
  p <- get_formula loc p_idx,
  q <- get_formula loc q_idx,
  return (append_formula loc (imp p q))

/-
If P and Q are syntactically valid formula schemes then P ↔ Q is a
syntactically valid formula scheme.
-/
| glb loc (is_iff p_idx q_idx) := do
  p <- get_formula loc p_idx,
  q <- get_formula loc q_idx,
  return (append_formula loc (iff p q))

-- Semantics

-- |- p & |- (p -> q) => |- q
/-
If p and q are syntactically valid formula schemes and p and p -> q are
semantically valid formula schemes then q is a semantically valid formula
scheme.
-/
| glb loc (mp p_idx q_idx h1_idx h2_idx) := do
  p <- get_formula loc p_idx,
  q <- get_formula loc q_idx,
  (proof.mk p') <- get_proof loc h1_idx,
  (proof.mk (imp p'' q')) <- get_proof loc h2_idx | none,
  guard (p' = p''), guard (p = p''), guard (q = q'),
  return (append_proof loc (proof.mk q))

-- |- (p -> (q -> p))
/-
If p and q are syntactically valid formula schemes then (p -> (q -> p)) 
is a semantically valid formula scheme.
-/
| glb loc (prop_1 p_idx q_idx) := do
  p <- get_formula loc p_idx,
  q <- get_formula loc q_idx,
  return (append_proof loc (proof.mk (p.imp (q.imp p))))

-- |- ((p -> (q -> r)) -> ((p -> q) -> (p -> r)))
/-
If p and q and r are syntactically valid formula schemes then
((p -> (q -> r)) -> ((p -> q) -> (p -> r))) is a semantically valid formula
scheme.
-/
| glb loc (prop_2 p_idx q_idx r_idx) := do
  p <- get_formula loc p_idx,
  q <- get_formula loc q_idx,
  r <- get_formula loc r_idx,
  return (append_proof loc (proof.mk ((p.imp (q.imp r)).imp ((p.imp q).imp (p.imp r)))))

-- |- ((~p -> ~q) -> (q -> p))
/-
If p and q are syntactically valid formula schemes then
((~p -> ~q) -> (q -> p)) is a semantically valid formula scheme.
-/
| glb loc (prop_3 p_idx q_idx) := do
  p <- get_formula loc p_idx,
  q <- get_formula loc q_idx,
  return (append_proof loc (proof.mk (((not p).imp (not q)).imp (q.imp p))))

| glb loc (apply_proof idx subst) := do
  (proof.mk prf) <- list.nth glb idx,
  let split := list.unzip subst,
  let split_fst := prod.fst split,
  let split_snd := prod.snd split,
  split_snd' <- list.mmap (get_formula loc) split_snd,
  let join := list.zip split_fst split_snd',
  let sub_fun := to_fun join,
  return (append_proof loc (proof.mk (sub sub_fun prf)))

def check_all :
list proof → prod (list formula) (list proof) → list step → option (list proof)
| glb loc [] := do
  let prf_list := prod.snd loc,
  prf <- list.last' prf_list,
  return (glb ++ [prf])
| glb loc (step :: steps) := do
  loc' <- check_step glb loc step,
  check_all glb loc' steps


-- example
def ex := do
  glb_1 <- (check_all [] ([], []) [
    is_atom "P",  -- f0 = p
    is_imp 0 0,   -- f1 = p -> p
    is_imp 1 0,   -- f2 = (p -> p) -> p
    is_imp 0 2,   -- f3 = p -> ((p -> p) -> p)
    is_imp 0 1,   -- f4 = p -> (p -> p)
    is_imp 4 1,   -- f5 = (p -> (p -> p)) -> (p -> p)
    is_imp 3 5,   -- f6 = (p -> ((p -> p) -> p)) -> ((p -> (p -> p)) -> (p -> p))
    prop_2 0 1 0, -- p0 = |- (p -> ((p -> p) -> p)) -> ((p -> (p -> p)) -> (p -> p))
    prop_1 0 1,   -- p1 = |- p -> ((p -> p) -> p)
    mp 3 5 1 0,   -- p2 = |- (p -> (p -> p)) -> (p -> p)
    prop_1 0 0,   -- p3 = |- p -> (p -> p)
    mp 4 1 3 2    -- p4 = |- p -> p
    ]),
  glb_2 <- check_all glb_1 ([], []) [
    is_atom "Q",
    apply_proof 0 [("P", 0)]
  ],
  return glb_2

#eval ex
