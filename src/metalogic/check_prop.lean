import .prop

open formula

/-
Proof schemes.
Proof schemes are semantically valid formula schemes.
-/
inductive proof : Type
| mk (p : formula) : is_tauto p → proof

meta def proof.repr : proof → string
| (proof.mk p _) := sformat!"⊢ {p.repr}"
meta instance : has_repr proof := ⟨proof.repr⟩


def local_context_t := (list formula) × (list proof)

meta def local_context_t.repr : local_context_t → string
| (fs, ps) := sformat!"({fs.repr} {ps.repr})"
meta instance : has_repr local_context_t := ⟨local_context_t.repr⟩

/-
append_local_formula loc_ctx f = Appends the formula scheme f to the end of the list of
syntactically checked formula schemes in the local context loc_ctx.
-/
def append_local_formula :
  local_context_t → formula → local_context_t
| (fs, ps) f := (fs ++ [f], ps)

/-
get_local_formula loc_ctx idx = Gets the formula scheme at index idx in the list of
syntactically checked formula schemes in the local context loc_ctx.
-/
def get_local_formula : local_context_t → ℕ → option formula
| (fs, _) idx := list.nth fs idx

/-
append_local_proof loc_ctx p = Appends the proof scheme p to the end of the list of
proof schemes in the local context loc_ctx.
-/
def append_local_proof :
  local_context_t → proof → local_context_t
| (fs, ps) p := (fs, ps ++ [p])

/-
get_local_proof loc_ctx idx = Gets the proof scheme at index idx in the list of
proof schemes in the local context loc_ctx.
-/
def get_local_proof : local_context_t → ℕ → option proof
| (_, ps) idx := list.nth ps idx


def global_context_t := list proof

meta def global_context_t.repr : global_context_t → string
| (ps : list proof) := sformat!"({ps.repr})"
meta instance : has_repr global_context_t := ⟨global_context_t.repr⟩

/-
append_global_proof glb_ctx p = Appends the proof scheme p to the end of the list of
proof schemes in the local context glb_ctx.
-/
def append_global_proof :
  global_context_t → proof → global_context_t
| ps p := list.append ps [p]

/-
get_global_proof glb_ctx idx = Gets the proof scheme at index idx in the list of
proof schemes in the global context glb_ctx.
-/
def get_global_proof : global_context_t → ℕ → option proof
| ps idx := list.nth ps idx


def dguard (p : Prop) [decidable p] : option (plift p) :=
if h : p then pure (plift.up h) else failure

/-
to_fun = Takes a list of string formula pairs and returns a function
from strings to formulas. For each pair in the list the function maps
the string in the pair to the formula in the pair. The function maps
each string not in a pair to an atomic proposition of the same name as
the string.
-/
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

def check_step : global_context_t → local_context_t → step → option local_context_t

-- Syntax

/-
bottom is a syntactically valid formula scheme.
-/
| _ loc_ctx is_bottom := do return (append_local_formula loc_ctx bottom)

/-
top is a syntactically valid formula scheme.
-/
| _ loc_ctx is_top := do return (append_local_formula loc_ctx top)

/-
(atom x) is a syntactically valid formula scheme for any name x.
-/
| _ loc_ctx (is_atom x) := do return (append_local_formula loc_ctx (atom x))

/-
If p is a syntactically valid formula scheme then ¬ p is a
syntactically valid formula scheme.
-/
| _ loc_ctx (is_not p_idx) := do
  p <- get_local_formula loc_ctx p_idx,
  return (append_local_formula loc_ctx (not p))

/-
If p and q are syntactically valid formula schemes then p ∧ q is a
syntactically valid formula scheme.
-/
| _ loc_ctx (is_and p_idx q_idx) := do
  p <- get_local_formula loc_ctx p_idx,
  q <- get_local_formula loc_ctx q_idx,
  return (append_local_formula loc_ctx (and p q))

/-
If p and q are syntactically valid formula schemes then p ∨ q is a
syntactically valid formula scheme.
-/
| _ loc_ctx (is_or p_idx q_idx) := do
  p <- get_local_formula loc_ctx p_idx,
  q <- get_local_formula loc_ctx q_idx,
  return (append_local_formula loc_ctx (or p q))

/-
If p and q are syntactically valid formula schemes then p → q is a
syntactically valid formula scheme.
-/
| _ loc_ctx (is_imp p_idx q_idx) := do
  p <- get_local_formula loc_ctx p_idx,
  q <- get_local_formula loc_ctx q_idx,
  return (append_local_formula loc_ctx (imp p q))

/-
If p and q are syntactically valid formula schemes then p ↔ q is a
syntactically valid formula scheme.
-/
| _ loc_ctx (is_iff p_idx q_idx) := do
  p <- get_local_formula loc_ctx p_idx,
  q <- get_local_formula loc_ctx q_idx,
  return (append_local_formula loc_ctx (iff p q))

-- Semantics

-- modus ponens
-- |- p & |- (p -> q) => |- q
/-
If p and q are syntactically valid formula schemes and p and p -> q are
semantically valid formula schemes then q is a semantically valid formula
scheme.
-/
| _ loc_ctx (mp p_idx q_idx h1_idx h2_idx) := do
  p <- get_local_formula loc_ctx p_idx,
  q <- get_local_formula loc_ctx q_idx,
  (proof.mk a ha) <- get_local_proof loc_ctx h1_idx,
  (proof.mk (imp b c) hbc) <- get_local_proof loc_ctx h2_idx | none,
  (plift.up hap) <- dguard (a = p),
  (plift.up hbp) <- dguard (b = p),
  (plift.up hcq) <- dguard (c = q),
  let t1 : is_tauto q :=
  begin
    have s1 : is_tauto p, rewrite <- hap, exact ha,
    have s2 : is_tauto (imp p q), rewrite <- hbp, rewrite <- hcq, exact hbc,
    exact is_tauto_mp p q s1 s2,
  end,
  return (append_local_proof loc_ctx (proof.mk q t1))

-- |- (p -> (q -> p))
/-
If p and q are syntactically valid formula schemes then (p -> (q -> p)) 
is a semantically valid formula scheme.
-/
| _ loc_ctx (prop_1 p_idx q_idx) := do
  p <- get_local_formula loc_ctx p_idx,
  q <- get_local_formula loc_ctx q_idx,
  let f := (p.imp (q.imp p)),
  let t1 : is_tauto f := is_tauto_prop_1 p q,
  return (append_local_proof loc_ctx (proof.mk f t1))

-- |- ((p -> (q -> r)) -> ((p -> q) -> (p -> r)))
/-
If p and q and r are syntactically valid formula schemes then
((p -> (q -> r)) -> ((p -> q) -> (p -> r))) is a semantically valid formula
scheme.
-/
| _ loc_ctx (prop_2 p_idx q_idx r_idx) := do
  p <- get_local_formula loc_ctx p_idx,
  q <- get_local_formula loc_ctx q_idx,
  r <- get_local_formula loc_ctx r_idx,
  let f := ((p.imp (q.imp r)).imp ((p.imp q).imp (p.imp r))),
  let t1 : is_tauto f := is_tauto_prop_2 p q r,
  return (append_local_proof loc_ctx (proof.mk f t1))

-- |- ((~p -> ~q) -> (q -> p))
/-
If p and q are syntactically valid formula schemes then
((~p -> ~q) -> (q -> p)) is a semantically valid formula scheme.
-/
| _ loc_ctx (prop_3 p_idx q_idx) := do
  p <- get_local_formula loc_ctx p_idx,
  q <- get_local_formula loc_ctx q_idx,
  let f := (((not p).imp (not q)).imp (q.imp p)),
  let t1 : is_tauto f := is_tauto_prop_3 p q,
  return (append_local_proof loc_ctx (proof.mk f t1))

/-
If p is a semantically valid formula scheme in the global context then
any consistent substitution of formula schemes for the atomic propositions
in p is a semantically valid formula scheme.
-/
| glb_ctx loc_ctx (apply_proof idx m) := do
  (proof.mk p h1) <- get_global_proof glb_ctx idx,
  let split := list.unzip m,
  let split_fst := prod.fst split,
  let split_snd := prod.snd split,
  split_snd' <- list.mmap (get_local_formula loc_ctx) split_snd,
  let join := list.zip split_fst split_snd',
  let m := to_fun join,
  let f := sub m p,
  let t1 : is_tauto f := thm_2_4_gen p h1 m,
  return (append_local_proof loc_ctx (proof.mk f t1))


def check_all :
global_context_t → local_context_t → list step → option global_context_t
| glb_ctx loc_ctx [] := do
  let prf_list := prod.snd loc_ctx,
  prf <- list.last' prf_list,
  return (append_global_proof glb_ctx prf)
| glb_ctx loc_ctx (step :: steps) := do
  loc_ctx' <- check_step glb_ctx loc_ctx step,
  check_all glb_ctx loc_ctx' steps


-- example
def ex := do
  glb_ctx_1 <- (check_all [] ([], []) [
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
  glb_ctx_2 <- check_all glb_ctx_1 ([], []) [
    is_atom "Q",
    apply_proof 0 [("P", 0)]
  ],
  return glb_ctx_2

#eval ex
