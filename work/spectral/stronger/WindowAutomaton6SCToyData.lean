/-
Toy instance of the share-weighted six-centre automaton with context shares (milestone 35,
`milestones/35-231-lean/DESIGN.md`, "Toy chain").  Written by hand.

* k6 and H8: no keys (zero exclusion rows, empty H8 tree); zero potential, lambda = 120/1.
* 5-window share table: zero (no share keys, no floors needed).
* ctx 7 table: one field, 16, at the canonical 7-direction shape `0123412` with the counts
  `(2, 3, 6, 6, 6, 4)`; backed by the ctx 7 key `(0123412, 236664, cap 15)`, whose certificate is
  `LocalWindowCtxCnf.C70123412A236664K15` + `LocalWindowCtxUnsat.C70123412A236664K15` (a record of
  `milestones/28-combined-identities/data/ctxshare_r23*.jsonl.gz` with T = 16).
* ctx 8 table: one field, 16, at the canonical 8-direction shape `01234032` with the counts
  `(5, 4, 4, 6, 4, 3)` of the centres 2..7 (the first centre free); backed by the ctx 8 key
  `(01234032, 544643, cap 15)` (`C801234032A544643K15`; the solver record has T = 32, the toy
  certifies the weaker T = 16).
-/
import WindowAutomaton6SCDefs

set_option maxHeartbeats 0

namespace Snake9.WindowAutomaton

def tables6SCToyk6 : Tables6 where
  wIdx := fun _ => 0
  forb := fun _ _ => 0
  pIdx := fun _ => 0
  pot := fun _ _ => 0
  bits := 1
  num := 120
  den := 1

def tables6SCToyS : Tables6S where
  k6 := tables6SCToyk6
  htree := .nil
  sIdx := fun _ => 0
  shr := fun _ _ => 0
  sbits := 1

/-- 7-direction shape code ↦ ctx 7 row (row 1: `0123412`, row 0: zero). -/
def c7Idx6SCToy (c : Nat) : Nat := bif Nat.beq c (shapeCode [0, 1, 2, 3, 4, 1, 2]) then 1 else 0

def c7Rows6SCToy (r t0 : Nat) : Nat :=
  bif Nat.beq r 1 && Nat.beq t0 2 then Nat.shiftLeft 16 (8 * cntIdx6 [3, 6, 6, 6, 4] 0) else 0

/-- 8-direction shape code ↦ ctx 8 row (row 1: `01234032`, row 0: zero). -/
def c8Idx6SCToy (c : Nat) : Nat := bif Nat.beq c (shapeCode [0, 1, 2, 3, 4, 0, 3, 2]) then 1 else 0

def c8Rows6SCToy (r t0 : Nat) : Nat :=
  bif Nat.beq r 1 && Nat.beq t0 5 then Nat.shiftLeft 16 (8 * cntIdx6 [4, 4, 6, 4, 3] 0) else 0

def tables6SCToy : Tables6SC where
  s := tables6SCToyS
  c7Idx := c7Idx6SCToy
  c7 := c7Rows6SCToy
  c8Idx := c8Idx6SCToy
  c8 := c8Rows6SCToy
  cbits := 8

/-- The ctx 7 keys `(dirs, counts, cap)`, in chunks (one per listed shape). -/
def ctx7Chunks6SCToy : List (List (List Nat × List Nat × Nat)) :=
  [[([0, 1, 2, 3, 4, 1, 2], [2, 3, 6, 6, 6, 4], 15)]]

def ctx8Chunks6SCToy : List (List (List Nat × List Nat × Nat)) :=
  [[([0, 1, 2, 3, 4, 0, 3, 2], [5, 4, 4, 6, 4, 3], 15)]]

def ctx7Keys6SCToy : List (List Nat × List Nat × Nat) := ctx7Chunks6SCToy.flatten
def ctx8Keys6SCToy : List (List Nat × List Nat × Nat) := ctx8Chunks6SCToy.flatten

def ctx7Shapes6SCToy : List (List Nat) := [[0, 1, 2, 3, 4, 1, 2]]
def ctx8Shapes6SCToy : List (List Nat) := [[0, 1, 2, 3, 4, 0, 3, 2]]

end Snake9.WindowAutomaton
