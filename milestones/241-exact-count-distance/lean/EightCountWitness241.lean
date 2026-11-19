import Std

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace EightCountWitness241

-- Vertex numbers use the low four coordinates, two pairs, then the top bit.
def pairSign (pairBits : Nat) : Int :=
  if pairBits = 0 then 1 else if pairBits = 3 then -1 else 0

def selectionDifference (x : Nat) : Int :=
  let middle := pairSign ((x / 16) % 4) * pairSign ((x / 64) % 4)
  if middle = 0 then 0 else
    let low := x % 16
    if x < 256 then
      if low = 1 ∨ low = 2 ∨ low = 4 ∨ low = 8 then middle
      else if low = 7 ∨ low = 11 ∨ low = 13 ∨ low = 14 then -middle
      else 0
    else if low = 0 then -middle else if low = 15 then middle else 0

def neighbourSum (x : Nat) : Int :=
  ((List.range 9).map fun i => selectionDifference (Nat.xor x (2 ^ i))).sum

def changedPositions : List Nat := [0, 15, 48, 63, 192, 207, 240, 255]

def expectedCount (x : Nat) : Int :=
  if x = 0 ∨ x = 63 ∨ x = 207 ∨ x = 240 then 3
  else if x = 15 ∨ x = 48 ∨ x = 192 ∨ x = 255 then -3 else 0

abbrev ExactAt (x : Nat) : Prop :=
  (selectionDifference x = -1 ∨ selectionDifference x = 0 ∨ selectionDifference x = 1) ∧
  neighbourSum x = expectedCount x ∧ (expectedCount x ≠ 0 ↔ x ∈ changedPositions)

-- Each sixteen-vertex block is reduced separately by the Lean kernel.
private abbrev Block (b : Nat) := ∀ r : Fin 16, ExactAt (16 * b + r.val)

private theorem block0 : Block 0 := by decide +kernel
private theorem block1 : Block 1 := by decide +kernel
private theorem block2 : Block 2 := by decide +kernel
private theorem block3 : Block 3 := by decide +kernel
private theorem block4 : Block 4 := by decide +kernel
private theorem block5 : Block 5 := by decide +kernel
private theorem block6 : Block 6 := by decide +kernel
private theorem block7 : Block 7 := by decide +kernel
private theorem block8 : Block 8 := by decide +kernel
private theorem block9 : Block 9 := by decide +kernel
private theorem block10 : Block 10 := by decide +kernel
private theorem block11 : Block 11 := by decide +kernel
private theorem block12 : Block 12 := by decide +kernel
private theorem block13 : Block 13 := by decide +kernel
private theorem block14 : Block 14 := by decide +kernel
private theorem block15 : Block 15 := by decide +kernel
private theorem block16 : Block 16 := by decide +kernel
private theorem block17 : Block 17 := by decide +kernel
private theorem block18 : Block 18 := by decide +kernel
private theorem block19 : Block 19 := by decide +kernel
private theorem block20 : Block 20 := by decide +kernel
private theorem block21 : Block 21 := by decide +kernel
private theorem block22 : Block 22 := by decide +kernel
private theorem block23 : Block 23 := by decide +kernel
private theorem block24 : Block 24 := by decide +kernel
private theorem block25 : Block 25 := by decide +kernel
private theorem block26 : Block 26 := by decide +kernel
private theorem block27 : Block 27 := by decide +kernel
private theorem block28 : Block 28 := by decide +kernel
private theorem block29 : Block 29 := by decide +kernel
private theorem block30 : Block 30 := by decide +kernel
private theorem block31 : Block 31 := by decide +kernel

private theorem blocks : (b : Nat) → b < 32 → Block b
  | 0, _ => block0
  | 1, _ => block1
  | 2, _ => block2
  | 3, _ => block3
  | 4, _ => block4
  | 5, _ => block5
  | 6, _ => block6
  | 7, _ => block7
  | 8, _ => block8
  | 9, _ => block9
  | 10, _ => block10
  | 11, _ => block11
  | 12, _ => block12
  | 13, _ => block13
  | 14, _ => block14
  | 15, _ => block15
  | 16, _ => block16
  | 17, _ => block17
  | 18, _ => block18
  | 19, _ => block19
  | 20, _ => block20
  | 21, _ => block21
  | 22, _ => block22
  | 23, _ => block23
  | 24, _ => block24
  | 25, _ => block25
  | 26, _ => block26
  | 27, _ => block27
  | 28, _ => block28
  | 29, _ => block29
  | 30, _ => block30
  | 31, _ => block31
  | n + 32, h => by omega

theorem actual_cube_witness (x : Fin 512) : ExactAt x.val := by
  have bound := x.isLt
  have b : x.val / 16 < 32 := by omega
  have r : x.val % 16 < 16 := by omega
  have h := blocks (x.val / 16) b ⟨x.val % 16, r⟩
  change ExactAt (16 * (x.val / 16) + x.val % 16) at h
  have e : 16 * (x.val / 16) + x.val % 16 = x.val := by omega
  rwa [e] at h

theorem eight_distinct_positions :
    changedPositions.Nodup ∧ changedPositions.length = 8 ∧
    (∀ p ∈ changedPositions, p < 512) := by
  decide

theorem positive_vertex : selectionDifference 1 = 1 := by decide

#print axioms actual_cube_witness
#print axioms eight_distinct_positions
#print axioms positive_vertex

end EightCountWitness241
