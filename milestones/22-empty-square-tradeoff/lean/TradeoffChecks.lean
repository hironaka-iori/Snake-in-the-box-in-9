import Snake9

/-! Small kernel-checked obstructions and counterexample. No new global upper bound.
The original Snake9.Snake definition is used without alteration. -/
namespace Snake9.EmptySquareTradeoff

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sharpValues : Array Nat :=
  #[5,7,6,14,10,11,9,25,17,19,18,50,34,35,33,97,65,67,66,194,130,131,129,385,257,259,258]

def sharpVertex (i : Fin 27) : Vertex := ⟨sharpValues[i.val]! % 512, by omega⟩

theorem sharp_distinct : ∀ i j : Fin 27, sharpVertex i = sharpVertex j → i = j := by decide

theorem sharp_induced : ∀ i j : Fin 27, i.val < j.val →
    (Adj (sharpVertex i) (sharpVertex j) ↔ i.val + 1 = j.val) := by decide

def sharpSnake : Snake 26 := ⟨sharpVertex, sharp_distinct, sharp_induced⟩

/-- The canonical coordinate square with axes zero and one. -/
def face : List Vertex := [⟨0,by omega⟩, ⟨1,by omega⟩, ⟨2,by omega⟩, ⟨3,by omega⟩]

def touchesFace (v : Vertex) : Bool := face.any (fun q => decide (Adj v q))

def touchCount {m : Nat} (p : Snake m) : Nat :=
  ((List.finRange (m+1)).filter (fun i => touchesFace (p.vertex i))).length

theorem sharp_face_empty : ∀ i : Fin 27, sharpSnake.vertex i ∉ face := by decide

theorem sharp_touch_count : touchCount sharpSnake = 21 := by decide

/-- In particular, the universal proposed multiplicity cap twenty is false. -/
theorem cap_twenty_false :
    ¬ (∀ m (p : Snake m), (∀ i, p.vertex i ∉ face) → touchCount p ≤ 20) := by
  intro h
  have hc := h 26 sharpSnake sharp_face_empty
  rw [sharp_touch_count] at hc
  omega

/-- Canonical nine-direction word 0,1,2,3,0,4,2,3,1.
Its endpoints 0 and 16 are adjacent; all proper eight-edge blocks are induced. -/
def badValues : Array Nat := #[0,1,3,7,15,14,30,26,18,16]
def badVertex (i : Fin 10) : Vertex := ⟨badValues[i.val]! % 512, by omega⟩

theorem bad_endpoints_adjacent : Adj (badVertex 0) (badVertex 9) := by decide

theorem no_bad_block {m : Nat} (p : Snake m) (s : Nat) (hs : s+9 ≤ m)
    (hblock : ∀ i : Fin 10, p.vertex ⟨s+i.val, by omega⟩ = badVertex i) : False := by
  have hi := p.induced ⟨s, by omega⟩ ⟨s+9, by omega⟩ (by simp)
  have h0 : p.vertex ⟨s, by omega⟩ = badVertex 0 := by simpa using hblock 0
  have h9 : p.vertex ⟨s+9, by omega⟩ = badVertex 9 := by simpa using hblock 9
  have ha : Adj (p.vertex ⟨s, by omega⟩) (p.vertex ⟨s+9, by omega⟩) := by
    rw [h0,h9]
    exact bad_endpoints_adjacent
  have hc := hi.mp ha
  change s + 1 = s + 9 at hc
  omega

#print axioms sharp_distinct
#print axioms sharp_induced
#print axioms sharp_face_empty
#print axioms sharp_touch_count
#print axioms cap_twenty_false
#print axioms no_bad_block
end Snake9.EmptySquareTradeoff
