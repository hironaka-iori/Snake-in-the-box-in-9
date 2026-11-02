import ReferenceInterface

namespace Snake9.Reference85
open Snake9.LocalWindow
set_option maxHeartbeats 2000000

abbrev Pick := Bool × Nat
def pickList (p : Pick) : List Key := if p.1 then dirKeysR4 else dirKeys6K235
def pickValid (p : Pick) : Bool := decide (p.2 < (pickList p).length)
def pickKey (p : Pick) : Key := (pickList p).getD p.2 ([],[])

theorem pick_mem (p : Pick) (h : pickValid p = true) : pickKey p ∈ pickList p := by
  have hi : p.2 < (pickList p).length := of_decide_eq_true h
  unfold pickKey
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  exact List.getElem_mem _

theorem pick_covered (p : Pick) (h : pickValid p = true) : keyCovered (pickKey p) = true := by
  apply List.contains_iff.mpr
  have hm := pick_mem p h
  cases he : p.1
  · apply List.mem_append_left
    simpa only [pickList,he,Bool.false_eq_true,↓reduceIte] using hm
  · apply List.mem_append_right
    simpa only [pickList,he,↓reduceIte] using hm

theorem picks_covered (ps : List Pick) (h : ps.all pickValid = true) :
    (ps.map pickKey).all keyCovered = true := by
  apply List.all_eq_true.mpr
  intro k hk
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hk
  exact pick_covered p (List.all_eq_true.mp h p hp)

#print axioms pick_mem
#print axioms pick_covered
#print axioms picks_covered
end Snake9.Reference85
