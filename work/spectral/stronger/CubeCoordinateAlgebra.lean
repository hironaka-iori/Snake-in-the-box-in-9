import CubeLocal
import Mathlib.Tactic

namespace Snake9

def quad (a b c d : Coord) : Vertex := vxor (triple a b c) (unit d)

theorem vxor_comm (u v : Vertex) : vxor u v = vxor v u := by
  apply Fin.ext
  exact Nat.xor_comm _ _

theorem vxor_assoc (u v w : Vertex) : vxor (vxor u v) w = vxor u (vxor v w) := by
  apply Fin.ext
  exact Nat.xor_assoc _ _ _

@[simp] theorem vxor_zero (u : Vertex) : vxor u 0 = u := by
  apply Fin.ext
  exact Nat.xor_zero _

@[simp] theorem zero_vxor (u : Vertex) : vxor 0 u = u := by
  rw [vxor_comm, vxor_zero]

@[simp] theorem vxor_cancel_right (u v : Vertex) : vxor (vxor u v) v = u := by
  rw [vxor_assoc, vxor_self, vxor_zero]

@[simp] theorem bit_unit (a k : Coord) : (unit a).val.testBit k.val = decide (a=k) := by
  simp [unit, Nat.testBit_two_pow, Fin.val_inj]

@[simp] theorem bit_pair (a b k : Coord) :
    (pair a b).val.testBit k.val = (decide (a=k) ^^ decide (b=k)) := by
  change ((unit a).val ^^^ (unit b).val).testBit k.val = _
  rw [Nat.testBit_xor, bit_unit, bit_unit]

@[simp] theorem bit_triple (a b c k : Coord) :
    (triple a b c).val.testBit k.val =
      ((decide (a=k) ^^ decide (b=k)) ^^ decide (c=k)) := by
  change ((pair a b).val ^^^ (unit c).val).testBit k.val = _
  rw [Nat.testBit_xor, bit_pair, bit_unit]

@[simp] theorem bit_quad (a b c d k : Coord) :
    (quad a b c d).val.testBit k.val =
      (((decide (a=k) ^^ decide (b=k)) ^^ decide (c=k)) ^^ decide (d=k)) := by
  change ((triple a b c).val ^^^ (unit d).val).testBit k.val = _
  rw [Nat.testBit_xor, bit_triple, bit_unit]

theorem adj_flip (v : Vertex) (a : Coord) : Adj v (vxor v (unit a)) := by
  apply (adj_iff_coordinate_flip _ _).mpr
  exact ⟨a.val,a.isLt,rfl⟩

theorem neighbor_triple (a b c : Coord) {v : Vertex} (h : Adj (triple a b c) v) :
    ∃ d : Coord, v=quad a b c d := by
  obtain ⟨k,hk,he⟩ := (adj_iff_coordinate_flip _ _).mp h
  exact ⟨⟨k,hk⟩,Fin.ext he⟩

theorem triple_quad_adj (a b c d : Coord) : Adj (triple a b c) (quad a b c d) :=
  adj_flip _ _

theorem quad_swap_first (a b c d : Coord) : quad a b c d = quad b a c d := by
  apply Fin.ext
  dsimp [quad,triple,pair,vxor]
  ac_rfl

theorem quad_swap_middle (a b c d : Coord) : quad a b c d = quad a c b d := by
  apply Fin.ext
  dsimp [quad,triple,pair,vxor]
  ac_rfl

theorem quad_swap_last (a b c d : Coord) : quad a b c d = quad a b d c := by
  apply Fin.ext
  dsimp [quad,triple,pair,vxor]
  ac_rfl

theorem quad_rotate (a b c d : Coord) : quad a b c d = quad d a b c := by
  apply Fin.ext
  dsimp [quad,triple,pair,vxor]
  ac_rfl

@[simp] theorem quad_cancel_first (a b c : Coord) : quad a b c a = pair b c := by
  apply Fin.ext
  change (((unit a).val ^^^ (unit b).val) ^^^ (unit c).val) ^^^ (unit a).val = _
  calc
    _ = (((unit b).val ^^^ (unit c).val) ^^^ (unit a).val) ^^^ (unit a).val := by ac_rfl
    _ = (unit b).val ^^^ (unit c).val := by
      rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

@[simp] theorem quad_cancel_second (a b c : Coord) : quad a b c b = pair a c := by
  rw [quad_swap_first,quad_cancel_first]

@[simp] theorem quad_cancel_third (a b c : Coord) : quad a b c c = pair a b := by
  exact vxor_cancel_right _ _

#print axioms bit_quad
#print axioms neighbor_triple
#print axioms quad_cancel_first
end Snake9
