import CubeLocal
import Mathlib.Tactic
namespace Snake9.ExpandedCells
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem edge_checks_sound (f : Vertex → Vertex)
    (h : ∀ v a, Adj (f v) (f (vxor v (unit a)))) {v w : Vertex}
    (ha : Adj v w) : Adj (f v) (f w) := by
  obtain ⟨k,hk,he⟩ := (adj_iff_coordinate_flip v w).mp ha
  have hw : w = vxor v (unit ⟨k,hk⟩) := Fin.ext he
  rw [hw]
  exact h v ⟨k,hk⟩

def permute (n : Nat) : Nat := (if n.testBit 1 then 1 else 0) + (if n.testBit 5 then 2 else 0) + (if n.testBit 4 then 4 else 0) + (if n.testBit 2 then 8 else 0) + (if n.testBit 7 then 16 else 0) + (if n.testBit 0 then 32 else 0) + (if n.testBit 3 then 64 else 0) + (if n.testBit 6 then 128 else 0) + (if n.testBit 8 then 256 else 0)
def inversePermute (n : Nat) : Nat := (if n.testBit 0 then 2 else 0) + (if n.testBit 1 then 32 else 0) + (if n.testBit 2 then 16 else 0) + (if n.testBit 3 then 4 else 0) + (if n.testBit 4 then 128 else 0) + (if n.testBit 5 then 1 else 0) + (if n.testBit 6 then 8 else 0) + (if n.testBit 7 then 64 else 0) + (if n.testBit 8 then 256 else 0)
def align (v : Vertex) : Vertex := ⟨(permute v.val ^^^ 7) % 512, Nat.mod_lt _ (by decide)⟩
def undo (v : Vertex) : Vertex := ⟨inversePermute (v.val ^^^ 7) % 512, Nat.mod_lt _ (by decide)⟩
def bitPerm (a : Coord) : Coord := ⟨(#[5,0,3,6,2,1,7,4,8])[a.val]! % 9, Nat.mod_lt _ (by decide)⟩
theorem undo_align : ∀ v, undo (align v) = v := by decide
#print axioms undo_align
theorem flip_rule : ∀ v a, align (vxor v (unit a)) = vxor (align v) (unit (bitPerm a)) := by decide
#print axioms flip_rule
theorem bitPerm_surjective : ∀ b, ∃ a, bitPerm a = b := by decide
theorem align_injective : Function.Injective align := by
  intro v w he
  have h := congrArg undo he
  simpa only [undo_align] using h
theorem align_adj (v w : Vertex) : Adj (align v) (align w) ↔ Adj v w := by
  constructor
  · intro h
    obtain ⟨k,hk,he⟩ := (adj_iff_coordinate_flip _ _).mp h
    obtain ⟨a,ha⟩ := bitPerm_surjective ⟨k,hk⟩
    have hw : align w = vxor (align v) (unit (bitPerm a)) := by
      rw [ha]
      exact Fin.ext he
    have hw' : w = vxor v (unit a) := align_injective (hw.trans (flip_rule v a).symm)
    rw [hw']
    exact (adj_iff_coordinate_flip _ _).mpr ⟨a.val,a.isLt,rfl⟩
  · apply edge_checks_sound align
    intro u a
    rw [flip_rule]
    exact (adj_iff_coordinate_flip _ _).mpr ⟨(bitPerm a).val,(bitPerm a).isLt,rfl⟩
def alignSnake {m : Nat} (p : Snake m) : Snake m where
  vertex i := align (p.vertex i)
  distinct i j h := p.distinct i j (align_injective h)
  induced i j hij := (align_adj _ _).trans (p.induced i j hij)
#print axioms edge_checks_sound
#print axioms bitPerm_surjective
#print axioms align_injective
#print axioms align_adj
#print axioms alignSnake
end Snake9.ExpandedCells
