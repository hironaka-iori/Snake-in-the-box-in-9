import CycleCut196
namespace Cliques198
open LayerJoining

def bit (x k : Nat) : Nat := x / 2^k % 2

def matching (x : Nat) : Nat :=
  let a := Nat.xor x (if bit x 1 == bit x 4 then 0 else 18)
  let b := Nat.xor a (if bit a 3 == bit a 6 then 0 else 72)
  Nat.xor b 126

def Adj (x y : Nat) : Prop :=
  let d := Nat.xor x y
  d=1 ∨ d=2 ∨ d=4 ∨ d=8 ∨ d=16 ∨ d=32 ∨ d=64 ∨ matching x=y
instance (x y : Nat) : Decidable (Adj x y) := inferInstanceAs (Decidable (_ ∨ _))

def triangles : Array (Array Nat) := #[#[10, 14, 42], #[10, 14, 46], #[10, 42, 46], #[11, 15, 43], #[11, 15, 47], #[11, 43, 47], #[14, 42, 46], #[15, 43, 47], #[24, 28, 56], #[24, 28, 60], #[24, 56, 60], #[25, 29, 57], #[25, 29, 61], #[25, 57, 61], #[28, 56, 60], #[29, 57, 61], #[66, 70, 98], #[66, 70, 102], #[66, 98, 102], #[67, 71, 99], #[67, 71, 103], #[67, 99, 103], #[70, 98, 102], #[71, 99, 103], #[80, 84, 112], #[80, 84, 116], #[80, 112, 116], #[81, 85, 113], #[81, 85, 117], #[81, 113, 117], #[84, 112, 116], #[85, 113, 117]]
def triangle (c : Fin 32) (i : Fin 3) : Nat := triangles[c.val]![i.val]!
def prev (i : Fin 3) : Fin 3 := ⟨(i.val+2)%3, by omega⟩
def next (i : Fin 3) : Fin 3 := ⟨(i.val+1)%3, by omega⟩
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem distinctNeighbours : ∀ c : Fin 32, ∀ i : Fin 3,
  triangle c (prev i) ≠ triangle c i ∧ triangle c (next i) ≠ triangle c i ∧
  triangle c (prev i) ≠ triangle c (next i) := by decide +kernel

theorem triangleEdges : ∀ c : Fin 32, ∀ i : Fin 3,
  Adj (triangle c (prev i)) (triangle c i) ∧ Adj (triangle c (next i)) (triangle c i) := by decide +kernel

theorem excluded {m : Nat} (p : InducedPath Nat Adj m) (c : Fin 32) :
  ¬ (∀ i : Fin 3, ∃ j, p.vertex j=triangle c i) :=
  CycleCut196.noContainedDegreeTwo p (triangle c) prev next (distinctNeighbours c) (triangleEdges c)

def bval (b : Bool) : Nat := if b then 1 else 0

theorem fourFlags : ∀ a b c d : Bool,
  ¬ (a=true ∧ b=true ∧ c=true) →
  ¬ (a=true ∧ b=true ∧ d=true) →
  ¬ (a=true ∧ c=true ∧ d=true) →
  ¬ (b=true ∧ c=true ∧ d=true) →
  bval a+bval b+bval c+bval d ≤ 2 := by decide +kernel

#print axioms distinctNeighbours
#print axioms triangleEdges
#print axioms excluded
#print axioms fourFlags
end Cliques198
