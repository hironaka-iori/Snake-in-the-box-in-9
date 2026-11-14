import CyclicSymmetry204
namespace RotationObstruction204
open CyclicSymmetry204 Phase
def seed : Array Nat := #[0,1,3,7,15,13,12,28,30,62,46,38,36,52,116,124,108,109,111,103,119,55,183,167,175,173,172,188,184,56,40,41,43,59,187,155,153,137,136,138,202,194,192,193,209,211,243,227,235,233,249,253,245,229,228,230,238,254,250,122,106,98,96,97,113,49,177,161,160,162,178,50,18,82,80,88,72,73,75,91,95,223,207,205,204,220,212,214,150,134,132,133,149,21,85,69,68,70,78]
def rotate (x : Nat) : Nat :=
  (x &&& 230) + (if x.testBit 4 then 1 else 0) +
  (if x.testBit 0 then 8 else 0) + (if x.testBit 3 then 16 else 0)
def image (r : Phase) (x : Nat) : Nat := if x &&& 230 = 70 then rot rotate r x else x
def adjacent (x y : Nat) : Prop :=
  let d := Nat.xor x y
  d=1 ∨ d=2 ∨ d=4 ∨ d=8 ∨ d=16 ∨ d=32 ∨ d=64 ∨ d=128
instance (x y : Nat) : Decidable (adjacent x y) := inferInstanceAs (Decidable (_ ∨ _))
theorem chord_one : 73+1<98 ∧ ¬adjacent seed[73]! seed[98]! ∧
    adjacent (image one seed[73]!) (image one seed[98]!) := by decide +kernel
theorem chord_two : 3+1<98 ∧ ¬adjacent seed[3]! seed[98]! ∧
    adjacent (image two seed[3]!) (image two seed[98]!) := by decide +kernel
theorem everyNonzeroPhase (r : Phase) (nonzero : r ≠ zero) :
    ∃ i j : Fin 99, i.val+1<j.val ∧ ¬adjacent seed[i.val]! seed[j.val]! ∧
      adjacent (image r seed[i.val]!) (image r seed[j.val]!) := by
  cases r with
  | zero => exact False.elim (nonzero rfl)
  | one => exact ⟨⟨73,by decide⟩,⟨98,by decide⟩,chord_one⟩
  | two => exact ⟨⟨3,by decide⟩,⟨98,by decide⟩,chord_two⟩
#print axioms chord_one
#print axioms chord_two
#print axioms everyNonzeroPhase
end RotationObstruction204
