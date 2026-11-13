import Std
namespace NormalForm197

def bit (x k : Nat) : Nat := x / 2^k % 2

def swaps8 (x : Nat) : Nat :=
  let a := Nat.xor x (if bit x 0 == bit x 3 then 0 else 9)
  Nat.xor a (if bit a 2 == bit a 4 then 0 else 20)
def original (x : Nat) : Nat := Nat.xor (swaps8 x) 63
def normal (x : Nat) : Nat := Nat.xor (swaps8 x) 34

def matching (x : Nat) : Nat :=
  let a := Nat.xor x (if bit x 0 == bit x 2 then 0 else 5)
  let b := Nat.xor a (if bit a 1 == bit a 3 then 0 else 10)
  Nat.xor b 16

def embed (y : Nat) : Nat := y % 2 + 4 * (y / 2)
def project (x : Nat) : Nat := x % 2 + 2 * (x / 4)
def label (x : Nat) : Nat := project (if bit x 1 == 0 then x else normal x)
def Adj7 (x y : Nat) : Prop :=
  let d := Nat.xor x y
  d=1 ∨ d=2 ∨ d=4 ∨ d=8 ∨ d=16 ∨ d=32 ∨ d=64
instance (x y : Nat) : Decidable (Adj7 x y) := inferInstanceAs (Decidable (_ ∨ _))

set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem conjugacy : ∀ x : Fin 256,
  normal (Nat.xor x.val 5) = Nat.xor (original x.val) 5 := by decide +kernel

theorem orbitLabels : ∀ x : Fin 256,
  label x.val = label (normal x.val) ∧ label x.val < 128 ∧
  (embed (label x.val) = x.val ∨ embed (label x.val) = normal x.val) := by decide +kernel

theorem matchingInvolution : ∀ y : Fin 128,
  matching (matching y.val) = y.val ∧ matching y.val ≠ y.val ∧ matching y.val < 128 := by decide +kernel

theorem representativeLabel : ∀ y : Fin 128, label (embed y.val) = y.val := by decide +kernel

theorem doubleEdgeCriterion : ∀ y : Fin 128,
  Adj7 y.val (matching y.val) ↔
    bit y.val 0 = bit y.val 2 ∧ bit y.val 1 = bit y.val 3 := by decide +kernel

#print axioms conjugacy
#print axioms orbitLabels
#print axioms matchingInvolution
#print axioms representativeLabel
#print axioms doubleEdgeCriterion
end NormalForm197
