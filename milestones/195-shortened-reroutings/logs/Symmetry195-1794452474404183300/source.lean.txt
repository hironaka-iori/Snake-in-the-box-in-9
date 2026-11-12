import Std
namespace Symmetry195

def partner (x : Nat) : Nat :=
  Nat.xor (Nat.xor x (if x / 4 % 2 == x / 32 % 2 then 0 else 36)) 73

def Adj (x y : Nat) : Prop :=
  let d := Nat.xor x y
  d=1 ∨ d=2 ∨ d=4 ∨ d=8 ∨ d=16 ∨ d=32 ∨ d=64 ∨ d=128

instance (x y : Nat) : Decidable (Adj x y) := inferInstanceAs (Decidable (_ ∨ _))

set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem involution : ∀ v : Fin 256, partner (partner v.val)=v.val := by
  decide +kernel

theorem closed : ∀ v : Fin 256, partner v.val<256 := by
  decide +kernel

theorem noFixed : ∀ v : Fin 256, v.val≠partner v.val := by
  decide +kernel

theorem noFibreEdge : ∀ v : Fin 256, ¬ Adj v.val (partner v.val) := by
  decide +kernel

#print axioms involution
#print axioms closed
#print axioms noFixed
#print axioms noFibreEdge
end Symmetry195
