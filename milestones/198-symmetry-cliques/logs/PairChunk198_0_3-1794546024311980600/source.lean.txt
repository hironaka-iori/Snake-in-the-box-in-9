import PairCover198
namespace PairChunk198_0_3
open PairData198
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem within : ∀ i : Fin 3, ∀ j : Fin 48,
 let a := 0+(9+i.val)
 (first[a]!<256 ∧ second[a]!<256) ∧
 (first[a]! = first[j.val]! ↔ a=j.val) ∧
 (second[a]! = second[j.val]! ↔ a=j.val) ∧
 (Adj first[a]! first[j.val]! ↔ a+1=j.val ∨ j.val+1=a) ∧
 (Adj second[a]! second[j.val]! ↔ a+1=j.val ∨ j.val+1=a) := by decide +kernel

theorem separated : ∀ i : Fin 3, ∀ j : Fin 48,
 let a := 0+(9+i.val)
 first[a]!≠second[j.val]! ∧ ¬ Adj first[a]! second[j.val]! := by decide +kernel

#print axioms within
#print axioms separated
end PairChunk198_0_3
