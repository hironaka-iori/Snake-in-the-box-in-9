import PairChunk198_3_0
import PairChunk198_3_1
import PairChunk198_3_2
import PairChunk198_3_3
namespace PairRows198_3
open PairData198

theorem within (i : Fin 12) (j : Fin 48) :
 let a := 36+i.val
 (first[a]!<256 ∧ second[a]!<256) ∧
 (first[a]! = first[j.val]! ↔ a=j.val) ∧
 (second[a]! = second[j.val]! ↔ a=j.val) ∧
 (Adj first[a]! first[j.val]! ↔ a+1=j.val ∨ j.val+1=a) ∧
 (Adj second[a]! second[j.val]! ↔ a+1=j.val ∨ j.val+1=a) := by
 refine PairCover198.cover (P:=fun i => let a := 36+i.val; (first[a]!<256 ∧ second[a]!<256) ∧
 (first[a]! = first[j.val]! ↔ a=j.val) ∧
 (second[a]! = second[j.val]! ↔ a=j.val) ∧
 (Adj first[a]! first[j.val]! ↔ a+1=j.val ∨ j.val+1=a) ∧
 (Adj second[a]! second[j.val]! ↔ a+1=j.val ∨ j.val+1=a)) ?_ i
 intro b q
 rcases b with ⟨b,hb⟩
 have cases : b=0 ∨ b=1 ∨ b=2 ∨ b=3 := by omega
 rcases cases with rfl | rfl | rfl | rfl
 · exact PairChunk198_3_0.within q j
 · exact PairChunk198_3_1.within q j
 · exact PairChunk198_3_2.within q j
 · exact PairChunk198_3_3.within q j

theorem separated (i : Fin 12) (j : Fin 48) :
 let a := 36+i.val
 first[a]!≠second[j.val]! ∧ ¬ Adj first[a]! second[j.val]! := by
 refine PairCover198.cover (P:=fun i => let a := 36+i.val; first[a]!≠second[j.val]! ∧ ¬ Adj first[a]! second[j.val]!) ?_ i
 intro b q
 rcases b with ⟨b,hb⟩
 have cases : b=0 ∨ b=1 ∨ b=2 ∨ b=3 := by omega
 rcases cases with rfl | rfl | rfl | rfl
 · exact PairChunk198_3_0.separated q j
 · exact PairChunk198_3_1.separated q j
 · exact PairChunk198_3_2.separated q j
 · exact PairChunk198_3_3.separated q j

#print axioms within
#print axioms separated
end PairRows198_3
