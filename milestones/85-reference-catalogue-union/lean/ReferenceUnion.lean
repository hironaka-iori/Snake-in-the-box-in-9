import ReferenceChunk00
import ReferenceChunk01
import ReferenceChunk02
import ReferenceChunk03
import ReferenceChunk04
import ReferenceChunk05
import ReferenceChunk06
import ReferenceChunk07
import ReferenceChunk08
import ReferenceChunk09
import ReferenceChunk10
import ReferenceChunk11
import ReferenceChunk12
import ReferenceChunk13
import ReferenceChunk14
import ReferenceChunk15
import ReferenceChunk16
import ReferenceChunk17
import ReferenceChunk18
import ReferenceChunk19
import ReferenceChunk20
import ReferenceChunk21

namespace Snake9.Reference85
open Snake9.LocalWindow
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def referenceKeys : List Key := keys00 ++ keys01 ++ keys02 ++ keys03 ++ keys04 ++ keys05 ++ keys06 ++ keys07 ++ keys08 ++ keys09 ++ keys10 ++ keys11 ++ keys12 ++ keys13 ++ keys14 ++ keys15 ++ keys16 ++ keys17 ++ keys18 ++ keys19 ++ keys20 ++ keys21

theorem referenceKeys_valid : referenceKeys.all keyValid = true := by
  simp only [referenceKeys,List.all_append,keys00_valid,keys01_valid,keys02_valid,keys03_valid,keys04_valid,keys05_valid,keys06_valid,keys07_valid,keys08_valid,keys09_valid,keys10_valid,keys11_valid,keys12_valid,keys13_valid,keys14_valid,keys15_valid,keys16_valid,keys17_valid,keys18_valid,keys19_valid,keys20_valid,keys21_valid,Bool.true_and]

theorem referenceKeys_covered : referenceKeys.all keyCovered = true := by
  simp only [referenceKeys,List.all_append,keys00_covered,keys01_covered,keys02_covered,keys03_covered,keys04_covered,keys05_covered,keys06_covered,keys07_covered,keys08_covered,keys09_covered,keys10_covered,keys11_covered,keys12_covered,keys13_covered,keys14_covered,keys15_covered,keys16_covered,keys17_covered,keys18_covered,keys19_covered,keys20_covered,keys21_covered,Bool.true_and]

theorem referenceKeys_length : referenceKeys.length = 1378 := by decide +kernel

theorem reference_union_refuted (h235 : AllRefuted6K235) (h236 : AllRefuted236) :
    AllRefutedList referenceKeys := allRefuted_of_covered h235 h236 _ referenceKeys_covered

theorem concrete_reference_retained (h235 : AllRefuted6K235) (h236 : AllRefuted236)
    {m : Nat} (p : Snake m) (r : Nat) (hr : r+9 ≤ m)
    (k : Key) (hk : k ∈ referenceKeys) (s : Nat) (hs : s+k.2.length ≤ 6) :
    ¬ forwardHit p r s k ∧ ¬ reverseHit p r s k :=
  all_reference_guards_retained h235 h236 referenceKeys referenceKeys_valid referenceKeys_covered p r hr k hk s hs

#print axioms referenceKeys_valid
#print axioms referenceKeys_covered
#print axioms referenceKeys_length
#print axioms reference_union_refuted
#print axioms concrete_reference_retained
end Snake9.Reference85
