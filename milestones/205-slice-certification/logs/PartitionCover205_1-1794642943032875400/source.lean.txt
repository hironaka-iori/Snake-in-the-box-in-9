import FiniteDomain205
namespace PartitionCover205_1
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
def r0 : Array Nat := #[1]
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0])
    (c0 : edge r0 (a 0) (a 1)=true)
    : (a 0=0 ∧ a 1=0) := by
  exact And.intro (forced (a 0) 0 start0) (forced (a 1) 0 start1)
#print axioms cover
end PartitionCover205_1
