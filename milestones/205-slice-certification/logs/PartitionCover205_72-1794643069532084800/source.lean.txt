import FiniteDomain205
namespace PartitionCover205_72
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
def r0 : Array Nat := #[3]
def r1 : Array Nat := #[1]
def r2 : Array Nat := #[1]
def r3 : Array Nat := #[1,2]
def r4 : Array Nat := #[1,2]
def r5 : Array Nat := #[1]
def r6 : Array Nat := #[1]
def r7 : Array Nat := #[1,2]
def r8 : Array Nat := #[1]
def r9 : Array Nat := #[1]
def r10 : Array Nat := #[1,2]
def r11 : Array Nat := #[3]
theorem chunk0 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,1])
    (d2 : a 2 ∈ [0])
    (d7 : a 7 ∈ [0,1])
    (d5 : a 5 ∈ [0,1])
    (d4 : a 4 ∈ [0])
    (d1 : a 1 ∈ [0,1])
    (c3 : edge r3 (a 1) (a 3)=true)
    (c5 : edge r5 (a 2) (a 3)=true)
    (c7 : edge r7 (a 3) (a 7)=true)
    (c8 : edge r8 (a 4) (a 5)=true)
    : a 3 ∈ [0] ∧ a 7 ∈ [0] ∧ a 5 ∈ [0] ∧ a 1 ∈ [0] := by
  have b0 : a 3 ≠ 1 := exclude [0] (fun u v => edge r5 v u) (a 3) (a 2) 1 d2 c5 (by decide +kernel)
  have t0 : a 3 ∈ [0] := remove (a 3) 1 [0,1] d3 b0
  have b1 : a 7 ≠ 1 := exclude [0] (fun u v => edge r7 v u) (a 7) (a 3) 1 t0 c7 (by decide +kernel)
  have t1 : a 7 ∈ [0] := remove (a 7) 1 [0,1] d7 b1
  have b2 : a 5 ≠ 1 := exclude [0] (fun u v => edge r8 v u) (a 5) (a 4) 1 d4 c8 (by decide +kernel)
  have t2 : a 5 ∈ [0] := remove (a 5) 1 [0,1] d5 b2
  have b3 : a 1 ≠ 1 := exclude [0] (edge r3) (a 1) (a 3) 1 t0 c3 (by decide +kernel)
  have t3 : a 1 ∈ [0] := remove (a 1) 1 [0,1] d1 b3
  exact And.intro t0 (And.intro t1 (And.intro t2 (t3)))
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0,1])
    (start2 : a 2 ∈ [0])
    (start3 : a 3 ∈ [0,1])
    (start4 : a 4 ∈ [0])
    (start5 : a 5 ∈ [0,1])
    (start6 : a 6 ∈ [0])
    (start7 : a 7 ∈ [0,1])
    (c0 : edge r0 (a 0) (a 1)=true)
    (c1 : edge r1 (a 0) (a 2)=true)
    (c2 : edge r2 (a 0) (a 4)=true)
    (c3 : edge r3 (a 1) (a 3)=true)
    (c4 : edge r4 (a 1) (a 5)=true)
    (c5 : edge r5 (a 2) (a 3)=true)
    (c6 : edge r6 (a 2) (a 6)=true)
    (c7 : edge r7 (a 3) (a 7)=true)
    (c8 : edge r8 (a 4) (a 5)=true)
    (c9 : edge r9 (a 4) (a 6)=true)
    (c10 : edge r10 (a 5) (a 7)=true)
    (c11 : edge r11 (a 6) (a 7)=true)
    : (a 0=0 ∧ a 1=0 ∧ a 2=0 ∧ a 3=0 ∧ a 4=0 ∧ a 5=0 ∧ a 6=0 ∧ a 7=0) := by
  have group1 := chunk0 a start3 start2 start7 start5 start4 start1 c3 c5 c7 c8
  rcases group1 with ⟨h2,h3,h4,h5⟩
  exact And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 h5) (And.intro (forced (a 2) 0 start2) (And.intro (forced (a 3) 0 h2) (And.intro (forced (a 4) 0 start4) (And.intro (forced (a 5) 0 h4) (And.intro (forced (a 6) 0 start6) (forced (a 7) 0 h3)))))))
#print axioms cover
end PartitionCover205_72
