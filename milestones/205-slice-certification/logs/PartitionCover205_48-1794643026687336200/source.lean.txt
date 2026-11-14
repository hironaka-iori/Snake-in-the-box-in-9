import FiniteDomain205
namespace PartitionCover205_48
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
def r0 : Array Nat := #[1]
def r1 : Array Nat := #[1]
def r2 : Array Nat := #[1]
def r3 : Array Nat := #[1]
def r4 : Array Nat := #[15]
def r5 : Array Nat := #[1]
def r6 : Array Nat := #[15]
def r7 : Array Nat := #[1]
def r8 : Array Nat := #[1,2,4,8]
def r9 : Array Nat := #[1,0,0,0]
def r10 : Array Nat := #[1,2,4,8]
def r11 : Array Nat := #[1,0,0,0]
theorem chunk0 (a : Nat → Nat)
    (d4 : a 4 ∈ [0,1,2,3])
    (d0 : a 0 ∈ [0])
    (d7 : a 7 ∈ [0,1,2,3])
    (d3 : a 3 ∈ [0])
    (d5 : a 5 ∈ [0,1,2,3])
    (d6 : a 6 ∈ [0,1,2,3])
    (c2 : edge r2 (a 0) (a 4)=true)
    (c7 : edge r7 (a 3) (a 7)=true)
    (c8 : edge r8 (a 4) (a 5)=true)
    (c9 : edge r9 (a 4) (a 6)=true)
    : a 4 ∈ [0] ∧ a 7 ∈ [0] ∧ a 5 ∈ [0] ∧ a 6 ∈ [0] := by
  have b0 : a 4 ≠ 1 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 1 d0 c2 (by decide +kernel)
  have t0 : a 4 ∈ [0,2,3] := remove (a 4) 1 [0,1,2,3] d4 b0
  have b1 : a 4 ≠ 2 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 2 d0 c2 (by decide +kernel)
  have t1 : a 4 ∈ [0,3] := remove (a 4) 2 [0,2,3] t0 b1
  have b2 : a 4 ≠ 3 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 3 d0 c2 (by decide +kernel)
  have t2 : a 4 ∈ [0] := remove (a 4) 3 [0,3] t1 b2
  have b3 : a 7 ≠ 1 := exclude [0] (fun u v => edge r7 v u) (a 7) (a 3) 1 d3 c7 (by decide +kernel)
  have t3 : a 7 ∈ [0,2,3] := remove (a 7) 1 [0,1,2,3] d7 b3
  have b4 : a 7 ≠ 2 := exclude [0] (fun u v => edge r7 v u) (a 7) (a 3) 2 d3 c7 (by decide +kernel)
  have t4 : a 7 ∈ [0,3] := remove (a 7) 2 [0,2,3] t3 b4
  have b5 : a 7 ≠ 3 := exclude [0] (fun u v => edge r7 v u) (a 7) (a 3) 3 d3 c7 (by decide +kernel)
  have t5 : a 7 ∈ [0] := remove (a 7) 3 [0,3] t4 b5
  have b6 : a 5 ≠ 1 := exclude [0] (fun u v => edge r8 v u) (a 5) (a 4) 1 t2 c8 (by decide +kernel)
  have t6 : a 5 ∈ [0,2,3] := remove (a 5) 1 [0,1,2,3] d5 b6
  have b7 : a 5 ≠ 2 := exclude [0] (fun u v => edge r8 v u) (a 5) (a 4) 2 t2 c8 (by decide +kernel)
  have t7 : a 5 ∈ [0,3] := remove (a 5) 2 [0,2,3] t6 b7
  have b8 : a 5 ≠ 3 := exclude [0] (fun u v => edge r8 v u) (a 5) (a 4) 3 t2 c8 (by decide +kernel)
  have t8 : a 5 ∈ [0] := remove (a 5) 3 [0,3] t7 b8
  have b9 : a 6 ≠ 1 := exclude [0] (fun u v => edge r9 v u) (a 6) (a 4) 1 t2 c9 (by decide +kernel)
  have t9 : a 6 ∈ [0,2,3] := remove (a 6) 1 [0,1,2,3] d6 b9
  have b10 : a 6 ≠ 2 := exclude [0] (fun u v => edge r9 v u) (a 6) (a 4) 2 t2 c9 (by decide +kernel)
  have t10 : a 6 ∈ [0,3] := remove (a 6) 2 [0,2,3] t9 b10
  have b11 : a 6 ≠ 3 := exclude [0] (fun u v => edge r9 v u) (a 6) (a 4) 3 t2 c9 (by decide +kernel)
  have t11 : a 6 ∈ [0] := remove (a 6) 3 [0,3] t10 b11
  exact And.intro t2 (And.intro t5 (And.intro t8 (t11)))
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0])
    (start2 : a 2 ∈ [0])
    (start3 : a 3 ∈ [0])
    (start4 : a 4 ∈ [0,1,2,3])
    (start5 : a 5 ∈ [0,1,2,3])
    (start6 : a 6 ∈ [0,1,2,3])
    (start7 : a 7 ∈ [0,1,2,3])
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
  have group1 := chunk0 a start4 start0 start7 start3 start5 start6 c2 c7 c8 c9
  rcases group1 with ⟨h2,h3,h4,h5⟩
  exact And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 start1) (And.intro (forced (a 2) 0 start2) (And.intro (forced (a 3) 0 start3) (And.intro (forced (a 4) 0 h2) (And.intro (forced (a 5) 0 h4) (And.intro (forced (a 6) 0 h5) (forced (a 7) 0 h3)))))))
#print axioms cover
end PartitionCover205_48
