import FiniteDomain205
namespace PartitionCover205_79
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
def r0 : Array Nat := #[3]
def r1 : Array Nat := #[3]
def r2 : Array Nat := #[3]
def r3 : Array Nat := #[1,2]
def r4 : Array Nat := #[1,2]
def r5 : Array Nat := #[1,2]
def r6 : Array Nat := #[1,2]
def r7 : Array Nat := #[1,2]
def r8 : Array Nat := #[1,2]
def r9 : Array Nat := #[1,2]
def r10 : Array Nat := #[1,2]
def r11 : Array Nat := #[1,2]
theorem chunk0 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,1])
    (d1 : a 1 ∈ [0])
    (d5 : a 5 ∈ [0,1])
    (d2 : a 2 ∈ [0,1])
    (d6 : a 6 ∈ [0,1])
    (d7 : a 7 ∈ [0,1])
    (d4 : a 4 ∈ [0,1])
    (c3 : edge r3 (a 1) (a 3)=true)
    (c4 : edge r4 (a 1) (a 5)=true)
    (c5 : edge r5 (a 2) (a 3)=true)
    (c6 : edge r6 (a 2) (a 6)=true)
    (c7 : edge r7 (a 3) (a 7)=true)
    (c8 : edge r8 (a 4) (a 5)=true)
    : a 3 ∈ [0] ∧ a 5 ∈ [0] ∧ a 2 ∈ [0] ∧ a 6 ∈ [0] ∧ a 7 ∈ [0] ∧ a 4 ∈ [0] := by
  have b0 : a 3 ≠ 1 := exclude [0] (fun u v => edge r3 v u) (a 3) (a 1) 1 d1 c3 (by decide +kernel)
  have t0 : a 3 ∈ [0] := remove (a 3) 1 [0,1] d3 b0
  have b1 : a 5 ≠ 1 := exclude [0] (fun u v => edge r4 v u) (a 5) (a 1) 1 d1 c4 (by decide +kernel)
  have t1 : a 5 ∈ [0] := remove (a 5) 1 [0,1] d5 b1
  have b2 : a 2 ≠ 1 := exclude [0] (edge r5) (a 2) (a 3) 1 t0 c5 (by decide +kernel)
  have t2 : a 2 ∈ [0] := remove (a 2) 1 [0,1] d2 b2
  have b3 : a 6 ≠ 1 := exclude [0] (fun u v => edge r6 v u) (a 6) (a 2) 1 t2 c6 (by decide +kernel)
  have t3 : a 6 ∈ [0] := remove (a 6) 1 [0,1] d6 b3
  have b4 : a 7 ≠ 1 := exclude [0] (fun u v => edge r7 v u) (a 7) (a 3) 1 t0 c7 (by decide +kernel)
  have t4 : a 7 ∈ [0] := remove (a 7) 1 [0,1] d7 b4
  have b5 : a 4 ≠ 1 := exclude [0] (edge r8) (a 4) (a 5) 1 t1 c8 (by decide +kernel)
  have t5 : a 4 ∈ [0] := remove (a 4) 1 [0,1] d4 b5
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (t5)))))

theorem chunk1 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,1])
    (d1 : a 1 ∈ [1])
    (d5 : a 5 ∈ [0,1])
    (d2 : a 2 ∈ [0,1])
    (d6 : a 6 ∈ [0,1])
    (d7 : a 7 ∈ [0,1])
    (d4 : a 4 ∈ [0,1])
    (c3 : edge r3 (a 1) (a 3)=true)
    (c4 : edge r4 (a 1) (a 5)=true)
    (c5 : edge r5 (a 2) (a 3)=true)
    (c6 : edge r6 (a 2) (a 6)=true)
    (c7 : edge r7 (a 3) (a 7)=true)
    (c8 : edge r8 (a 4) (a 5)=true)
    : a 3 ∈ [1] ∧ a 5 ∈ [1] ∧ a 2 ∈ [1] ∧ a 6 ∈ [1] ∧ a 7 ∈ [1] ∧ a 4 ∈ [1] := by
  have b0 : a 3 ≠ 0 := exclude [1] (fun u v => edge r3 v u) (a 3) (a 1) 0 d1 c3 (by decide +kernel)
  have t0 : a 3 ∈ [1] := remove (a 3) 0 [0,1] d3 b0
  have b1 : a 5 ≠ 0 := exclude [1] (fun u v => edge r4 v u) (a 5) (a 1) 0 d1 c4 (by decide +kernel)
  have t1 : a 5 ∈ [1] := remove (a 5) 0 [0,1] d5 b1
  have b2 : a 2 ≠ 0 := exclude [1] (edge r5) (a 2) (a 3) 0 t0 c5 (by decide +kernel)
  have t2 : a 2 ∈ [1] := remove (a 2) 0 [0,1] d2 b2
  have b3 : a 6 ≠ 0 := exclude [1] (fun u v => edge r6 v u) (a 6) (a 2) 0 t2 c6 (by decide +kernel)
  have t3 : a 6 ∈ [1] := remove (a 6) 0 [0,1] d6 b3
  have b4 : a 7 ≠ 0 := exclude [1] (fun u v => edge r7 v u) (a 7) (a 3) 0 t0 c7 (by decide +kernel)
  have t4 : a 7 ∈ [1] := remove (a 7) 0 [0,1] d7 b4
  have b5 : a 4 ≠ 0 := exclude [1] (edge r8) (a 4) (a 5) 0 t1 c8 (by decide +kernel)
  have t5 : a 4 ∈ [1] := remove (a 4) 0 [0,1] d4 b5
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (t5)))))
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0,1])
    (start2 : a 2 ∈ [0,1])
    (start3 : a 3 ∈ [0,1])
    (start4 : a 4 ∈ [0,1])
    (start5 : a 5 ∈ [0,1])
    (start6 : a 6 ∈ [0,1])
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
    : (a 0=0 ∧ a 1=0 ∧ a 2=0 ∧ a 3=0 ∧ a 4=0 ∧ a 5=0 ∧ a 6=0 ∧ a 7=0) ∨
      (a 0=0 ∧ a 1=1 ∧ a 2=1 ∧ a 3=1 ∧ a 4=1 ∧ a 5=1 ∧ a 6=1 ∧ a 7=1) := by
  rcases (show a 1=0 ∨ a 1=1 from by simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using start1) with q1 | q2
  · have h3 : a 1 ∈ [0] := List.mem_singleton.mpr q1
    have group4 := chunk0 a start3 h3 start5 start2 start6 start7 start4 c3 c4 c5 c6 c7 c8
    rcases group4 with ⟨h5,h6,h7,h8,h9,h10⟩
    exact Or.inl (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 h3) (And.intro (forced (a 2) 0 h7) (And.intro (forced (a 3) 0 h5) (And.intro (forced (a 4) 0 h10) (And.intro (forced (a 5) 0 h6) (And.intro (forced (a 6) 0 h8) (forced (a 7) 0 h9))))))))
  · have h11 : a 1 ∈ [1] := List.mem_singleton.mpr q2
    have group12 := chunk1 a start3 h11 start5 start2 start6 start7 start4 c3 c4 c5 c6 c7 c8
    rcases group12 with ⟨h13,h14,h15,h16,h17,h18⟩
    exact Or.inr (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 1 h11) (And.intro (forced (a 2) 1 h15) (And.intro (forced (a 3) 1 h13) (And.intro (forced (a 4) 1 h18) (And.intro (forced (a 5) 1 h14) (And.intro (forced (a 6) 1 h16) (forced (a 7) 1 h17))))))))
#print axioms cover
end PartitionCover205_79
