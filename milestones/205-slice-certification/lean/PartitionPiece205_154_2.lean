import PartitionData205_154
namespace PartitionCover205_154
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,1])
    (d1 : a 1 ∈ [1])
    (d5 : a 5 ∈ [0,6])
    (d2 : a 2 ∈ [0,1])
    (d6 : a 6 ∈ [0,4])
    (d7 : a 7 ∈ [0,6])
    (d11 : a 11 ∈ [0,1])
    (d4 : a 4 ∈ [0,4])
    (d12 : a 12 ∈ [0,4])
    (d13 : a 13 ∈ [0,4])
    (d14 : a 14 ∈ [0,4])
    (d15 : a 15 ∈ [0,4])
    (d10 : a 10 ∈ [0,8])
    (d8 : a 8 ∈ [0,16])
    (c4 : edge r4 (a 1) (a 3)=true)
    (c5 : edge r5 (a 1) (a 5)=true)
    (c7 : edge r7 (a 2) (a 3)=true)
    (c8 : edge r8 (a 2) (a 6)=true)
    (c10 : edge r10 (a 3) (a 7)=true)
    (c11 : edge r11 (a 3) (a 11)=true)
    (c12 : edge r12 (a 4) (a 5)=true)
    (c14 : edge r14 (a 4) (a 12)=true)
    (c16 : edge r16 (a 5) (a 13)=true)
    (c18 : edge r18 (a 6) (a 14)=true)
    (c19 : edge r19 (a 7) (a 15)=true)
    (c21 : edge r21 (a 8) (a 10)=true)
    (c26 : edge r26 (a 10) (a 14)=true)
    : a 3 ∈ [1] ∧ a 5 ∈ [6] ∧ a 2 ∈ [1] ∧ a 6 ∈ [4] ∧ a 7 ∈ [6] ∧ a 11 ∈ [1] ∧ a 4 ∈ [4] ∧ a 12 ∈ [4] ∧ a 13 ∈ [4] ∧ a 14 ∈ [4] ∧ a 15 ∈ [4] ∧ a 10 ∈ [8] ∧ a 8 ∈ [16] := by
  have b0 : a 3 ≠ 0 := exclude [1] (fun u v => edge r4 v u) (a 3) (a 1) 0 d1 c4 (by decide +kernel)
  have t0 : a 3 ∈ [1] := remove (a 3) 0 [0,1] d3 b0
  have b1 : a 5 ≠ 0 := exclude [1] (fun u v => edge r5 v u) (a 5) (a 1) 0 d1 c5 (by decide +kernel)
  have t1 : a 5 ∈ [6] := remove (a 5) 0 [0,6] d5 b1
  have b2 : a 2 ≠ 0 := exclude [1] (edge r7) (a 2) (a 3) 0 t0 c7 (by decide +kernel)
  have t2 : a 2 ∈ [1] := remove (a 2) 0 [0,1] d2 b2
  have b3 : a 6 ≠ 0 := exclude [1] (fun u v => edge r8 v u) (a 6) (a 2) 0 t2 c8 (by decide +kernel)
  have t3 : a 6 ∈ [4] := remove (a 6) 0 [0,4] d6 b3
  have b4 : a 7 ≠ 0 := exclude [1] (fun u v => edge r10 v u) (a 7) (a 3) 0 t0 c10 (by decide +kernel)
  have t4 : a 7 ∈ [6] := remove (a 7) 0 [0,6] d7 b4
  have b5 : a 11 ≠ 0 := exclude [1] (fun u v => edge r11 v u) (a 11) (a 3) 0 t0 c11 (by decide +kernel)
  have t5 : a 11 ∈ [1] := remove (a 11) 0 [0,1] d11 b5
  have b6 : a 4 ≠ 0 := exclude [6] (edge r12) (a 4) (a 5) 0 t1 c12 (by decide +kernel)
  have t6 : a 4 ∈ [4] := remove (a 4) 0 [0,4] d4 b6
  have b7 : a 12 ≠ 0 := exclude [4] (fun u v => edge r14 v u) (a 12) (a 4) 0 t6 c14 (by decide +kernel)
  have t7 : a 12 ∈ [4] := remove (a 12) 0 [0,4] d12 b7
  have b8 : a 13 ≠ 0 := exclude [6] (fun u v => edge r16 v u) (a 13) (a 5) 0 t1 c16 (by decide +kernel)
  have t8 : a 13 ∈ [4] := remove (a 13) 0 [0,4] d13 b8
  have b9 : a 14 ≠ 0 := exclude [4] (fun u v => edge r18 v u) (a 14) (a 6) 0 t3 c18 (by decide +kernel)
  have t9 : a 14 ∈ [4] := remove (a 14) 0 [0,4] d14 b9
  have b10 : a 15 ≠ 0 := exclude [6] (fun u v => edge r19 v u) (a 15) (a 7) 0 t4 c19 (by decide +kernel)
  have t10 : a 15 ∈ [4] := remove (a 15) 0 [0,4] d15 b10
  have b11 : a 10 ≠ 0 := exclude [4] (edge r26) (a 10) (a 14) 0 t9 c26 (by decide +kernel)
  have t11 : a 10 ∈ [8] := remove (a 10) 0 [0,8] d10 b11
  have b12 : a 8 ≠ 0 := exclude [8] (edge r21) (a 8) (a 10) 0 t11 c21 (by decide +kernel)
  have t12 : a 8 ∈ [16] := remove (a 8) 0 [0,16] d8 b12
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (t12))))))))))))
#print axioms chunk8
end PartitionCover205_154
