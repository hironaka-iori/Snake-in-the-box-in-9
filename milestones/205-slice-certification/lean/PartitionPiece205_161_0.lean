import PartitionData205_161
namespace PartitionCover205_161
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d2 : a 2 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19])
    (d0 : a 0 ∈ [0])
    (c1 : edge r1 (a 0) (a 2)=true)
    : a 2 ∈ [0,17,18,19] := by
  have b0 : a 2 ≠ 1 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 1 d0 c1 (by decide +kernel)
  have t0 : a 2 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 2) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] d2 b0
  have b1 : a 2 ≠ 2 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 2 d0 c1 (by decide +kernel)
  have t1 : a 2 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 2) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t0 b1
  have b2 : a 2 ≠ 3 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 3 d0 c1 (by decide +kernel)
  have t2 : a 2 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 2) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t1 b2
  have b3 : a 2 ≠ 4 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 4 d0 c1 (by decide +kernel)
  have t3 : a 2 ∈ [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 2) 4 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t2 b3
  have b4 : a 2 ≠ 5 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 5 d0 c1 (by decide +kernel)
  have t4 : a 2 ∈ [0,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 2) 5 [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t3 b4
  have b5 : a 2 ≠ 6 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 6 d0 c1 (by decide +kernel)
  have t5 : a 2 ∈ [0,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 2) 6 [0,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t4 b5
  have b6 : a 2 ≠ 7 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 7 d0 c1 (by decide +kernel)
  have t6 : a 2 ∈ [0,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 2) 7 [0,7,8,9,10,11,12,13,14,15,16,17,18,19] t5 b6
  have b7 : a 2 ≠ 8 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 8 d0 c1 (by decide +kernel)
  have t7 : a 2 ∈ [0,9,10,11,12,13,14,15,16,17,18,19] := remove (a 2) 8 [0,8,9,10,11,12,13,14,15,16,17,18,19] t6 b7
  have b8 : a 2 ≠ 9 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 9 d0 c1 (by decide +kernel)
  have t8 : a 2 ∈ [0,10,11,12,13,14,15,16,17,18,19] := remove (a 2) 9 [0,9,10,11,12,13,14,15,16,17,18,19] t7 b8
  have b9 : a 2 ≠ 10 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 10 d0 c1 (by decide +kernel)
  have t9 : a 2 ∈ [0,11,12,13,14,15,16,17,18,19] := remove (a 2) 10 [0,10,11,12,13,14,15,16,17,18,19] t8 b9
  have b10 : a 2 ≠ 11 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 11 d0 c1 (by decide +kernel)
  have t10 : a 2 ∈ [0,12,13,14,15,16,17,18,19] := remove (a 2) 11 [0,11,12,13,14,15,16,17,18,19] t9 b10
  have b11 : a 2 ≠ 12 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 12 d0 c1 (by decide +kernel)
  have t11 : a 2 ∈ [0,13,14,15,16,17,18,19] := remove (a 2) 12 [0,12,13,14,15,16,17,18,19] t10 b11
  have b12 : a 2 ≠ 13 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 13 d0 c1 (by decide +kernel)
  have t12 : a 2 ∈ [0,14,15,16,17,18,19] := remove (a 2) 13 [0,13,14,15,16,17,18,19] t11 b12
  have b13 : a 2 ≠ 14 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 14 d0 c1 (by decide +kernel)
  have t13 : a 2 ∈ [0,15,16,17,18,19] := remove (a 2) 14 [0,14,15,16,17,18,19] t12 b13
  have b14 : a 2 ≠ 15 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 15 d0 c1 (by decide +kernel)
  have t14 : a 2 ∈ [0,16,17,18,19] := remove (a 2) 15 [0,15,16,17,18,19] t13 b14
  have b15 : a 2 ≠ 16 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 16 d0 c1 (by decide +kernel)
  have t15 : a 2 ∈ [0,17,18,19] := remove (a 2) 16 [0,16,17,18,19] t14 b15
  exact t15

theorem chunk1 (a : Nat → Nat)
    (d2 : a 2 ∈ [0,17,18,19])
    (d0 : a 0 ∈ [0])
    (d4 : a 4 ∈ [0,1,2,3,4,5,6])
    (d8 : a 8 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (c1 : edge r1 (a 0) (a 2)=true)
    (c2 : edge r2 (a 0) (a 4)=true)
    (c3 : edge r3 (a 0) (a 8)=true)
    : a 2 ∈ [0] ∧ a 4 ∈ [0] ∧ a 8 ∈ [0,4,9,10,11,12,13,14,15,16,17] := by
  have b0 : a 2 ≠ 17 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 17 d0 c1 (by decide +kernel)
  have t0 : a 2 ∈ [0,18,19] := remove (a 2) 17 [0,17,18,19] d2 b0
  have b1 : a 2 ≠ 18 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 18 d0 c1 (by decide +kernel)
  have t1 : a 2 ∈ [0,19] := remove (a 2) 18 [0,18,19] t0 b1
  have b2 : a 2 ≠ 19 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 19 d0 c1 (by decide +kernel)
  have t2 : a 2 ∈ [0] := remove (a 2) 19 [0,19] t1 b2
  have b3 : a 4 ≠ 1 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 1 d0 c2 (by decide +kernel)
  have t3 : a 4 ∈ [0,2,3,4,5,6] := remove (a 4) 1 [0,1,2,3,4,5,6] d4 b3
  have b4 : a 4 ≠ 2 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 2 d0 c2 (by decide +kernel)
  have t4 : a 4 ∈ [0,3,4,5,6] := remove (a 4) 2 [0,2,3,4,5,6] t3 b4
  have b5 : a 4 ≠ 3 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 3 d0 c2 (by decide +kernel)
  have t5 : a 4 ∈ [0,4,5,6] := remove (a 4) 3 [0,3,4,5,6] t4 b5
  have b6 : a 4 ≠ 4 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 4 d0 c2 (by decide +kernel)
  have t6 : a 4 ∈ [0,5,6] := remove (a 4) 4 [0,4,5,6] t5 b6
  have b7 : a 4 ≠ 5 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 5 d0 c2 (by decide +kernel)
  have t7 : a 4 ∈ [0,6] := remove (a 4) 5 [0,5,6] t6 b7
  have b8 : a 4 ≠ 6 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 6 d0 c2 (by decide +kernel)
  have t8 : a 4 ∈ [0] := remove (a 4) 6 [0,6] t7 b8
  have b9 : a 8 ≠ 1 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 1 d0 c3 (by decide +kernel)
  have t9 : a 8 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 8) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d8 b9
  have b10 : a 8 ≠ 2 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 2 d0 c3 (by decide +kernel)
  have t10 : a 8 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 8) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t9 b10
  have b11 : a 8 ≠ 3 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 3 d0 c3 (by decide +kernel)
  have t11 : a 8 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 8) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t10 b11
  have b12 : a 8 ≠ 5 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 5 d0 c3 (by decide +kernel)
  have t12 : a 8 ∈ [0,4,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 8) 5 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t11 b12
  have b13 : a 8 ≠ 6 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 6 d0 c3 (by decide +kernel)
  have t13 : a 8 ∈ [0,4,7,8,9,10,11,12,13,14,15,16,17] := remove (a 8) 6 [0,4,6,7,8,9,10,11,12,13,14,15,16,17] t12 b13
  have b14 : a 8 ≠ 7 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 7 d0 c3 (by decide +kernel)
  have t14 : a 8 ∈ [0,4,8,9,10,11,12,13,14,15,16,17] := remove (a 8) 7 [0,4,7,8,9,10,11,12,13,14,15,16,17] t13 b14
  have b15 : a 8 ≠ 8 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 8 d0 c3 (by decide +kernel)
  have t15 : a 8 ∈ [0,4,9,10,11,12,13,14,15,16,17] := remove (a 8) 8 [0,4,8,9,10,11,12,13,14,15,16,17] t14 b15
  exact And.intro t2 (And.intro t8 (t15))

theorem chunk2 (a : Nat → Nat)
    (d8 : a 8 ∈ [0,4,9,10,11,12,13,14,15,16,17])
    (d0 : a 0 ∈ [0])
    (d3 : a 3 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19])
    (d2 : a 2 ∈ [0])
    (c3 : edge r3 (a 0) (a 8)=true)
    (c7 : edge r7 (a 2) (a 3)=true)
    : a 8 ∈ [0,4] ∧ a 3 ∈ [0,8,9,10,11,12,13,14,15,16,17,18,19] := by
  have b0 : a 8 ≠ 9 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 9 d0 c3 (by decide +kernel)
  have t0 : a 8 ∈ [0,4,10,11,12,13,14,15,16,17] := remove (a 8) 9 [0,4,9,10,11,12,13,14,15,16,17] d8 b0
  have b1 : a 8 ≠ 10 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 10 d0 c3 (by decide +kernel)
  have t1 : a 8 ∈ [0,4,11,12,13,14,15,16,17] := remove (a 8) 10 [0,4,10,11,12,13,14,15,16,17] t0 b1
  have b2 : a 8 ≠ 11 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 11 d0 c3 (by decide +kernel)
  have t2 : a 8 ∈ [0,4,12,13,14,15,16,17] := remove (a 8) 11 [0,4,11,12,13,14,15,16,17] t1 b2
  have b3 : a 8 ≠ 12 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 12 d0 c3 (by decide +kernel)
  have t3 : a 8 ∈ [0,4,13,14,15,16,17] := remove (a 8) 12 [0,4,12,13,14,15,16,17] t2 b3
  have b4 : a 8 ≠ 13 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 13 d0 c3 (by decide +kernel)
  have t4 : a 8 ∈ [0,4,14,15,16,17] := remove (a 8) 13 [0,4,13,14,15,16,17] t3 b4
  have b5 : a 8 ≠ 14 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 14 d0 c3 (by decide +kernel)
  have t5 : a 8 ∈ [0,4,15,16,17] := remove (a 8) 14 [0,4,14,15,16,17] t4 b5
  have b6 : a 8 ≠ 15 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 15 d0 c3 (by decide +kernel)
  have t6 : a 8 ∈ [0,4,16,17] := remove (a 8) 15 [0,4,15,16,17] t5 b6
  have b7 : a 8 ≠ 16 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 16 d0 c3 (by decide +kernel)
  have t7 : a 8 ∈ [0,4,17] := remove (a 8) 16 [0,4,16,17] t6 b7
  have b8 : a 8 ≠ 17 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 17 d0 c3 (by decide +kernel)
  have t8 : a 8 ∈ [0,4] := remove (a 8) 17 [0,4,17] t7 b8
  have b9 : a 3 ≠ 1 := exclude [0] (fun u v => edge r7 v u) (a 3) (a 2) 1 d2 c7 (by decide +kernel)
  have t9 : a 3 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 3) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] d3 b9
  have b10 : a 3 ≠ 2 := exclude [0] (fun u v => edge r7 v u) (a 3) (a 2) 2 d2 c7 (by decide +kernel)
  have t10 : a 3 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 3) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t9 b10
  have b11 : a 3 ≠ 3 := exclude [0] (fun u v => edge r7 v u) (a 3) (a 2) 3 d2 c7 (by decide +kernel)
  have t11 : a 3 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 3) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t10 b11
  have b12 : a 3 ≠ 4 := exclude [0] (fun u v => edge r7 v u) (a 3) (a 2) 4 d2 c7 (by decide +kernel)
  have t12 : a 3 ∈ [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 3) 4 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t11 b12
  have b13 : a 3 ≠ 5 := exclude [0] (fun u v => edge r7 v u) (a 3) (a 2) 5 d2 c7 (by decide +kernel)
  have t13 : a 3 ∈ [0,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 3) 5 [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t12 b13
  have b14 : a 3 ≠ 6 := exclude [0] (fun u v => edge r7 v u) (a 3) (a 2) 6 d2 c7 (by decide +kernel)
  have t14 : a 3 ∈ [0,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 3) 6 [0,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t13 b14
  have b15 : a 3 ≠ 7 := exclude [0] (fun u v => edge r7 v u) (a 3) (a 2) 7 d2 c7 (by decide +kernel)
  have t15 : a 3 ∈ [0,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 3) 7 [0,7,8,9,10,11,12,13,14,15,16,17,18,19] t14 b15
  exact And.intro t8 (t15)

theorem chunk3 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,8,9,10,11,12,13,14,15,16,17,18,19])
    (d2 : a 2 ∈ [0])
    (d6 : a 6 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19])
    (c7 : edge r7 (a 2) (a 3)=true)
    (c8 : edge r8 (a 2) (a 6)=true)
    : a 3 ∈ [0] ∧ a 6 ∈ [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := by
  have b0 : a 3 ≠ 8 := exclude [0] (fun u v => edge r7 v u) (a 3) (a 2) 8 d2 c7 (by decide +kernel)
  have t0 : a 3 ∈ [0,9,10,11,12,13,14,15,16,17,18,19] := remove (a 3) 8 [0,8,9,10,11,12,13,14,15,16,17,18,19] d3 b0
  have b1 : a 3 ≠ 9 := exclude [0] (fun u v => edge r7 v u) (a 3) (a 2) 9 d2 c7 (by decide +kernel)
  have t1 : a 3 ∈ [0,10,11,12,13,14,15,16,17,18,19] := remove (a 3) 9 [0,9,10,11,12,13,14,15,16,17,18,19] t0 b1
  have b2 : a 3 ≠ 10 := exclude [0] (fun u v => edge r7 v u) (a 3) (a 2) 10 d2 c7 (by decide +kernel)
  have t2 : a 3 ∈ [0,11,12,13,14,15,16,17,18,19] := remove (a 3) 10 [0,10,11,12,13,14,15,16,17,18,19] t1 b2
  have b3 : a 3 ≠ 11 := exclude [0] (fun u v => edge r7 v u) (a 3) (a 2) 11 d2 c7 (by decide +kernel)
  have t3 : a 3 ∈ [0,12,13,14,15,16,17,18,19] := remove (a 3) 11 [0,11,12,13,14,15,16,17,18,19] t2 b3
  have b4 : a 3 ≠ 12 := exclude [0] (fun u v => edge r7 v u) (a 3) (a 2) 12 d2 c7 (by decide +kernel)
  have t4 : a 3 ∈ [0,13,14,15,16,17,18,19] := remove (a 3) 12 [0,12,13,14,15,16,17,18,19] t3 b4
  have b5 : a 3 ≠ 13 := exclude [0] (fun u v => edge r7 v u) (a 3) (a 2) 13 d2 c7 (by decide +kernel)
  have t5 : a 3 ∈ [0,14,15,16,17,18,19] := remove (a 3) 13 [0,13,14,15,16,17,18,19] t4 b5
  have b6 : a 3 ≠ 14 := exclude [0] (fun u v => edge r7 v u) (a 3) (a 2) 14 d2 c7 (by decide +kernel)
  have t6 : a 3 ∈ [0,15,16,17,18,19] := remove (a 3) 14 [0,14,15,16,17,18,19] t5 b6
  have b7 : a 3 ≠ 15 := exclude [0] (fun u v => edge r7 v u) (a 3) (a 2) 15 d2 c7 (by decide +kernel)
  have t7 : a 3 ∈ [0,16,17,18,19] := remove (a 3) 15 [0,15,16,17,18,19] t6 b7
  have b8 : a 3 ≠ 16 := exclude [0] (fun u v => edge r7 v u) (a 3) (a 2) 16 d2 c7 (by decide +kernel)
  have t8 : a 3 ∈ [0,17,18,19] := remove (a 3) 16 [0,16,17,18,19] t7 b8
  have b9 : a 3 ≠ 17 := exclude [0] (fun u v => edge r7 v u) (a 3) (a 2) 17 d2 c7 (by decide +kernel)
  have t9 : a 3 ∈ [0,18,19] := remove (a 3) 17 [0,17,18,19] t8 b9
  have b10 : a 3 ≠ 18 := exclude [0] (fun u v => edge r7 v u) (a 3) (a 2) 18 d2 c7 (by decide +kernel)
  have t10 : a 3 ∈ [0,19] := remove (a 3) 18 [0,18,19] t9 b10
  have b11 : a 3 ≠ 19 := exclude [0] (fun u v => edge r7 v u) (a 3) (a 2) 19 d2 c7 (by decide +kernel)
  have t11 : a 3 ∈ [0] := remove (a 3) 19 [0,19] t10 b11
  have b12 : a 6 ≠ 1 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 1 d2 c8 (by decide +kernel)
  have t12 : a 6 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 6) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] d6 b12
  have b13 : a 6 ≠ 2 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 2 d2 c8 (by decide +kernel)
  have t13 : a 6 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 6) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t12 b13
  have b14 : a 6 ≠ 3 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 3 d2 c8 (by decide +kernel)
  have t14 : a 6 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 6) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t13 b14
  have b15 : a 6 ≠ 4 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 4 d2 c8 (by decide +kernel)
  have t15 : a 6 ∈ [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 6) 4 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t14 b15
  exact And.intro t11 (t15)

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_161
