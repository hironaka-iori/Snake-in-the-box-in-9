import PartitionData205_217
namespace PartitionCover205_217
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d5 : a 5 ∈ [0,2,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d1 : a 1 ∈ [0,1,2])
    (d9 : a 9 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c6 : edge r6 (a 1) (a 5)=true)
    (c7 : edge r7 (a 1) (a 9)=true)
    : a 5 ∈ [0,2,12,14,18,20] ∧ a 9 ∈ [0,1,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 5 ≠ 10 := exclude [0,1,2] (fun u v => edge r6 v u) (a 5) (a 1) 10 d1 c6 (by decide +kernel)
  have t0 : a 5 ∈ [0,2,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 5) 10 [0,2,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d5 b0
  have b1 : a 5 ≠ 11 := exclude [0,1,2] (fun u v => edge r6 v u) (a 5) (a 1) 11 d1 c6 (by decide +kernel)
  have t1 : a 5 ∈ [0,2,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 5) 11 [0,2,11,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 5 ≠ 13 := exclude [0,1,2] (fun u v => edge r6 v u) (a 5) (a 1) 13 d1 c6 (by decide +kernel)
  have t2 : a 5 ∈ [0,2,12,14,15,16,17,18,19,20,21,22,23] := remove (a 5) 13 [0,2,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 5 ≠ 15 := exclude [0,1,2] (fun u v => edge r6 v u) (a 5) (a 1) 15 d1 c6 (by decide +kernel)
  have t3 : a 5 ∈ [0,2,12,14,16,17,18,19,20,21,22,23] := remove (a 5) 15 [0,2,12,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 5 ≠ 16 := exclude [0,1,2] (fun u v => edge r6 v u) (a 5) (a 1) 16 d1 c6 (by decide +kernel)
  have t4 : a 5 ∈ [0,2,12,14,17,18,19,20,21,22,23] := remove (a 5) 16 [0,2,12,14,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 5 ≠ 17 := exclude [0,1,2] (fun u v => edge r6 v u) (a 5) (a 1) 17 d1 c6 (by decide +kernel)
  have t5 : a 5 ∈ [0,2,12,14,18,19,20,21,22,23] := remove (a 5) 17 [0,2,12,14,17,18,19,20,21,22,23] t4 b5
  have b6 : a 5 ≠ 19 := exclude [0,1,2] (fun u v => edge r6 v u) (a 5) (a 1) 19 d1 c6 (by decide +kernel)
  have t6 : a 5 ∈ [0,2,12,14,18,20,21,22,23] := remove (a 5) 19 [0,2,12,14,18,19,20,21,22,23] t5 b6
  have b7 : a 5 ≠ 21 := exclude [0,1,2] (fun u v => edge r6 v u) (a 5) (a 1) 21 d1 c6 (by decide +kernel)
  have t7 : a 5 ∈ [0,2,12,14,18,20,22,23] := remove (a 5) 21 [0,2,12,14,18,20,21,22,23] t6 b7
  have b8 : a 5 ≠ 22 := exclude [0,1,2] (fun u v => edge r6 v u) (a 5) (a 1) 22 d1 c6 (by decide +kernel)
  have t8 : a 5 ∈ [0,2,12,14,18,20,23] := remove (a 5) 22 [0,2,12,14,18,20,22,23] t7 b8
  have b9 : a 5 ≠ 23 := exclude [0,1,2] (fun u v => edge r6 v u) (a 5) (a 1) 23 d1 c6 (by decide +kernel)
  have t9 : a 5 ∈ [0,2,12,14,18,20] := remove (a 5) 23 [0,2,12,14,18,20,23] t8 b9
  have b10 : a 9 ≠ 2 := exclude [0,1,2] (fun u v => edge r7 v u) (a 9) (a 1) 2 d1 c7 (by decide +kernel)
  have t10 : a 9 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 9) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d9 b10
  have b11 : a 9 ≠ 3 := exclude [0,1,2] (fun u v => edge r7 v u) (a 9) (a 1) 3 d1 c7 (by decide +kernel)
  have t11 : a 9 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 9) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 9 ≠ 4 := exclude [0,1,2] (fun u v => edge r7 v u) (a 9) (a 1) 4 d1 c7 (by decide +kernel)
  have t12 : a 9 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 9) 4 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 9 ≠ 5 := exclude [0,1,2] (fun u v => edge r7 v u) (a 9) (a 1) 5 d1 c7 (by decide +kernel)
  have t13 : a 9 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 9) 5 [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 9 ≠ 6 := exclude [0,1,2] (fun u v => edge r7 v u) (a 9) (a 1) 6 d1 c7 (by decide +kernel)
  have t14 : a 9 ∈ [0,1,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 9) 6 [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 9 ≠ 7 := exclude [0,1,2] (fun u v => edge r7 v u) (a 9) (a 1) 7 d1 c7 (by decide +kernel)
  have t15 : a 9 ∈ [0,1,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 9) 7 [0,1,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t9 (t15)

theorem chunk5 (a : Nat → Nat)
    (d9 : a 9 ∈ [0,1,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d1 : a 1 ∈ [0,1,2])
    (d17 : a 17 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c7 : edge r7 (a 1) (a 9)=true)
    (c8 : edge r8 (a 1) (a 17)=true)
    : a 9 ∈ [0,1,14,15,16,17] ∧ a 17 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 9 ≠ 8 := exclude [0,1,2] (fun u v => edge r7 v u) (a 9) (a 1) 8 d1 c7 (by decide +kernel)
  have t0 : a 9 ∈ [0,1,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 9) 8 [0,1,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d9 b0
  have b1 : a 9 ≠ 9 := exclude [0,1,2] (fun u v => edge r7 v u) (a 9) (a 1) 9 d1 c7 (by decide +kernel)
  have t1 : a 9 ∈ [0,1,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 9) 9 [0,1,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 9 ≠ 10 := exclude [0,1,2] (fun u v => edge r7 v u) (a 9) (a 1) 10 d1 c7 (by decide +kernel)
  have t2 : a 9 ∈ [0,1,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 9) 10 [0,1,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 9 ≠ 11 := exclude [0,1,2] (fun u v => edge r7 v u) (a 9) (a 1) 11 d1 c7 (by decide +kernel)
  have t3 : a 9 ∈ [0,1,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 9) 11 [0,1,11,12,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 9 ≠ 12 := exclude [0,1,2] (fun u v => edge r7 v u) (a 9) (a 1) 12 d1 c7 (by decide +kernel)
  have t4 : a 9 ∈ [0,1,13,14,15,16,17,18,19,20,21,22,23] := remove (a 9) 12 [0,1,12,13,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 9 ≠ 13 := exclude [0,1,2] (fun u v => edge r7 v u) (a 9) (a 1) 13 d1 c7 (by decide +kernel)
  have t5 : a 9 ∈ [0,1,14,15,16,17,18,19,20,21,22,23] := remove (a 9) 13 [0,1,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 9 ≠ 18 := exclude [0,1,2] (fun u v => edge r7 v u) (a 9) (a 1) 18 d1 c7 (by decide +kernel)
  have t6 : a 9 ∈ [0,1,14,15,16,17,19,20,21,22,23] := remove (a 9) 18 [0,1,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 9 ≠ 19 := exclude [0,1,2] (fun u v => edge r7 v u) (a 9) (a 1) 19 d1 c7 (by decide +kernel)
  have t7 : a 9 ∈ [0,1,14,15,16,17,20,21,22,23] := remove (a 9) 19 [0,1,14,15,16,17,19,20,21,22,23] t6 b7
  have b8 : a 9 ≠ 20 := exclude [0,1,2] (fun u v => edge r7 v u) (a 9) (a 1) 20 d1 c7 (by decide +kernel)
  have t8 : a 9 ∈ [0,1,14,15,16,17,21,22,23] := remove (a 9) 20 [0,1,14,15,16,17,20,21,22,23] t7 b8
  have b9 : a 9 ≠ 21 := exclude [0,1,2] (fun u v => edge r7 v u) (a 9) (a 1) 21 d1 c7 (by decide +kernel)
  have t9 : a 9 ∈ [0,1,14,15,16,17,22,23] := remove (a 9) 21 [0,1,14,15,16,17,21,22,23] t8 b9
  have b10 : a 9 ≠ 22 := exclude [0,1,2] (fun u v => edge r7 v u) (a 9) (a 1) 22 d1 c7 (by decide +kernel)
  have t10 : a 9 ∈ [0,1,14,15,16,17,23] := remove (a 9) 22 [0,1,14,15,16,17,22,23] t9 b10
  have b11 : a 9 ≠ 23 := exclude [0,1,2] (fun u v => edge r7 v u) (a 9) (a 1) 23 d1 c7 (by decide +kernel)
  have t11 : a 9 ∈ [0,1,14,15,16,17] := remove (a 9) 23 [0,1,14,15,16,17,23] t10 b11
  have b12 : a 17 ≠ 2 := exclude [0,1,2] (fun u v => edge r8 v u) (a 17) (a 1) 2 d1 c8 (by decide +kernel)
  have t12 : a 17 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 17) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d17 b12
  have b13 : a 17 ≠ 3 := exclude [0,1,2] (fun u v => edge r8 v u) (a 17) (a 1) 3 d1 c8 (by decide +kernel)
  have t13 : a 17 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 17) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 17 ≠ 4 := exclude [0,1,2] (fun u v => edge r8 v u) (a 17) (a 1) 4 d1 c8 (by decide +kernel)
  have t14 : a 17 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 17) 4 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 17 ≠ 5 := exclude [0,1,2] (fun u v => edge r8 v u) (a 17) (a 1) 5 d1 c8 (by decide +kernel)
  have t15 : a 17 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 17) 5 [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t11 (t15)

theorem chunk6 (a : Nat → Nat)
    (d17 : a 17 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d1 : a 1 ∈ [0,1,2])
    (d3 : a 3 ∈ [0,1,2,3,4])
    (d2 : a 2 ∈ [0])
    (d6 : a 6 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c8 : edge r8 (a 1) (a 17)=true)
    (c9 : edge r9 (a 2) (a 3)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    : a 17 ∈ [0,1,10,11,12,13,16,17] ∧ a 3 ∈ [0,1] ∧ a 6 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 17 ≠ 6 := exclude [0,1,2] (fun u v => edge r8 v u) (a 17) (a 1) 6 d1 c8 (by decide +kernel)
  have t0 : a 17 ∈ [0,1,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 17) 6 [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d17 b0
  have b1 : a 17 ≠ 7 := exclude [0,1,2] (fun u v => edge r8 v u) (a 17) (a 1) 7 d1 c8 (by decide +kernel)
  have t1 : a 17 ∈ [0,1,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 17) 7 [0,1,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 17 ≠ 8 := exclude [0,1,2] (fun u v => edge r8 v u) (a 17) (a 1) 8 d1 c8 (by decide +kernel)
  have t2 : a 17 ∈ [0,1,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 17) 8 [0,1,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 17 ≠ 9 := exclude [0,1,2] (fun u v => edge r8 v u) (a 17) (a 1) 9 d1 c8 (by decide +kernel)
  have t3 : a 17 ∈ [0,1,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 17) 9 [0,1,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 17 ≠ 14 := exclude [0,1,2] (fun u v => edge r8 v u) (a 17) (a 1) 14 d1 c8 (by decide +kernel)
  have t4 : a 17 ∈ [0,1,10,11,12,13,15,16,17,18,19,20,21,22,23] := remove (a 17) 14 [0,1,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 17 ≠ 15 := exclude [0,1,2] (fun u v => edge r8 v u) (a 17) (a 1) 15 d1 c8 (by decide +kernel)
  have t5 : a 17 ∈ [0,1,10,11,12,13,16,17,18,19,20,21,22,23] := remove (a 17) 15 [0,1,10,11,12,13,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 17 ≠ 18 := exclude [0,1,2] (fun u v => edge r8 v u) (a 17) (a 1) 18 d1 c8 (by decide +kernel)
  have t6 : a 17 ∈ [0,1,10,11,12,13,16,17,19,20,21,22,23] := remove (a 17) 18 [0,1,10,11,12,13,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 17 ≠ 19 := exclude [0,1,2] (fun u v => edge r8 v u) (a 17) (a 1) 19 d1 c8 (by decide +kernel)
  have t7 : a 17 ∈ [0,1,10,11,12,13,16,17,20,21,22,23] := remove (a 17) 19 [0,1,10,11,12,13,16,17,19,20,21,22,23] t6 b7
  have b8 : a 17 ≠ 20 := exclude [0,1,2] (fun u v => edge r8 v u) (a 17) (a 1) 20 d1 c8 (by decide +kernel)
  have t8 : a 17 ∈ [0,1,10,11,12,13,16,17,21,22,23] := remove (a 17) 20 [0,1,10,11,12,13,16,17,20,21,22,23] t7 b8
  have b9 : a 17 ≠ 21 := exclude [0,1,2] (fun u v => edge r8 v u) (a 17) (a 1) 21 d1 c8 (by decide +kernel)
  have t9 : a 17 ∈ [0,1,10,11,12,13,16,17,22,23] := remove (a 17) 21 [0,1,10,11,12,13,16,17,21,22,23] t8 b9
  have b10 : a 17 ≠ 22 := exclude [0,1,2] (fun u v => edge r8 v u) (a 17) (a 1) 22 d1 c8 (by decide +kernel)
  have t10 : a 17 ∈ [0,1,10,11,12,13,16,17,23] := remove (a 17) 22 [0,1,10,11,12,13,16,17,22,23] t9 b10
  have b11 : a 17 ≠ 23 := exclude [0,1,2] (fun u v => edge r8 v u) (a 17) (a 1) 23 d1 c8 (by decide +kernel)
  have t11 : a 17 ∈ [0,1,10,11,12,13,16,17] := remove (a 17) 23 [0,1,10,11,12,13,16,17,23] t10 b11
  have b12 : a 3 ≠ 2 := exclude [0] (fun u v => edge r9 v u) (a 3) (a 2) 2 d2 c9 (by decide +kernel)
  have t12 : a 3 ∈ [0,1,3,4] := remove (a 3) 2 [0,1,2,3,4] d3 b12
  have b13 : a 3 ≠ 3 := exclude [0] (fun u v => edge r9 v u) (a 3) (a 2) 3 d2 c9 (by decide +kernel)
  have t13 : a 3 ∈ [0,1,4] := remove (a 3) 3 [0,1,3,4] t12 b13
  have b14 : a 3 ≠ 4 := exclude [0] (fun u v => edge r9 v u) (a 3) (a 2) 4 d2 c9 (by decide +kernel)
  have t14 : a 3 ∈ [0,1] := remove (a 3) 4 [0,1,4] t13 b14
  have b15 : a 6 ≠ 1 := exclude [0] (fun u v => edge r10 v u) (a 6) (a 2) 1 d2 c10 (by decide +kernel)
  have t15 : a 6 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 6) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d6 b15
  exact And.intro t11 (And.intro t14 (t15))

theorem chunk7 (a : Nat → Nat)
    (d6 : a 6 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d2 : a 2 ∈ [0])
    (c10 : edge r10 (a 2) (a 6)=true)
    : a 6 ∈ [0,2,12,14,18,20,23] := by
  have b0 : a 6 ≠ 3 := exclude [0] (fun u v => edge r10 v u) (a 6) (a 2) 3 d2 c10 (by decide +kernel)
  have t0 : a 6 ∈ [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 6) 3 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d6 b0
  have b1 : a 6 ≠ 4 := exclude [0] (fun u v => edge r10 v u) (a 6) (a 2) 4 d2 c10 (by decide +kernel)
  have t1 : a 6 ∈ [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 6) 4 [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 6 ≠ 5 := exclude [0] (fun u v => edge r10 v u) (a 6) (a 2) 5 d2 c10 (by decide +kernel)
  have t2 : a 6 ∈ [0,2,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 6) 5 [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 6 ≠ 6 := exclude [0] (fun u v => edge r10 v u) (a 6) (a 2) 6 d2 c10 (by decide +kernel)
  have t3 : a 6 ∈ [0,2,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 6) 6 [0,2,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 6 ≠ 7 := exclude [0] (fun u v => edge r10 v u) (a 6) (a 2) 7 d2 c10 (by decide +kernel)
  have t4 : a 6 ∈ [0,2,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 6) 7 [0,2,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 6 ≠ 8 := exclude [0] (fun u v => edge r10 v u) (a 6) (a 2) 8 d2 c10 (by decide +kernel)
  have t5 : a 6 ∈ [0,2,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 6) 8 [0,2,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 6 ≠ 9 := exclude [0] (fun u v => edge r10 v u) (a 6) (a 2) 9 d2 c10 (by decide +kernel)
  have t6 : a 6 ∈ [0,2,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 6) 9 [0,2,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 6 ≠ 10 := exclude [0] (fun u v => edge r10 v u) (a 6) (a 2) 10 d2 c10 (by decide +kernel)
  have t7 : a 6 ∈ [0,2,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 6) 10 [0,2,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 6 ≠ 11 := exclude [0] (fun u v => edge r10 v u) (a 6) (a 2) 11 d2 c10 (by decide +kernel)
  have t8 : a 6 ∈ [0,2,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 6) 11 [0,2,11,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 6 ≠ 13 := exclude [0] (fun u v => edge r10 v u) (a 6) (a 2) 13 d2 c10 (by decide +kernel)
  have t9 : a 6 ∈ [0,2,12,14,15,16,17,18,19,20,21,22,23] := remove (a 6) 13 [0,2,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 6 ≠ 15 := exclude [0] (fun u v => edge r10 v u) (a 6) (a 2) 15 d2 c10 (by decide +kernel)
  have t10 : a 6 ∈ [0,2,12,14,16,17,18,19,20,21,22,23] := remove (a 6) 15 [0,2,12,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 6 ≠ 16 := exclude [0] (fun u v => edge r10 v u) (a 6) (a 2) 16 d2 c10 (by decide +kernel)
  have t11 : a 6 ∈ [0,2,12,14,17,18,19,20,21,22,23] := remove (a 6) 16 [0,2,12,14,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 6 ≠ 17 := exclude [0] (fun u v => edge r10 v u) (a 6) (a 2) 17 d2 c10 (by decide +kernel)
  have t12 : a 6 ∈ [0,2,12,14,18,19,20,21,22,23] := remove (a 6) 17 [0,2,12,14,17,18,19,20,21,22,23] t11 b12
  have b13 : a 6 ≠ 19 := exclude [0] (fun u v => edge r10 v u) (a 6) (a 2) 19 d2 c10 (by decide +kernel)
  have t13 : a 6 ∈ [0,2,12,14,18,20,21,22,23] := remove (a 6) 19 [0,2,12,14,18,19,20,21,22,23] t12 b13
  have b14 : a 6 ≠ 21 := exclude [0] (fun u v => edge r10 v u) (a 6) (a 2) 21 d2 c10 (by decide +kernel)
  have t14 : a 6 ∈ [0,2,12,14,18,20,22,23] := remove (a 6) 21 [0,2,12,14,18,20,21,22,23] t13 b14
  have b15 : a 6 ≠ 22 := exclude [0] (fun u v => edge r10 v u) (a 6) (a 2) 22 d2 c10 (by decide +kernel)
  have t15 : a 6 ∈ [0,2,12,14,18,20,23] := remove (a 6) 22 [0,2,12,14,18,20,22,23] t14 b15
  exact t15

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_217
