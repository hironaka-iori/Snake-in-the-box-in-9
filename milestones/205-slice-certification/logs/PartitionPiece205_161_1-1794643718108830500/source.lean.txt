import PartitionData205_161
namespace PartitionCover205_161
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d6 : a 6 ∈ [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19])
    (d2 : a 2 ∈ [0])
    (d10 : a 10 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19])
    (c8 : edge r8 (a 2) (a 6)=true)
    (c9 : edge r9 (a 2) (a 10)=true)
    : a 6 ∈ [0] ∧ a 10 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := by
  have b0 : a 6 ≠ 5 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 5 d2 c8 (by decide +kernel)
  have t0 : a 6 ∈ [0,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 6) 5 [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] d6 b0
  have b1 : a 6 ≠ 6 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 6 d2 c8 (by decide +kernel)
  have t1 : a 6 ∈ [0,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 6) 6 [0,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t0 b1
  have b2 : a 6 ≠ 7 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 7 d2 c8 (by decide +kernel)
  have t2 : a 6 ∈ [0,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 6) 7 [0,7,8,9,10,11,12,13,14,15,16,17,18,19] t1 b2
  have b3 : a 6 ≠ 8 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 8 d2 c8 (by decide +kernel)
  have t3 : a 6 ∈ [0,9,10,11,12,13,14,15,16,17,18,19] := remove (a 6) 8 [0,8,9,10,11,12,13,14,15,16,17,18,19] t2 b3
  have b4 : a 6 ≠ 9 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 9 d2 c8 (by decide +kernel)
  have t4 : a 6 ∈ [0,10,11,12,13,14,15,16,17,18,19] := remove (a 6) 9 [0,9,10,11,12,13,14,15,16,17,18,19] t3 b4
  have b5 : a 6 ≠ 10 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 10 d2 c8 (by decide +kernel)
  have t5 : a 6 ∈ [0,11,12,13,14,15,16,17,18,19] := remove (a 6) 10 [0,10,11,12,13,14,15,16,17,18,19] t4 b5
  have b6 : a 6 ≠ 11 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 11 d2 c8 (by decide +kernel)
  have t6 : a 6 ∈ [0,12,13,14,15,16,17,18,19] := remove (a 6) 11 [0,11,12,13,14,15,16,17,18,19] t5 b6
  have b7 : a 6 ≠ 12 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 12 d2 c8 (by decide +kernel)
  have t7 : a 6 ∈ [0,13,14,15,16,17,18,19] := remove (a 6) 12 [0,12,13,14,15,16,17,18,19] t6 b7
  have b8 : a 6 ≠ 13 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 13 d2 c8 (by decide +kernel)
  have t8 : a 6 ∈ [0,14,15,16,17,18,19] := remove (a 6) 13 [0,13,14,15,16,17,18,19] t7 b8
  have b9 : a 6 ≠ 14 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 14 d2 c8 (by decide +kernel)
  have t9 : a 6 ∈ [0,15,16,17,18,19] := remove (a 6) 14 [0,14,15,16,17,18,19] t8 b9
  have b10 : a 6 ≠ 15 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 15 d2 c8 (by decide +kernel)
  have t10 : a 6 ∈ [0,16,17,18,19] := remove (a 6) 15 [0,15,16,17,18,19] t9 b10
  have b11 : a 6 ≠ 16 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 16 d2 c8 (by decide +kernel)
  have t11 : a 6 ∈ [0,17,18,19] := remove (a 6) 16 [0,16,17,18,19] t10 b11
  have b12 : a 6 ≠ 17 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 17 d2 c8 (by decide +kernel)
  have t12 : a 6 ∈ [0,18,19] := remove (a 6) 17 [0,17,18,19] t11 b12
  have b13 : a 6 ≠ 18 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 18 d2 c8 (by decide +kernel)
  have t13 : a 6 ∈ [0,19] := remove (a 6) 18 [0,18,19] t12 b13
  have b14 : a 6 ≠ 19 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 19 d2 c8 (by decide +kernel)
  have t14 : a 6 ∈ [0] := remove (a 6) 19 [0,19] t13 b14
  have b15 : a 10 ≠ 1 := exclude [0] (fun u v => edge r9 v u) (a 10) (a 2) 1 d2 c9 (by decide +kernel)
  have t15 : a 10 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 10) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] d10 b15
  exact And.intro t14 (t15)

theorem chunk5 (a : Nat → Nat)
    (d10 : a 10 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19])
    (d2 : a 2 ∈ [0])
    (c9 : edge r9 (a 2) (a 10)=true)
    : a 10 ∈ [0,18,19] := by
  have b0 : a 10 ≠ 2 := exclude [0] (fun u v => edge r9 v u) (a 10) (a 2) 2 d2 c9 (by decide +kernel)
  have t0 : a 10 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 10) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] d10 b0
  have b1 : a 10 ≠ 3 := exclude [0] (fun u v => edge r9 v u) (a 10) (a 2) 3 d2 c9 (by decide +kernel)
  have t1 : a 10 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 10) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t0 b1
  have b2 : a 10 ≠ 4 := exclude [0] (fun u v => edge r9 v u) (a 10) (a 2) 4 d2 c9 (by decide +kernel)
  have t2 : a 10 ∈ [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 10) 4 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t1 b2
  have b3 : a 10 ≠ 5 := exclude [0] (fun u v => edge r9 v u) (a 10) (a 2) 5 d2 c9 (by decide +kernel)
  have t3 : a 10 ∈ [0,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 10) 5 [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t2 b3
  have b4 : a 10 ≠ 6 := exclude [0] (fun u v => edge r9 v u) (a 10) (a 2) 6 d2 c9 (by decide +kernel)
  have t4 : a 10 ∈ [0,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 10) 6 [0,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t3 b4
  have b5 : a 10 ≠ 7 := exclude [0] (fun u v => edge r9 v u) (a 10) (a 2) 7 d2 c9 (by decide +kernel)
  have t5 : a 10 ∈ [0,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 10) 7 [0,7,8,9,10,11,12,13,14,15,16,17,18,19] t4 b5
  have b6 : a 10 ≠ 8 := exclude [0] (fun u v => edge r9 v u) (a 10) (a 2) 8 d2 c9 (by decide +kernel)
  have t6 : a 10 ∈ [0,9,10,11,12,13,14,15,16,17,18,19] := remove (a 10) 8 [0,8,9,10,11,12,13,14,15,16,17,18,19] t5 b6
  have b7 : a 10 ≠ 9 := exclude [0] (fun u v => edge r9 v u) (a 10) (a 2) 9 d2 c9 (by decide +kernel)
  have t7 : a 10 ∈ [0,10,11,12,13,14,15,16,17,18,19] := remove (a 10) 9 [0,9,10,11,12,13,14,15,16,17,18,19] t6 b7
  have b8 : a 10 ≠ 10 := exclude [0] (fun u v => edge r9 v u) (a 10) (a 2) 10 d2 c9 (by decide +kernel)
  have t8 : a 10 ∈ [0,11,12,13,14,15,16,17,18,19] := remove (a 10) 10 [0,10,11,12,13,14,15,16,17,18,19] t7 b8
  have b9 : a 10 ≠ 11 := exclude [0] (fun u v => edge r9 v u) (a 10) (a 2) 11 d2 c9 (by decide +kernel)
  have t9 : a 10 ∈ [0,12,13,14,15,16,17,18,19] := remove (a 10) 11 [0,11,12,13,14,15,16,17,18,19] t8 b9
  have b10 : a 10 ≠ 12 := exclude [0] (fun u v => edge r9 v u) (a 10) (a 2) 12 d2 c9 (by decide +kernel)
  have t10 : a 10 ∈ [0,13,14,15,16,17,18,19] := remove (a 10) 12 [0,12,13,14,15,16,17,18,19] t9 b10
  have b11 : a 10 ≠ 13 := exclude [0] (fun u v => edge r9 v u) (a 10) (a 2) 13 d2 c9 (by decide +kernel)
  have t11 : a 10 ∈ [0,14,15,16,17,18,19] := remove (a 10) 13 [0,13,14,15,16,17,18,19] t10 b11
  have b12 : a 10 ≠ 14 := exclude [0] (fun u v => edge r9 v u) (a 10) (a 2) 14 d2 c9 (by decide +kernel)
  have t12 : a 10 ∈ [0,15,16,17,18,19] := remove (a 10) 14 [0,14,15,16,17,18,19] t11 b12
  have b13 : a 10 ≠ 15 := exclude [0] (fun u v => edge r9 v u) (a 10) (a 2) 15 d2 c9 (by decide +kernel)
  have t13 : a 10 ∈ [0,16,17,18,19] := remove (a 10) 15 [0,15,16,17,18,19] t12 b13
  have b14 : a 10 ≠ 16 := exclude [0] (fun u v => edge r9 v u) (a 10) (a 2) 16 d2 c9 (by decide +kernel)
  have t14 : a 10 ∈ [0,17,18,19] := remove (a 10) 16 [0,16,17,18,19] t13 b14
  have b15 : a 10 ≠ 17 := exclude [0] (fun u v => edge r9 v u) (a 10) (a 2) 17 d2 c9 (by decide +kernel)
  have t15 : a 10 ∈ [0,18,19] := remove (a 10) 17 [0,17,18,19] t14 b15
  exact t15

theorem chunk6 (a : Nat → Nat)
    (d10 : a 10 ∈ [0,18,19])
    (d2 : a 2 ∈ [0])
    (d7 : a 7 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19])
    (d3 : a 3 ∈ [0])
    (c9 : edge r9 (a 2) (a 10)=true)
    (c10 : edge r10 (a 3) (a 7)=true)
    : a 10 ∈ [0] ∧ a 7 ∈ [0,15,16,17,18,19] := by
  have b0 : a 10 ≠ 18 := exclude [0] (fun u v => edge r9 v u) (a 10) (a 2) 18 d2 c9 (by decide +kernel)
  have t0 : a 10 ∈ [0,19] := remove (a 10) 18 [0,18,19] d10 b0
  have b1 : a 10 ≠ 19 := exclude [0] (fun u v => edge r9 v u) (a 10) (a 2) 19 d2 c9 (by decide +kernel)
  have t1 : a 10 ∈ [0] := remove (a 10) 19 [0,19] t0 b1
  have b2 : a 7 ≠ 1 := exclude [0] (fun u v => edge r10 v u) (a 7) (a 3) 1 d3 c10 (by decide +kernel)
  have t2 : a 7 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 7) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] d7 b2
  have b3 : a 7 ≠ 2 := exclude [0] (fun u v => edge r10 v u) (a 7) (a 3) 2 d3 c10 (by decide +kernel)
  have t3 : a 7 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 7) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t2 b3
  have b4 : a 7 ≠ 3 := exclude [0] (fun u v => edge r10 v u) (a 7) (a 3) 3 d3 c10 (by decide +kernel)
  have t4 : a 7 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 7) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t3 b4
  have b5 : a 7 ≠ 4 := exclude [0] (fun u v => edge r10 v u) (a 7) (a 3) 4 d3 c10 (by decide +kernel)
  have t5 : a 7 ∈ [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 7) 4 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t4 b5
  have b6 : a 7 ≠ 5 := exclude [0] (fun u v => edge r10 v u) (a 7) (a 3) 5 d3 c10 (by decide +kernel)
  have t6 : a 7 ∈ [0,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 7) 5 [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t5 b6
  have b7 : a 7 ≠ 6 := exclude [0] (fun u v => edge r10 v u) (a 7) (a 3) 6 d3 c10 (by decide +kernel)
  have t7 : a 7 ∈ [0,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 7) 6 [0,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t6 b7
  have b8 : a 7 ≠ 7 := exclude [0] (fun u v => edge r10 v u) (a 7) (a 3) 7 d3 c10 (by decide +kernel)
  have t8 : a 7 ∈ [0,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 7) 7 [0,7,8,9,10,11,12,13,14,15,16,17,18,19] t7 b8
  have b9 : a 7 ≠ 8 := exclude [0] (fun u v => edge r10 v u) (a 7) (a 3) 8 d3 c10 (by decide +kernel)
  have t9 : a 7 ∈ [0,9,10,11,12,13,14,15,16,17,18,19] := remove (a 7) 8 [0,8,9,10,11,12,13,14,15,16,17,18,19] t8 b9
  have b10 : a 7 ≠ 9 := exclude [0] (fun u v => edge r10 v u) (a 7) (a 3) 9 d3 c10 (by decide +kernel)
  have t10 : a 7 ∈ [0,10,11,12,13,14,15,16,17,18,19] := remove (a 7) 9 [0,9,10,11,12,13,14,15,16,17,18,19] t9 b10
  have b11 : a 7 ≠ 10 := exclude [0] (fun u v => edge r10 v u) (a 7) (a 3) 10 d3 c10 (by decide +kernel)
  have t11 : a 7 ∈ [0,11,12,13,14,15,16,17,18,19] := remove (a 7) 10 [0,10,11,12,13,14,15,16,17,18,19] t10 b11
  have b12 : a 7 ≠ 11 := exclude [0] (fun u v => edge r10 v u) (a 7) (a 3) 11 d3 c10 (by decide +kernel)
  have t12 : a 7 ∈ [0,12,13,14,15,16,17,18,19] := remove (a 7) 11 [0,11,12,13,14,15,16,17,18,19] t11 b12
  have b13 : a 7 ≠ 12 := exclude [0] (fun u v => edge r10 v u) (a 7) (a 3) 12 d3 c10 (by decide +kernel)
  have t13 : a 7 ∈ [0,13,14,15,16,17,18,19] := remove (a 7) 12 [0,12,13,14,15,16,17,18,19] t12 b13
  have b14 : a 7 ≠ 13 := exclude [0] (fun u v => edge r10 v u) (a 7) (a 3) 13 d3 c10 (by decide +kernel)
  have t14 : a 7 ∈ [0,14,15,16,17,18,19] := remove (a 7) 13 [0,13,14,15,16,17,18,19] t13 b14
  have b15 : a 7 ≠ 14 := exclude [0] (fun u v => edge r10 v u) (a 7) (a 3) 14 d3 c10 (by decide +kernel)
  have t15 : a 7 ∈ [0,15,16,17,18,19] := remove (a 7) 14 [0,14,15,16,17,18,19] t14 b15
  exact And.intro t1 (t15)

theorem chunk7 (a : Nat → Nat)
    (d7 : a 7 ∈ [0,15,16,17,18,19])
    (d3 : a 3 ∈ [0])
    (d11 : a 11 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19])
    (c10 : edge r10 (a 3) (a 7)=true)
    (c11 : edge r11 (a 3) (a 11)=true)
    : a 7 ∈ [0] ∧ a 11 ∈ [0,12,13,14,15,16,17,18,19] := by
  have b0 : a 7 ≠ 15 := exclude [0] (fun u v => edge r10 v u) (a 7) (a 3) 15 d3 c10 (by decide +kernel)
  have t0 : a 7 ∈ [0,16,17,18,19] := remove (a 7) 15 [0,15,16,17,18,19] d7 b0
  have b1 : a 7 ≠ 16 := exclude [0] (fun u v => edge r10 v u) (a 7) (a 3) 16 d3 c10 (by decide +kernel)
  have t1 : a 7 ∈ [0,17,18,19] := remove (a 7) 16 [0,16,17,18,19] t0 b1
  have b2 : a 7 ≠ 17 := exclude [0] (fun u v => edge r10 v u) (a 7) (a 3) 17 d3 c10 (by decide +kernel)
  have t2 : a 7 ∈ [0,18,19] := remove (a 7) 17 [0,17,18,19] t1 b2
  have b3 : a 7 ≠ 18 := exclude [0] (fun u v => edge r10 v u) (a 7) (a 3) 18 d3 c10 (by decide +kernel)
  have t3 : a 7 ∈ [0,19] := remove (a 7) 18 [0,18,19] t2 b3
  have b4 : a 7 ≠ 19 := exclude [0] (fun u v => edge r10 v u) (a 7) (a 3) 19 d3 c10 (by decide +kernel)
  have t4 : a 7 ∈ [0] := remove (a 7) 19 [0,19] t3 b4
  have b5 : a 11 ≠ 1 := exclude [0] (fun u v => edge r11 v u) (a 11) (a 3) 1 d3 c11 (by decide +kernel)
  have t5 : a 11 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 11) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] d11 b5
  have b6 : a 11 ≠ 2 := exclude [0] (fun u v => edge r11 v u) (a 11) (a 3) 2 d3 c11 (by decide +kernel)
  have t6 : a 11 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 11) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t5 b6
  have b7 : a 11 ≠ 3 := exclude [0] (fun u v => edge r11 v u) (a 11) (a 3) 3 d3 c11 (by decide +kernel)
  have t7 : a 11 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 11) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t6 b7
  have b8 : a 11 ≠ 4 := exclude [0] (fun u v => edge r11 v u) (a 11) (a 3) 4 d3 c11 (by decide +kernel)
  have t8 : a 11 ∈ [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 11) 4 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t7 b8
  have b9 : a 11 ≠ 5 := exclude [0] (fun u v => edge r11 v u) (a 11) (a 3) 5 d3 c11 (by decide +kernel)
  have t9 : a 11 ∈ [0,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 11) 5 [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t8 b9
  have b10 : a 11 ≠ 6 := exclude [0] (fun u v => edge r11 v u) (a 11) (a 3) 6 d3 c11 (by decide +kernel)
  have t10 : a 11 ∈ [0,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 11) 6 [0,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t9 b10
  have b11 : a 11 ≠ 7 := exclude [0] (fun u v => edge r11 v u) (a 11) (a 3) 7 d3 c11 (by decide +kernel)
  have t11 : a 11 ∈ [0,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 11) 7 [0,7,8,9,10,11,12,13,14,15,16,17,18,19] t10 b11
  have b12 : a 11 ≠ 8 := exclude [0] (fun u v => edge r11 v u) (a 11) (a 3) 8 d3 c11 (by decide +kernel)
  have t12 : a 11 ∈ [0,9,10,11,12,13,14,15,16,17,18,19] := remove (a 11) 8 [0,8,9,10,11,12,13,14,15,16,17,18,19] t11 b12
  have b13 : a 11 ≠ 9 := exclude [0] (fun u v => edge r11 v u) (a 11) (a 3) 9 d3 c11 (by decide +kernel)
  have t13 : a 11 ∈ [0,10,11,12,13,14,15,16,17,18,19] := remove (a 11) 9 [0,9,10,11,12,13,14,15,16,17,18,19] t12 b13
  have b14 : a 11 ≠ 10 := exclude [0] (fun u v => edge r11 v u) (a 11) (a 3) 10 d3 c11 (by decide +kernel)
  have t14 : a 11 ∈ [0,11,12,13,14,15,16,17,18,19] := remove (a 11) 10 [0,10,11,12,13,14,15,16,17,18,19] t13 b14
  have b15 : a 11 ≠ 11 := exclude [0] (fun u v => edge r11 v u) (a 11) (a 3) 11 d3 c11 (by decide +kernel)
  have t15 : a 11 ∈ [0,12,13,14,15,16,17,18,19] := remove (a 11) 11 [0,11,12,13,14,15,16,17,18,19] t14 b15
  exact And.intro t4 (t15)

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_161
