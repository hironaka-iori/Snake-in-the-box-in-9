import PartitionData205_153
namespace PartitionCover205_153
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d7 : a 7 ∈ [0,12,26,27,28,29,30,31,34,35,36,37,38,39,40,41,42,43,46,47])
    (d5 : a 5 ∈ [0,12])
    (c15 : edge r15 (a 5) (a 7)=true)
    : a 7 ∈ [0,12,46,47] := by
  have b0 : a 7 ≠ 26 := exclude [0,12] (fun u v => edge r15 v u) (a 7) (a 5) 26 d5 c15 (by decide +kernel)
  have t0 : a 7 ∈ [0,12,27,28,29,30,31,34,35,36,37,38,39,40,41,42,43,46,47] := remove (a 7) 26 [0,12,26,27,28,29,30,31,34,35,36,37,38,39,40,41,42,43,46,47] d7 b0
  have b1 : a 7 ≠ 27 := exclude [0,12] (fun u v => edge r15 v u) (a 7) (a 5) 27 d5 c15 (by decide +kernel)
  have t1 : a 7 ∈ [0,12,28,29,30,31,34,35,36,37,38,39,40,41,42,43,46,47] := remove (a 7) 27 [0,12,27,28,29,30,31,34,35,36,37,38,39,40,41,42,43,46,47] t0 b1
  have b2 : a 7 ≠ 28 := exclude [0,12] (fun u v => edge r15 v u) (a 7) (a 5) 28 d5 c15 (by decide +kernel)
  have t2 : a 7 ∈ [0,12,29,30,31,34,35,36,37,38,39,40,41,42,43,46,47] := remove (a 7) 28 [0,12,28,29,30,31,34,35,36,37,38,39,40,41,42,43,46,47] t1 b2
  have b3 : a 7 ≠ 29 := exclude [0,12] (fun u v => edge r15 v u) (a 7) (a 5) 29 d5 c15 (by decide +kernel)
  have t3 : a 7 ∈ [0,12,30,31,34,35,36,37,38,39,40,41,42,43,46,47] := remove (a 7) 29 [0,12,29,30,31,34,35,36,37,38,39,40,41,42,43,46,47] t2 b3
  have b4 : a 7 ≠ 30 := exclude [0,12] (fun u v => edge r15 v u) (a 7) (a 5) 30 d5 c15 (by decide +kernel)
  have t4 : a 7 ∈ [0,12,31,34,35,36,37,38,39,40,41,42,43,46,47] := remove (a 7) 30 [0,12,30,31,34,35,36,37,38,39,40,41,42,43,46,47] t3 b4
  have b5 : a 7 ≠ 31 := exclude [0,12] (fun u v => edge r15 v u) (a 7) (a 5) 31 d5 c15 (by decide +kernel)
  have t5 : a 7 ∈ [0,12,34,35,36,37,38,39,40,41,42,43,46,47] := remove (a 7) 31 [0,12,31,34,35,36,37,38,39,40,41,42,43,46,47] t4 b5
  have b6 : a 7 ≠ 34 := exclude [0,12] (fun u v => edge r15 v u) (a 7) (a 5) 34 d5 c15 (by decide +kernel)
  have t6 : a 7 ∈ [0,12,35,36,37,38,39,40,41,42,43,46,47] := remove (a 7) 34 [0,12,34,35,36,37,38,39,40,41,42,43,46,47] t5 b6
  have b7 : a 7 ≠ 35 := exclude [0,12] (fun u v => edge r15 v u) (a 7) (a 5) 35 d5 c15 (by decide +kernel)
  have t7 : a 7 ∈ [0,12,36,37,38,39,40,41,42,43,46,47] := remove (a 7) 35 [0,12,35,36,37,38,39,40,41,42,43,46,47] t6 b7
  have b8 : a 7 ≠ 36 := exclude [0,12] (fun u v => edge r15 v u) (a 7) (a 5) 36 d5 c15 (by decide +kernel)
  have t8 : a 7 ∈ [0,12,37,38,39,40,41,42,43,46,47] := remove (a 7) 36 [0,12,36,37,38,39,40,41,42,43,46,47] t7 b8
  have b9 : a 7 ≠ 37 := exclude [0,12] (fun u v => edge r15 v u) (a 7) (a 5) 37 d5 c15 (by decide +kernel)
  have t9 : a 7 ∈ [0,12,38,39,40,41,42,43,46,47] := remove (a 7) 37 [0,12,37,38,39,40,41,42,43,46,47] t8 b9
  have b10 : a 7 ≠ 38 := exclude [0,12] (fun u v => edge r15 v u) (a 7) (a 5) 38 d5 c15 (by decide +kernel)
  have t10 : a 7 ∈ [0,12,39,40,41,42,43,46,47] := remove (a 7) 38 [0,12,38,39,40,41,42,43,46,47] t9 b10
  have b11 : a 7 ≠ 39 := exclude [0,12] (fun u v => edge r15 v u) (a 7) (a 5) 39 d5 c15 (by decide +kernel)
  have t11 : a 7 ∈ [0,12,40,41,42,43,46,47] := remove (a 7) 39 [0,12,39,40,41,42,43,46,47] t10 b11
  have b12 : a 7 ≠ 40 := exclude [0,12] (fun u v => edge r15 v u) (a 7) (a 5) 40 d5 c15 (by decide +kernel)
  have t12 : a 7 ∈ [0,12,41,42,43,46,47] := remove (a 7) 40 [0,12,40,41,42,43,46,47] t11 b12
  have b13 : a 7 ≠ 41 := exclude [0,12] (fun u v => edge r15 v u) (a 7) (a 5) 41 d5 c15 (by decide +kernel)
  have t13 : a 7 ∈ [0,12,42,43,46,47] := remove (a 7) 41 [0,12,41,42,43,46,47] t12 b13
  have b14 : a 7 ≠ 42 := exclude [0,12] (fun u v => edge r15 v u) (a 7) (a 5) 42 d5 c15 (by decide +kernel)
  have t14 : a 7 ∈ [0,12,43,46,47] := remove (a 7) 42 [0,12,42,43,46,47] t13 b14
  have b15 : a 7 ≠ 43 := exclude [0,12] (fun u v => edge r15 v u) (a 7) (a 5) 43 d5 c15 (by decide +kernel)
  have t15 : a 7 ∈ [0,12,46,47] := remove (a 7) 43 [0,12,43,46,47] t14 b15
  exact t15

theorem chunk9 (a : Nat → Nat)
    (d7 : a 7 ∈ [0,12,46,47])
    (d5 : a 5 ∈ [0,12])
    (d13 : a 13 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27])
    (c15 : edge r15 (a 5) (a 7)=true)
    (c16 : edge r16 (a 5) (a 13)=true)
    : a 7 ∈ [0,12] ∧ a 13 ∈ [0,1,16,17,18,19,20,21,22,23,24,25,26,27] := by
  have b0 : a 7 ≠ 46 := exclude [0,12] (fun u v => edge r15 v u) (a 7) (a 5) 46 d5 c15 (by decide +kernel)
  have t0 : a 7 ∈ [0,12,47] := remove (a 7) 46 [0,12,46,47] d7 b0
  have b1 : a 7 ≠ 47 := exclude [0,12] (fun u v => edge r15 v u) (a 7) (a 5) 47 d5 c15 (by decide +kernel)
  have t1 : a 7 ∈ [0,12] := remove (a 7) 47 [0,12,47] t0 b1
  have b2 : a 13 ≠ 2 := exclude [0,12] (fun u v => edge r16 v u) (a 13) (a 5) 2 d5 c16 (by decide +kernel)
  have t2 : a 13 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 13) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] d13 b2
  have b3 : a 13 ≠ 3 := exclude [0,12] (fun u v => edge r16 v u) (a 13) (a 5) 3 d5 c16 (by decide +kernel)
  have t3 : a 13 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 13) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] t2 b3
  have b4 : a 13 ≠ 4 := exclude [0,12] (fun u v => edge r16 v u) (a 13) (a 5) 4 d5 c16 (by decide +kernel)
  have t4 : a 13 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 13) 4 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] t3 b4
  have b5 : a 13 ≠ 5 := exclude [0,12] (fun u v => edge r16 v u) (a 13) (a 5) 5 d5 c16 (by decide +kernel)
  have t5 : a 13 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 13) 5 [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] t4 b5
  have b6 : a 13 ≠ 6 := exclude [0,12] (fun u v => edge r16 v u) (a 13) (a 5) 6 d5 c16 (by decide +kernel)
  have t6 : a 13 ∈ [0,1,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 13) 6 [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] t5 b6
  have b7 : a 13 ≠ 7 := exclude [0,12] (fun u v => edge r16 v u) (a 13) (a 5) 7 d5 c16 (by decide +kernel)
  have t7 : a 13 ∈ [0,1,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 13) 7 [0,1,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] t6 b7
  have b8 : a 13 ≠ 8 := exclude [0,12] (fun u v => edge r16 v u) (a 13) (a 5) 8 d5 c16 (by decide +kernel)
  have t8 : a 13 ∈ [0,1,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 13) 8 [0,1,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] t7 b8
  have b9 : a 13 ≠ 9 := exclude [0,12] (fun u v => edge r16 v u) (a 13) (a 5) 9 d5 c16 (by decide +kernel)
  have t9 : a 13 ∈ [0,1,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 13) 9 [0,1,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] t8 b9
  have b10 : a 13 ≠ 10 := exclude [0,12] (fun u v => edge r16 v u) (a 13) (a 5) 10 d5 c16 (by decide +kernel)
  have t10 : a 13 ∈ [0,1,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 13) 10 [0,1,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] t9 b10
  have b11 : a 13 ≠ 11 := exclude [0,12] (fun u v => edge r16 v u) (a 13) (a 5) 11 d5 c16 (by decide +kernel)
  have t11 : a 13 ∈ [0,1,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 13) 11 [0,1,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] t10 b11
  have b12 : a 13 ≠ 12 := exclude [0,12] (fun u v => edge r16 v u) (a 13) (a 5) 12 d5 c16 (by decide +kernel)
  have t12 : a 13 ∈ [0,1,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 13) 12 [0,1,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] t11 b12
  have b13 : a 13 ≠ 13 := exclude [0,12] (fun u v => edge r16 v u) (a 13) (a 5) 13 d5 c16 (by decide +kernel)
  have t13 : a 13 ∈ [0,1,14,15,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 13) 13 [0,1,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] t12 b13
  have b14 : a 13 ≠ 14 := exclude [0,12] (fun u v => edge r16 v u) (a 13) (a 5) 14 d5 c16 (by decide +kernel)
  have t14 : a 13 ∈ [0,1,15,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 13) 14 [0,1,14,15,16,17,18,19,20,21,22,23,24,25,26,27] t13 b14
  have b15 : a 13 ≠ 15 := exclude [0,12] (fun u v => edge r16 v u) (a 13) (a 5) 15 d5 c16 (by decide +kernel)
  have t15 : a 13 ∈ [0,1,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 13) 15 [0,1,15,16,17,18,19,20,21,22,23,24,25,26,27] t14 b15
  exact And.intro t1 (t15)

theorem chunk10 (a : Nat → Nat)
    (d13 : a 13 ∈ [0,1,16,17,18,19,20,21,22,23,24,25,26,27])
    (d5 : a 5 ∈ [0,12])
    (d14 : a 14 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d6 : a 6 ∈ [0,1])
    (c16 : edge r16 (a 5) (a 13)=true)
    (c18 : edge r18 (a 6) (a 14)=true)
    : a 13 ∈ [0,1] ∧ a 14 ∈ [0,1,3,4,6,7,9,10] := by
  have b0 : a 13 ≠ 16 := exclude [0,12] (fun u v => edge r16 v u) (a 13) (a 5) 16 d5 c16 (by decide +kernel)
  have t0 : a 13 ∈ [0,1,17,18,19,20,21,22,23,24,25,26,27] := remove (a 13) 16 [0,1,16,17,18,19,20,21,22,23,24,25,26,27] d13 b0
  have b1 : a 13 ≠ 17 := exclude [0,12] (fun u v => edge r16 v u) (a 13) (a 5) 17 d5 c16 (by decide +kernel)
  have t1 : a 13 ∈ [0,1,18,19,20,21,22,23,24,25,26,27] := remove (a 13) 17 [0,1,17,18,19,20,21,22,23,24,25,26,27] t0 b1
  have b2 : a 13 ≠ 18 := exclude [0,12] (fun u v => edge r16 v u) (a 13) (a 5) 18 d5 c16 (by decide +kernel)
  have t2 : a 13 ∈ [0,1,19,20,21,22,23,24,25,26,27] := remove (a 13) 18 [0,1,18,19,20,21,22,23,24,25,26,27] t1 b2
  have b3 : a 13 ≠ 19 := exclude [0,12] (fun u v => edge r16 v u) (a 13) (a 5) 19 d5 c16 (by decide +kernel)
  have t3 : a 13 ∈ [0,1,20,21,22,23,24,25,26,27] := remove (a 13) 19 [0,1,19,20,21,22,23,24,25,26,27] t2 b3
  have b4 : a 13 ≠ 20 := exclude [0,12] (fun u v => edge r16 v u) (a 13) (a 5) 20 d5 c16 (by decide +kernel)
  have t4 : a 13 ∈ [0,1,21,22,23,24,25,26,27] := remove (a 13) 20 [0,1,20,21,22,23,24,25,26,27] t3 b4
  have b5 : a 13 ≠ 21 := exclude [0,12] (fun u v => edge r16 v u) (a 13) (a 5) 21 d5 c16 (by decide +kernel)
  have t5 : a 13 ∈ [0,1,22,23,24,25,26,27] := remove (a 13) 21 [0,1,21,22,23,24,25,26,27] t4 b5
  have b6 : a 13 ≠ 22 := exclude [0,12] (fun u v => edge r16 v u) (a 13) (a 5) 22 d5 c16 (by decide +kernel)
  have t6 : a 13 ∈ [0,1,23,24,25,26,27] := remove (a 13) 22 [0,1,22,23,24,25,26,27] t5 b6
  have b7 : a 13 ≠ 23 := exclude [0,12] (fun u v => edge r16 v u) (a 13) (a 5) 23 d5 c16 (by decide +kernel)
  have t7 : a 13 ∈ [0,1,24,25,26,27] := remove (a 13) 23 [0,1,23,24,25,26,27] t6 b7
  have b8 : a 13 ≠ 24 := exclude [0,12] (fun u v => edge r16 v u) (a 13) (a 5) 24 d5 c16 (by decide +kernel)
  have t8 : a 13 ∈ [0,1,25,26,27] := remove (a 13) 24 [0,1,24,25,26,27] t7 b8
  have b9 : a 13 ≠ 25 := exclude [0,12] (fun u v => edge r16 v u) (a 13) (a 5) 25 d5 c16 (by decide +kernel)
  have t9 : a 13 ∈ [0,1,26,27] := remove (a 13) 25 [0,1,25,26,27] t8 b9
  have b10 : a 13 ≠ 26 := exclude [0,12] (fun u v => edge r16 v u) (a 13) (a 5) 26 d5 c16 (by decide +kernel)
  have t10 : a 13 ∈ [0,1,27] := remove (a 13) 26 [0,1,26,27] t9 b10
  have b11 : a 13 ≠ 27 := exclude [0,12] (fun u v => edge r16 v u) (a 13) (a 5) 27 d5 c16 (by decide +kernel)
  have t11 : a 13 ∈ [0,1] := remove (a 13) 27 [0,1,27] t10 b11
  have b12 : a 14 ≠ 2 := exclude [0,1] (fun u v => edge r18 v u) (a 14) (a 6) 2 d6 c18 (by decide +kernel)
  have t12 : a 14 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 14) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d14 b12
  have b13 : a 14 ≠ 5 := exclude [0,1] (fun u v => edge r18 v u) (a 14) (a 6) 5 d6 c18 (by decide +kernel)
  have t13 : a 14 ∈ [0,1,3,4,6,7,8,9,10,11] := remove (a 14) 5 [0,1,3,4,5,6,7,8,9,10,11] t12 b13
  have b14 : a 14 ≠ 8 := exclude [0,1] (fun u v => edge r18 v u) (a 14) (a 6) 8 d6 c18 (by decide +kernel)
  have t14 : a 14 ∈ [0,1,3,4,6,7,9,10,11] := remove (a 14) 8 [0,1,3,4,6,7,8,9,10,11] t13 b14
  have b15 : a 14 ≠ 11 := exclude [0,1] (fun u v => edge r18 v u) (a 14) (a 6) 11 d6 c18 (by decide +kernel)
  have t15 : a 14 ∈ [0,1,3,4,6,7,9,10] := remove (a 14) 11 [0,1,3,4,6,7,9,10,11] t14 b15
  exact And.intro t11 (t15)

theorem chunk11 (a : Nat → Nat)
    (d15 : a 15 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27])
    (d7 : a 7 ∈ [0,12])
    (c19 : edge r19 (a 7) (a 15)=true)
    : a 15 ∈ [0,1,18,19,20,21,22,23,24,25,26,27] := by
  have b0 : a 15 ≠ 2 := exclude [0,12] (fun u v => edge r19 v u) (a 15) (a 7) 2 d7 c19 (by decide +kernel)
  have t0 : a 15 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 15) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] d15 b0
  have b1 : a 15 ≠ 3 := exclude [0,12] (fun u v => edge r19 v u) (a 15) (a 7) 3 d7 c19 (by decide +kernel)
  have t1 : a 15 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 15) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] t0 b1
  have b2 : a 15 ≠ 4 := exclude [0,12] (fun u v => edge r19 v u) (a 15) (a 7) 4 d7 c19 (by decide +kernel)
  have t2 : a 15 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 15) 4 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] t1 b2
  have b3 : a 15 ≠ 5 := exclude [0,12] (fun u v => edge r19 v u) (a 15) (a 7) 5 d7 c19 (by decide +kernel)
  have t3 : a 15 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 15) 5 [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] t2 b3
  have b4 : a 15 ≠ 6 := exclude [0,12] (fun u v => edge r19 v u) (a 15) (a 7) 6 d7 c19 (by decide +kernel)
  have t4 : a 15 ∈ [0,1,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 15) 6 [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] t3 b4
  have b5 : a 15 ≠ 7 := exclude [0,12] (fun u v => edge r19 v u) (a 15) (a 7) 7 d7 c19 (by decide +kernel)
  have t5 : a 15 ∈ [0,1,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 15) 7 [0,1,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] t4 b5
  have b6 : a 15 ≠ 8 := exclude [0,12] (fun u v => edge r19 v u) (a 15) (a 7) 8 d7 c19 (by decide +kernel)
  have t6 : a 15 ∈ [0,1,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 15) 8 [0,1,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] t5 b6
  have b7 : a 15 ≠ 9 := exclude [0,12] (fun u v => edge r19 v u) (a 15) (a 7) 9 d7 c19 (by decide +kernel)
  have t7 : a 15 ∈ [0,1,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 15) 9 [0,1,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] t6 b7
  have b8 : a 15 ≠ 10 := exclude [0,12] (fun u v => edge r19 v u) (a 15) (a 7) 10 d7 c19 (by decide +kernel)
  have t8 : a 15 ∈ [0,1,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 15) 10 [0,1,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] t7 b8
  have b9 : a 15 ≠ 11 := exclude [0,12] (fun u v => edge r19 v u) (a 15) (a 7) 11 d7 c19 (by decide +kernel)
  have t9 : a 15 ∈ [0,1,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 15) 11 [0,1,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] t8 b9
  have b10 : a 15 ≠ 12 := exclude [0,12] (fun u v => edge r19 v u) (a 15) (a 7) 12 d7 c19 (by decide +kernel)
  have t10 : a 15 ∈ [0,1,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 15) 12 [0,1,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] t9 b10
  have b11 : a 15 ≠ 13 := exclude [0,12] (fun u v => edge r19 v u) (a 15) (a 7) 13 d7 c19 (by decide +kernel)
  have t11 : a 15 ∈ [0,1,14,15,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 15) 13 [0,1,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] t10 b11
  have b12 : a 15 ≠ 14 := exclude [0,12] (fun u v => edge r19 v u) (a 15) (a 7) 14 d7 c19 (by decide +kernel)
  have t12 : a 15 ∈ [0,1,15,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 15) 14 [0,1,14,15,16,17,18,19,20,21,22,23,24,25,26,27] t11 b12
  have b13 : a 15 ≠ 15 := exclude [0,12] (fun u v => edge r19 v u) (a 15) (a 7) 15 d7 c19 (by decide +kernel)
  have t13 : a 15 ∈ [0,1,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 15) 15 [0,1,15,16,17,18,19,20,21,22,23,24,25,26,27] t12 b13
  have b14 : a 15 ≠ 16 := exclude [0,12] (fun u v => edge r19 v u) (a 15) (a 7) 16 d7 c19 (by decide +kernel)
  have t14 : a 15 ∈ [0,1,17,18,19,20,21,22,23,24,25,26,27] := remove (a 15) 16 [0,1,16,17,18,19,20,21,22,23,24,25,26,27] t13 b14
  have b15 : a 15 ≠ 17 := exclude [0,12] (fun u v => edge r19 v u) (a 15) (a 7) 17 d7 c19 (by decide +kernel)
  have t15 : a 15 ∈ [0,1,18,19,20,21,22,23,24,25,26,27] := remove (a 15) 17 [0,1,17,18,19,20,21,22,23,24,25,26,27] t14 b15
  exact t15

#print axioms chunk8
#print axioms chunk9
#print axioms chunk10
#print axioms chunk11
end PartitionCover205_153
