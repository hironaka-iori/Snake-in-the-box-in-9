import PartitionData205_150
namespace PartitionCover205_150
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d6 : a 6 ∈ [0,1,6,7,8,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41])
    (d4 : a 4 ∈ [0,2])
    (c13 : edge r13 (a 4) (a 6)=true)
    : a 6 ∈ [0,1,6,7,8,29,30,31,32,33,34,35,36,37,38,39,40,41] := by
  have b0 : a 6 ≠ 13 := exclude [0,2] (fun u v => edge r13 v u) (a 6) (a 4) 13 d4 c13 (by decide +kernel)
  have t0 : a 6 ∈ [0,1,6,7,8,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41] := remove (a 6) 13 [0,1,6,7,8,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41] d6 b0
  have b1 : a 6 ≠ 14 := exclude [0,2] (fun u v => edge r13 v u) (a 6) (a 4) 14 d4 c13 (by decide +kernel)
  have t1 : a 6 ∈ [0,1,6,7,8,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41] := remove (a 6) 14 [0,1,6,7,8,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41] t0 b1
  have b2 : a 6 ≠ 15 := exclude [0,2] (fun u v => edge r13 v u) (a 6) (a 4) 15 d4 c13 (by decide +kernel)
  have t2 : a 6 ∈ [0,1,6,7,8,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41] := remove (a 6) 15 [0,1,6,7,8,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41] t1 b2
  have b3 : a 6 ≠ 16 := exclude [0,2] (fun u v => edge r13 v u) (a 6) (a 4) 16 d4 c13 (by decide +kernel)
  have t3 : a 6 ∈ [0,1,6,7,8,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41] := remove (a 6) 16 [0,1,6,7,8,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41] t2 b3
  have b4 : a 6 ≠ 17 := exclude [0,2] (fun u v => edge r13 v u) (a 6) (a 4) 17 d4 c13 (by decide +kernel)
  have t4 : a 6 ∈ [0,1,6,7,8,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41] := remove (a 6) 17 [0,1,6,7,8,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41] t3 b4
  have b5 : a 6 ≠ 18 := exclude [0,2] (fun u v => edge r13 v u) (a 6) (a 4) 18 d4 c13 (by decide +kernel)
  have t5 : a 6 ∈ [0,1,6,7,8,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41] := remove (a 6) 18 [0,1,6,7,8,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41] t4 b5
  have b6 : a 6 ≠ 19 := exclude [0,2] (fun u v => edge r13 v u) (a 6) (a 4) 19 d4 c13 (by decide +kernel)
  have t6 : a 6 ∈ [0,1,6,7,8,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41] := remove (a 6) 19 [0,1,6,7,8,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41] t5 b6
  have b7 : a 6 ≠ 20 := exclude [0,2] (fun u v => edge r13 v u) (a 6) (a 4) 20 d4 c13 (by decide +kernel)
  have t7 : a 6 ∈ [0,1,6,7,8,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41] := remove (a 6) 20 [0,1,6,7,8,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41] t6 b7
  have b8 : a 6 ≠ 21 := exclude [0,2] (fun u v => edge r13 v u) (a 6) (a 4) 21 d4 c13 (by decide +kernel)
  have t8 : a 6 ∈ [0,1,6,7,8,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41] := remove (a 6) 21 [0,1,6,7,8,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41] t7 b8
  have b9 : a 6 ≠ 22 := exclude [0,2] (fun u v => edge r13 v u) (a 6) (a 4) 22 d4 c13 (by decide +kernel)
  have t9 : a 6 ∈ [0,1,6,7,8,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41] := remove (a 6) 22 [0,1,6,7,8,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41] t8 b9
  have b10 : a 6 ≠ 23 := exclude [0,2] (fun u v => edge r13 v u) (a 6) (a 4) 23 d4 c13 (by decide +kernel)
  have t10 : a 6 ∈ [0,1,6,7,8,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41] := remove (a 6) 23 [0,1,6,7,8,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41] t9 b10
  have b11 : a 6 ≠ 24 := exclude [0,2] (fun u v => edge r13 v u) (a 6) (a 4) 24 d4 c13 (by decide +kernel)
  have t11 : a 6 ∈ [0,1,6,7,8,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41] := remove (a 6) 24 [0,1,6,7,8,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41] t10 b11
  have b12 : a 6 ≠ 25 := exclude [0,2] (fun u v => edge r13 v u) (a 6) (a 4) 25 d4 c13 (by decide +kernel)
  have t12 : a 6 ∈ [0,1,6,7,8,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41] := remove (a 6) 25 [0,1,6,7,8,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41] t11 b12
  have b13 : a 6 ≠ 26 := exclude [0,2] (fun u v => edge r13 v u) (a 6) (a 4) 26 d4 c13 (by decide +kernel)
  have t13 : a 6 ∈ [0,1,6,7,8,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41] := remove (a 6) 26 [0,1,6,7,8,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41] t12 b13
  have b14 : a 6 ≠ 27 := exclude [0,2] (fun u v => edge r13 v u) (a 6) (a 4) 27 d4 c13 (by decide +kernel)
  have t14 : a 6 ∈ [0,1,6,7,8,28,29,30,31,32,33,34,35,36,37,38,39,40,41] := remove (a 6) 27 [0,1,6,7,8,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41] t13 b14
  have b15 : a 6 ≠ 28 := exclude [0,2] (fun u v => edge r13 v u) (a 6) (a 4) 28 d4 c13 (by decide +kernel)
  have t15 : a 6 ∈ [0,1,6,7,8,29,30,31,32,33,34,35,36,37,38,39,40,41] := remove (a 6) 28 [0,1,6,7,8,28,29,30,31,32,33,34,35,36,37,38,39,40,41] t14 b15
  exact t15

theorem chunk5 (a : Nat → Nat)
    (d6 : a 6 ∈ [0,1,6,7,8,29,30,31,32,33,34,35,36,37,38,39,40,41])
    (d4 : a 4 ∈ [0,2])
    (d12 : a 12 ∈ [0,1,2,3,4,5])
    (c13 : edge r13 (a 4) (a 6)=true)
    (c14 : edge r14 (a 4) (a 12)=true)
    : a 6 ∈ [0,1,6,7,8] ∧ a 4 ∈ [0] ∧ a 12 ∈ [0,3,4,5] := by
  have b0 : a 6 ≠ 29 := exclude [0,2] (fun u v => edge r13 v u) (a 6) (a 4) 29 d4 c13 (by decide +kernel)
  have t0 : a 6 ∈ [0,1,6,7,8,30,31,32,33,34,35,36,37,38,39,40,41] := remove (a 6) 29 [0,1,6,7,8,29,30,31,32,33,34,35,36,37,38,39,40,41] d6 b0
  have b1 : a 6 ≠ 30 := exclude [0,2] (fun u v => edge r13 v u) (a 6) (a 4) 30 d4 c13 (by decide +kernel)
  have t1 : a 6 ∈ [0,1,6,7,8,31,32,33,34,35,36,37,38,39,40,41] := remove (a 6) 30 [0,1,6,7,8,30,31,32,33,34,35,36,37,38,39,40,41] t0 b1
  have b2 : a 6 ≠ 31 := exclude [0,2] (fun u v => edge r13 v u) (a 6) (a 4) 31 d4 c13 (by decide +kernel)
  have t2 : a 6 ∈ [0,1,6,7,8,32,33,34,35,36,37,38,39,40,41] := remove (a 6) 31 [0,1,6,7,8,31,32,33,34,35,36,37,38,39,40,41] t1 b2
  have b3 : a 6 ≠ 32 := exclude [0,2] (fun u v => edge r13 v u) (a 6) (a 4) 32 d4 c13 (by decide +kernel)
  have t3 : a 6 ∈ [0,1,6,7,8,33,34,35,36,37,38,39,40,41] := remove (a 6) 32 [0,1,6,7,8,32,33,34,35,36,37,38,39,40,41] t2 b3
  have b4 : a 6 ≠ 33 := exclude [0,2] (fun u v => edge r13 v u) (a 6) (a 4) 33 d4 c13 (by decide +kernel)
  have t4 : a 6 ∈ [0,1,6,7,8,34,35,36,37,38,39,40,41] := remove (a 6) 33 [0,1,6,7,8,33,34,35,36,37,38,39,40,41] t3 b4
  have b5 : a 6 ≠ 34 := exclude [0,2] (fun u v => edge r13 v u) (a 6) (a 4) 34 d4 c13 (by decide +kernel)
  have t5 : a 6 ∈ [0,1,6,7,8,35,36,37,38,39,40,41] := remove (a 6) 34 [0,1,6,7,8,34,35,36,37,38,39,40,41] t4 b5
  have b6 : a 6 ≠ 35 := exclude [0,2] (fun u v => edge r13 v u) (a 6) (a 4) 35 d4 c13 (by decide +kernel)
  have t6 : a 6 ∈ [0,1,6,7,8,36,37,38,39,40,41] := remove (a 6) 35 [0,1,6,7,8,35,36,37,38,39,40,41] t5 b6
  have b7 : a 6 ≠ 36 := exclude [0,2] (fun u v => edge r13 v u) (a 6) (a 4) 36 d4 c13 (by decide +kernel)
  have t7 : a 6 ∈ [0,1,6,7,8,37,38,39,40,41] := remove (a 6) 36 [0,1,6,7,8,36,37,38,39,40,41] t6 b7
  have b8 : a 6 ≠ 37 := exclude [0,2] (fun u v => edge r13 v u) (a 6) (a 4) 37 d4 c13 (by decide +kernel)
  have t8 : a 6 ∈ [0,1,6,7,8,38,39,40,41] := remove (a 6) 37 [0,1,6,7,8,37,38,39,40,41] t7 b8
  have b9 : a 6 ≠ 38 := exclude [0,2] (fun u v => edge r13 v u) (a 6) (a 4) 38 d4 c13 (by decide +kernel)
  have t9 : a 6 ∈ [0,1,6,7,8,39,40,41] := remove (a 6) 38 [0,1,6,7,8,38,39,40,41] t8 b9
  have b10 : a 6 ≠ 39 := exclude [0,2] (fun u v => edge r13 v u) (a 6) (a 4) 39 d4 c13 (by decide +kernel)
  have t10 : a 6 ∈ [0,1,6,7,8,40,41] := remove (a 6) 39 [0,1,6,7,8,39,40,41] t9 b10
  have b11 : a 6 ≠ 40 := exclude [0,2] (fun u v => edge r13 v u) (a 6) (a 4) 40 d4 c13 (by decide +kernel)
  have t11 : a 6 ∈ [0,1,6,7,8,41] := remove (a 6) 40 [0,1,6,7,8,40,41] t10 b11
  have b12 : a 6 ≠ 41 := exclude [0,2] (fun u v => edge r13 v u) (a 6) (a 4) 41 d4 c13 (by decide +kernel)
  have t12 : a 6 ∈ [0,1,6,7,8] := remove (a 6) 41 [0,1,6,7,8,41] t11 b12
  have b13 : a 4 ≠ 2 := exclude [0,1,2,3,4,5] (edge r14) (a 4) (a 12) 2 d12 c14 (by decide +kernel)
  have t13 : a 4 ∈ [0] := remove (a 4) 2 [0,2] d4 b13
  have b14 : a 12 ≠ 1 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 1 t13 c14 (by decide +kernel)
  have t14 : a 12 ∈ [0,2,3,4,5] := remove (a 12) 1 [0,1,2,3,4,5] d12 b14
  have b15 : a 12 ≠ 2 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 2 t13 c14 (by decide +kernel)
  have t15 : a 12 ∈ [0,3,4,5] := remove (a 12) 2 [0,2,3,4,5] t14 b15
  exact And.intro t12 (And.intro t13 (t15))

theorem chunk6 (a : Nat → Nat)
    (d12 : a 12 ∈ [0,3,4,5])
    (d4 : a 4 ∈ [0])
    (d5 : a 5 ∈ [0,1,26,27])
    (d7 : a 7 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,18,19,20,21,22,23,30,31,32,33,34,35])
    (c14 : edge r14 (a 4) (a 12)=true)
    (c15 : edge r15 (a 5) (a 7)=true)
    : a 12 ∈ [0] ∧ a 5 ∈ [0] ∧ a 7 ∈ [0,11,18,19,20,21,22,23,30,31,32,33,34,35] := by
  have b0 : a 12 ≠ 3 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 3 d4 c14 (by decide +kernel)
  have t0 : a 12 ∈ [0,4,5] := remove (a 12) 3 [0,3,4,5] d12 b0
  have b1 : a 12 ≠ 4 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 4 d4 c14 (by decide +kernel)
  have t1 : a 12 ∈ [0,5] := remove (a 12) 4 [0,4,5] t0 b1
  have b2 : a 12 ≠ 5 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 5 d4 c14 (by decide +kernel)
  have t2 : a 12 ∈ [0] := remove (a 12) 5 [0,5] t1 b2
  have b3 : a 5 ≠ 1 := exclude [0,1,2,3,4,5,6,7,8,9,10,11,18,19,20,21,22,23,30,31,32,33,34,35] (edge r15) (a 5) (a 7) 1 d7 c15 (by decide +kernel)
  have t3 : a 5 ∈ [0,26,27] := remove (a 5) 1 [0,1,26,27] d5 b3
  have b4 : a 5 ≠ 26 := exclude [0,1,2,3,4,5,6,7,8,9,10,11,18,19,20,21,22,23,30,31,32,33,34,35] (edge r15) (a 5) (a 7) 26 d7 c15 (by decide +kernel)
  have t4 : a 5 ∈ [0,27] := remove (a 5) 26 [0,26,27] t3 b4
  have b5 : a 5 ≠ 27 := exclude [0,1,2,3,4,5,6,7,8,9,10,11,18,19,20,21,22,23,30,31,32,33,34,35] (edge r15) (a 5) (a 7) 27 d7 c15 (by decide +kernel)
  have t5 : a 5 ∈ [0] := remove (a 5) 27 [0,27] t4 b5
  have b6 : a 7 ≠ 1 := exclude [0] (fun u v => edge r15 v u) (a 7) (a 5) 1 t5 c15 (by decide +kernel)
  have t6 : a 7 ∈ [0,2,3,4,5,6,7,8,9,10,11,18,19,20,21,22,23,30,31,32,33,34,35] := remove (a 7) 1 [0,1,2,3,4,5,6,7,8,9,10,11,18,19,20,21,22,23,30,31,32,33,34,35] d7 b6
  have b7 : a 7 ≠ 2 := exclude [0] (fun u v => edge r15 v u) (a 7) (a 5) 2 t5 c15 (by decide +kernel)
  have t7 : a 7 ∈ [0,3,4,5,6,7,8,9,10,11,18,19,20,21,22,23,30,31,32,33,34,35] := remove (a 7) 2 [0,2,3,4,5,6,7,8,9,10,11,18,19,20,21,22,23,30,31,32,33,34,35] t6 b7
  have b8 : a 7 ≠ 3 := exclude [0] (fun u v => edge r15 v u) (a 7) (a 5) 3 t5 c15 (by decide +kernel)
  have t8 : a 7 ∈ [0,4,5,6,7,8,9,10,11,18,19,20,21,22,23,30,31,32,33,34,35] := remove (a 7) 3 [0,3,4,5,6,7,8,9,10,11,18,19,20,21,22,23,30,31,32,33,34,35] t7 b8
  have b9 : a 7 ≠ 4 := exclude [0] (fun u v => edge r15 v u) (a 7) (a 5) 4 t5 c15 (by decide +kernel)
  have t9 : a 7 ∈ [0,5,6,7,8,9,10,11,18,19,20,21,22,23,30,31,32,33,34,35] := remove (a 7) 4 [0,4,5,6,7,8,9,10,11,18,19,20,21,22,23,30,31,32,33,34,35] t8 b9
  have b10 : a 7 ≠ 5 := exclude [0] (fun u v => edge r15 v u) (a 7) (a 5) 5 t5 c15 (by decide +kernel)
  have t10 : a 7 ∈ [0,6,7,8,9,10,11,18,19,20,21,22,23,30,31,32,33,34,35] := remove (a 7) 5 [0,5,6,7,8,9,10,11,18,19,20,21,22,23,30,31,32,33,34,35] t9 b10
  have b11 : a 7 ≠ 6 := exclude [0] (fun u v => edge r15 v u) (a 7) (a 5) 6 t5 c15 (by decide +kernel)
  have t11 : a 7 ∈ [0,7,8,9,10,11,18,19,20,21,22,23,30,31,32,33,34,35] := remove (a 7) 6 [0,6,7,8,9,10,11,18,19,20,21,22,23,30,31,32,33,34,35] t10 b11
  have b12 : a 7 ≠ 7 := exclude [0] (fun u v => edge r15 v u) (a 7) (a 5) 7 t5 c15 (by decide +kernel)
  have t12 : a 7 ∈ [0,8,9,10,11,18,19,20,21,22,23,30,31,32,33,34,35] := remove (a 7) 7 [0,7,8,9,10,11,18,19,20,21,22,23,30,31,32,33,34,35] t11 b12
  have b13 : a 7 ≠ 8 := exclude [0] (fun u v => edge r15 v u) (a 7) (a 5) 8 t5 c15 (by decide +kernel)
  have t13 : a 7 ∈ [0,9,10,11,18,19,20,21,22,23,30,31,32,33,34,35] := remove (a 7) 8 [0,8,9,10,11,18,19,20,21,22,23,30,31,32,33,34,35] t12 b13
  have b14 : a 7 ≠ 9 := exclude [0] (fun u v => edge r15 v u) (a 7) (a 5) 9 t5 c15 (by decide +kernel)
  have t14 : a 7 ∈ [0,10,11,18,19,20,21,22,23,30,31,32,33,34,35] := remove (a 7) 9 [0,9,10,11,18,19,20,21,22,23,30,31,32,33,34,35] t13 b14
  have b15 : a 7 ≠ 10 := exclude [0] (fun u v => edge r15 v u) (a 7) (a 5) 10 t5 c15 (by decide +kernel)
  have t15 : a 7 ∈ [0,11,18,19,20,21,22,23,30,31,32,33,34,35] := remove (a 7) 10 [0,10,11,18,19,20,21,22,23,30,31,32,33,34,35] t14 b15
  exact And.intro t2 (And.intro t5 (t15))

theorem chunk7 (a : Nat → Nat)
    (d7 : a 7 ∈ [0,11,18,19,20,21,22,23,30,31,32,33,34,35])
    (d5 : a 5 ∈ [0])
    (d13 : a 13 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (c15 : edge r15 (a 5) (a 7)=true)
    (c16 : edge r16 (a 5) (a 13)=true)
    : a 7 ∈ [0] ∧ a 13 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := by
  have b0 : a 7 ≠ 11 := exclude [0] (fun u v => edge r15 v u) (a 7) (a 5) 11 d5 c15 (by decide +kernel)
  have t0 : a 7 ∈ [0,18,19,20,21,22,23,30,31,32,33,34,35] := remove (a 7) 11 [0,11,18,19,20,21,22,23,30,31,32,33,34,35] d7 b0
  have b1 : a 7 ≠ 18 := exclude [0] (fun u v => edge r15 v u) (a 7) (a 5) 18 d5 c15 (by decide +kernel)
  have t1 : a 7 ∈ [0,19,20,21,22,23,30,31,32,33,34,35] := remove (a 7) 18 [0,18,19,20,21,22,23,30,31,32,33,34,35] t0 b1
  have b2 : a 7 ≠ 19 := exclude [0] (fun u v => edge r15 v u) (a 7) (a 5) 19 d5 c15 (by decide +kernel)
  have t2 : a 7 ∈ [0,20,21,22,23,30,31,32,33,34,35] := remove (a 7) 19 [0,19,20,21,22,23,30,31,32,33,34,35] t1 b2
  have b3 : a 7 ≠ 20 := exclude [0] (fun u v => edge r15 v u) (a 7) (a 5) 20 d5 c15 (by decide +kernel)
  have t3 : a 7 ∈ [0,21,22,23,30,31,32,33,34,35] := remove (a 7) 20 [0,20,21,22,23,30,31,32,33,34,35] t2 b3
  have b4 : a 7 ≠ 21 := exclude [0] (fun u v => edge r15 v u) (a 7) (a 5) 21 d5 c15 (by decide +kernel)
  have t4 : a 7 ∈ [0,22,23,30,31,32,33,34,35] := remove (a 7) 21 [0,21,22,23,30,31,32,33,34,35] t3 b4
  have b5 : a 7 ≠ 22 := exclude [0] (fun u v => edge r15 v u) (a 7) (a 5) 22 d5 c15 (by decide +kernel)
  have t5 : a 7 ∈ [0,23,30,31,32,33,34,35] := remove (a 7) 22 [0,22,23,30,31,32,33,34,35] t4 b5
  have b6 : a 7 ≠ 23 := exclude [0] (fun u v => edge r15 v u) (a 7) (a 5) 23 d5 c15 (by decide +kernel)
  have t6 : a 7 ∈ [0,30,31,32,33,34,35] := remove (a 7) 23 [0,23,30,31,32,33,34,35] t5 b6
  have b7 : a 7 ≠ 30 := exclude [0] (fun u v => edge r15 v u) (a 7) (a 5) 30 d5 c15 (by decide +kernel)
  have t7 : a 7 ∈ [0,31,32,33,34,35] := remove (a 7) 30 [0,30,31,32,33,34,35] t6 b7
  have b8 : a 7 ≠ 31 := exclude [0] (fun u v => edge r15 v u) (a 7) (a 5) 31 d5 c15 (by decide +kernel)
  have t8 : a 7 ∈ [0,32,33,34,35] := remove (a 7) 31 [0,31,32,33,34,35] t7 b8
  have b9 : a 7 ≠ 32 := exclude [0] (fun u v => edge r15 v u) (a 7) (a 5) 32 d5 c15 (by decide +kernel)
  have t9 : a 7 ∈ [0,33,34,35] := remove (a 7) 32 [0,32,33,34,35] t8 b9
  have b10 : a 7 ≠ 33 := exclude [0] (fun u v => edge r15 v u) (a 7) (a 5) 33 d5 c15 (by decide +kernel)
  have t10 : a 7 ∈ [0,34,35] := remove (a 7) 33 [0,33,34,35] t9 b10
  have b11 : a 7 ≠ 34 := exclude [0] (fun u v => edge r15 v u) (a 7) (a 5) 34 d5 c15 (by decide +kernel)
  have t11 : a 7 ∈ [0,35] := remove (a 7) 34 [0,34,35] t10 b11
  have b12 : a 7 ≠ 35 := exclude [0] (fun u v => edge r15 v u) (a 7) (a 5) 35 d5 c15 (by decide +kernel)
  have t12 : a 7 ∈ [0] := remove (a 7) 35 [0,35] t11 b12
  have b13 : a 13 ≠ 1 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 1 d5 c16 (by decide +kernel)
  have t13 : a 13 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 13) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d13 b13
  have b14 : a 13 ≠ 2 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 2 d5 c16 (by decide +kernel)
  have t14 : a 13 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 13) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t13 b14
  have b15 : a 13 ≠ 3 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 3 d5 c16 (by decide +kernel)
  have t15 : a 13 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 13) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t14 b15
  exact And.intro t12 (t15)

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_150
