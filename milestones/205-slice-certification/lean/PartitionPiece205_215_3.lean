import PartitionData205_215
namespace PartitionCover205_215
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk12 (a : Nat → Nat)
    (d27 : a 27 ∈ [0,1,2,3,4,5,16,17])
    (d13 : a 13 ∈ [0])
    (d28 : a 28 ∈ [0,1,2,3,4,5,6,7,8])
    (d14 : a 14 ∈ [0,3])
    (d15 : a 15 ∈ [0,1])
    (d18 : a 18 ∈ [0,1,2])
    (d16 : a 16 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d19 : a 19 ∈ [0,9])
    (c39 : edge r39 (a 13) (a 27)=true)
    (c40 : edge r40 (a 14) (a 28)=true)
    (c41 : edge r41 (a 15) (a 18)=true)
    (c43 : edge r43 (a 16) (a 19)=true)
    : a 27 ∈ [0,1,2,3,4,5] ∧ a 28 ∈ [0,2] ∧ a 15 ∈ [0] ∧ a 18 ∈ [0] ∧ a 16 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 27 ≠ 16 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 13) 16 d13 c39 (by decide +kernel)
  have t0 : a 27 ∈ [0,1,2,3,4,5,17] := remove (a 27) 16 [0,1,2,3,4,5,16,17] d27 b0
  have b1 : a 27 ≠ 17 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 13) 17 d13 c39 (by decide +kernel)
  have t1 : a 27 ∈ [0,1,2,3,4,5] := remove (a 27) 17 [0,1,2,3,4,5,17] t0 b1
  have b2 : a 28 ≠ 1 := exclude [0,3] (fun u v => edge r40 v u) (a 28) (a 14) 1 d14 c40 (by decide +kernel)
  have t2 : a 28 ∈ [0,2,3,4,5,6,7,8] := remove (a 28) 1 [0,1,2,3,4,5,6,7,8] d28 b2
  have b3 : a 28 ≠ 3 := exclude [0,3] (fun u v => edge r40 v u) (a 28) (a 14) 3 d14 c40 (by decide +kernel)
  have t3 : a 28 ∈ [0,2,4,5,6,7,8] := remove (a 28) 3 [0,2,3,4,5,6,7,8] t2 b3
  have b4 : a 28 ≠ 4 := exclude [0,3] (fun u v => edge r40 v u) (a 28) (a 14) 4 d14 c40 (by decide +kernel)
  have t4 : a 28 ∈ [0,2,5,6,7,8] := remove (a 28) 4 [0,2,4,5,6,7,8] t3 b4
  have b5 : a 28 ≠ 5 := exclude [0,3] (fun u v => edge r40 v u) (a 28) (a 14) 5 d14 c40 (by decide +kernel)
  have t5 : a 28 ∈ [0,2,6,7,8] := remove (a 28) 5 [0,2,5,6,7,8] t4 b5
  have b6 : a 28 ≠ 6 := exclude [0,3] (fun u v => edge r40 v u) (a 28) (a 14) 6 d14 c40 (by decide +kernel)
  have t6 : a 28 ∈ [0,2,7,8] := remove (a 28) 6 [0,2,6,7,8] t5 b6
  have b7 : a 28 ≠ 7 := exclude [0,3] (fun u v => edge r40 v u) (a 28) (a 14) 7 d14 c40 (by decide +kernel)
  have t7 : a 28 ∈ [0,2,8] := remove (a 28) 7 [0,2,7,8] t6 b7
  have b8 : a 28 ≠ 8 := exclude [0,3] (fun u v => edge r40 v u) (a 28) (a 14) 8 d14 c40 (by decide +kernel)
  have t8 : a 28 ∈ [0,2] := remove (a 28) 8 [0,2,8] t7 b8
  have b9 : a 15 ≠ 1 := exclude [0,1,2] (edge r41) (a 15) (a 18) 1 d18 c41 (by decide +kernel)
  have t9 : a 15 ∈ [0] := remove (a 15) 1 [0,1] d15 b9
  have b10 : a 18 ≠ 1 := exclude [0] (fun u v => edge r41 v u) (a 18) (a 15) 1 t9 c41 (by decide +kernel)
  have t10 : a 18 ∈ [0,2] := remove (a 18) 1 [0,1,2] d18 b10
  have b11 : a 18 ≠ 2 := exclude [0] (fun u v => edge r41 v u) (a 18) (a 15) 2 t9 c41 (by decide +kernel)
  have t11 : a 18 ∈ [0] := remove (a 18) 2 [0,2] t10 b11
  have b12 : a 16 ≠ 2 := exclude [0,9] (edge r43) (a 16) (a 19) 2 d19 c43 (by decide +kernel)
  have t12 : a 16 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 16) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d16 b12
  have b13 : a 16 ≠ 3 := exclude [0,9] (edge r43) (a 16) (a 19) 3 d19 c43 (by decide +kernel)
  have t13 : a 16 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 16) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 16 ≠ 4 := exclude [0,9] (edge r43) (a 16) (a 19) 4 d19 c43 (by decide +kernel)
  have t14 : a 16 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 16) 4 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 16 ≠ 5 := exclude [0,9] (edge r43) (a 16) (a 19) 5 d19 c43 (by decide +kernel)
  have t15 : a 16 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 16) 5 [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t1 (And.intro t8 (And.intro t9 (And.intro t11 (t15))))

theorem chunk13 (a : Nat → Nat)
    (d16 : a 16 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d19 : a 19 ∈ [0,9])
    (c43 : edge r43 (a 16) (a 19)=true)
    : a 16 ∈ [0,1,18,19] := by
  have b0 : a 16 ≠ 6 := exclude [0,9] (edge r43) (a 16) (a 19) 6 d19 c43 (by decide +kernel)
  have t0 : a 16 ∈ [0,1,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 16) 6 [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d16 b0
  have b1 : a 16 ≠ 7 := exclude [0,9] (edge r43) (a 16) (a 19) 7 d19 c43 (by decide +kernel)
  have t1 : a 16 ∈ [0,1,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 16) 7 [0,1,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 16 ≠ 8 := exclude [0,9] (edge r43) (a 16) (a 19) 8 d19 c43 (by decide +kernel)
  have t2 : a 16 ∈ [0,1,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 16) 8 [0,1,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 16 ≠ 9 := exclude [0,9] (edge r43) (a 16) (a 19) 9 d19 c43 (by decide +kernel)
  have t3 : a 16 ∈ [0,1,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 16) 9 [0,1,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 16 ≠ 10 := exclude [0,9] (edge r43) (a 16) (a 19) 10 d19 c43 (by decide +kernel)
  have t4 : a 16 ∈ [0,1,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 16) 10 [0,1,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 16 ≠ 11 := exclude [0,9] (edge r43) (a 16) (a 19) 11 d19 c43 (by decide +kernel)
  have t5 : a 16 ∈ [0,1,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 16) 11 [0,1,11,12,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 16 ≠ 12 := exclude [0,9] (edge r43) (a 16) (a 19) 12 d19 c43 (by decide +kernel)
  have t6 : a 16 ∈ [0,1,13,14,15,16,17,18,19,20,21,22,23] := remove (a 16) 12 [0,1,12,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 16 ≠ 13 := exclude [0,9] (edge r43) (a 16) (a 19) 13 d19 c43 (by decide +kernel)
  have t7 : a 16 ∈ [0,1,14,15,16,17,18,19,20,21,22,23] := remove (a 16) 13 [0,1,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 16 ≠ 14 := exclude [0,9] (edge r43) (a 16) (a 19) 14 d19 c43 (by decide +kernel)
  have t8 : a 16 ∈ [0,1,15,16,17,18,19,20,21,22,23] := remove (a 16) 14 [0,1,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 16 ≠ 15 := exclude [0,9] (edge r43) (a 16) (a 19) 15 d19 c43 (by decide +kernel)
  have t9 : a 16 ∈ [0,1,16,17,18,19,20,21,22,23] := remove (a 16) 15 [0,1,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 16 ≠ 16 := exclude [0,9] (edge r43) (a 16) (a 19) 16 d19 c43 (by decide +kernel)
  have t10 : a 16 ∈ [0,1,17,18,19,20,21,22,23] := remove (a 16) 16 [0,1,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 16 ≠ 17 := exclude [0,9] (edge r43) (a 16) (a 19) 17 d19 c43 (by decide +kernel)
  have t11 : a 16 ∈ [0,1,18,19,20,21,22,23] := remove (a 16) 17 [0,1,17,18,19,20,21,22,23] t10 b11
  have b12 : a 16 ≠ 20 := exclude [0,9] (edge r43) (a 16) (a 19) 20 d19 c43 (by decide +kernel)
  have t12 : a 16 ∈ [0,1,18,19,21,22,23] := remove (a 16) 20 [0,1,18,19,20,21,22,23] t11 b12
  have b13 : a 16 ≠ 21 := exclude [0,9] (edge r43) (a 16) (a 19) 21 d19 c43 (by decide +kernel)
  have t13 : a 16 ∈ [0,1,18,19,22,23] := remove (a 16) 21 [0,1,18,19,21,22,23] t12 b13
  have b14 : a 16 ≠ 22 := exclude [0,9] (edge r43) (a 16) (a 19) 22 d19 c43 (by decide +kernel)
  have t14 : a 16 ∈ [0,1,18,19,23] := remove (a 16) 22 [0,1,18,19,22,23] t13 b14
  have b15 : a 16 ≠ 23 := exclude [0,9] (edge r43) (a 16) (a 19) 23 d19 c43 (by decide +kernel)
  have t15 : a 16 ∈ [0,1,18,19] := remove (a 16) 23 [0,1,18,19,23] t14 b15
  exact t15

theorem chunk14 (a : Nat → Nat)
    (d16 : a 16 ∈ [0,1,18,19])
    (d23 : a 23 ∈ [0])
    (d17 : a 17 ∈ [0,1])
    (d18 : a 18 ∈ [0])
    (d25 : a 25 ∈ [0,8,10,11])
    (d20 : a 20 ∈ [0,3,12,15,20,22])
    (d19 : a 19 ∈ [0,9])
    (d21 : a 21 ∈ [0,5,14,16])
    (d22 : a 22 ∈ [0,1])
    (d24 : a 24 ∈ [0,1])
    (c44 : edge r44 (a 16) (a 23)=true)
    (c45 : edge r45 (a 17) (a 18)=true)
    (c47 : edge r47 (a 17) (a 25)=true)
    (c48 : edge r48 (a 18) (a 20)=true)
    (c50 : edge r50 (a 19) (a 20)=true)
    (c54 : edge r54 (a 21) (a 23)=true)
    (c55 : edge r55 (a 21) (a 25)=true)
    (c56 : edge r56 (a 22) (a 24)=true)
    : a 16 ∈ [0,18] ∧ a 17 ∈ [0] ∧ a 25 ∈ [0] ∧ a 20 ∈ [0,3] ∧ a 19 ∈ [0] ∧ a 21 ∈ [0] ∧ a 22 ∈ [0] ∧ a 24 ∈ [0] := by
  have b0 : a 16 ≠ 1 := exclude [0] (edge r44) (a 16) (a 23) 1 d23 c44 (by decide +kernel)
  have t0 : a 16 ∈ [0,18,19] := remove (a 16) 1 [0,1,18,19] d16 b0
  have b1 : a 16 ≠ 19 := exclude [0] (edge r44) (a 16) (a 23) 19 d23 c44 (by decide +kernel)
  have t1 : a 16 ∈ [0,18] := remove (a 16) 19 [0,18,19] t0 b1
  have b2 : a 17 ≠ 1 := exclude [0] (edge r45) (a 17) (a 18) 1 d18 c45 (by decide +kernel)
  have t2 : a 17 ∈ [0] := remove (a 17) 1 [0,1] d17 b2
  have b3 : a 25 ≠ 8 := exclude [0] (fun u v => edge r47 v u) (a 25) (a 17) 8 t2 c47 (by decide +kernel)
  have t3 : a 25 ∈ [0,10,11] := remove (a 25) 8 [0,8,10,11] d25 b3
  have b4 : a 25 ≠ 10 := exclude [0] (fun u v => edge r47 v u) (a 25) (a 17) 10 t2 c47 (by decide +kernel)
  have t4 : a 25 ∈ [0,11] := remove (a 25) 10 [0,10,11] t3 b4
  have b5 : a 25 ≠ 11 := exclude [0] (fun u v => edge r47 v u) (a 25) (a 17) 11 t2 c47 (by decide +kernel)
  have t5 : a 25 ∈ [0] := remove (a 25) 11 [0,11] t4 b5
  have b6 : a 20 ≠ 12 := exclude [0] (fun u v => edge r48 v u) (a 20) (a 18) 12 d18 c48 (by decide +kernel)
  have t6 : a 20 ∈ [0,3,15,20,22] := remove (a 20) 12 [0,3,12,15,20,22] d20 b6
  have b7 : a 20 ≠ 15 := exclude [0] (fun u v => edge r48 v u) (a 20) (a 18) 15 d18 c48 (by decide +kernel)
  have t7 : a 20 ∈ [0,3,20,22] := remove (a 20) 15 [0,3,15,20,22] t6 b7
  have b8 : a 20 ≠ 20 := exclude [0] (fun u v => edge r48 v u) (a 20) (a 18) 20 d18 c48 (by decide +kernel)
  have t8 : a 20 ∈ [0,3,22] := remove (a 20) 20 [0,3,20,22] t7 b8
  have b9 : a 20 ≠ 22 := exclude [0] (fun u v => edge r48 v u) (a 20) (a 18) 22 d18 c48 (by decide +kernel)
  have t9 : a 20 ∈ [0,3] := remove (a 20) 22 [0,3,22] t8 b9
  have b10 : a 19 ≠ 9 := exclude [0,3] (edge r50) (a 19) (a 20) 9 t9 c50 (by decide +kernel)
  have t10 : a 19 ∈ [0] := remove (a 19) 9 [0,9] d19 b10
  have b11 : a 21 ≠ 5 := exclude [0] (edge r54) (a 21) (a 23) 5 d23 c54 (by decide +kernel)
  have t11 : a 21 ∈ [0,14,16] := remove (a 21) 5 [0,5,14,16] d21 b11
  have b12 : a 21 ≠ 16 := exclude [0] (edge r54) (a 21) (a 23) 16 d23 c54 (by decide +kernel)
  have t12 : a 21 ∈ [0,14] := remove (a 21) 16 [0,14,16] t11 b12
  have b13 : a 21 ≠ 14 := exclude [0] (edge r55) (a 21) (a 25) 14 t5 c55 (by decide +kernel)
  have t13 : a 21 ∈ [0] := remove (a 21) 14 [0,14] t12 b13
  have b14 : a 22 ≠ 1 := exclude [0,1] (edge r56) (a 22) (a 24) 1 d24 c56 (by decide +kernel)
  have t14 : a 22 ∈ [0] := remove (a 22) 1 [0,1] d22 b14
  have b15 : a 24 ≠ 1 := exclude [0] (fun u v => edge r56 v u) (a 24) (a 22) 1 t14 c56 (by decide +kernel)
  have t15 : a 24 ∈ [0] := remove (a 24) 1 [0,1] d24 b15
  exact And.intro t1 (And.intro t2 (And.intro t5 (And.intro t9 (And.intro t10 (And.intro t13 (And.intro t14 (t15)))))))

theorem chunk15 (a : Nat → Nat)
    (d26 : a 26 ∈ [0,19])
    (d22 : a 22 ∈ [0])
    (d28 : a 28 ∈ [0,2])
    (d24 : a 24 ∈ [0])
    (d27 : a 27 ∈ [0,1,2,3,4,5])
    (d25 : a 25 ∈ [0])
    (d2 : a 2 ∈ [0,1])
    (d6 : a 6 ∈ [0])
    (d4 : a 4 ∈ [0,3])
    (d12 : a 12 ∈ [0])
    (d5 : a 5 ∈ [0,18])
    (d19 : a 19 ∈ [0])
    (d7 : a 7 ∈ [0,2])
    (d9 : a 9 ∈ [0])
    (d11 : a 11 ∈ [0,3])
    (d8 : a 8 ∈ [0,3])
    (d14 : a 14 ∈ [0,3])
    (d16 : a 16 ∈ [0,18])
    (d20 : a 20 ∈ [0,3])
    (c7 : edge r7 (a 2) (a 6)=true)
    (c14 : edge r14 (a 4) (a 12)=true)
    (c18 : edge r18 (a 5) (a 19)=true)
    (c22 : edge r22 (a 7) (a 9)=true)
    (c23 : edge r23 (a 7) (a 11)=true)
    (c26 : edge r26 (a 8) (a 12)=true)
    (c40 : edge r40 (a 14) (a 28)=true)
    (c43 : edge r43 (a 16) (a 19)=true)
    (c52 : edge r52 (a 20) (a 28)=true)
    (c57 : edge r57 (a 22) (a 26)=true)
    (c60 : edge r60 (a 24) (a 28)=true)
    (c62 : edge r62 (a 25) (a 27)=true)
    (c64 : edge r64 (a 27) (a 28)=true)
    : a 26 ∈ [0] ∧ a 28 ∈ [0] ∧ a 27 ∈ [0] ∧ a 2 ∈ [0] ∧ a 4 ∈ [0] ∧ a 5 ∈ [0] ∧ a 7 ∈ [0] ∧ a 11 ∈ [0] ∧ a 8 ∈ [0] ∧ a 14 ∈ [0] ∧ a 16 ∈ [0] ∧ a 20 ∈ [0] := by
  have b0 : a 26 ≠ 19 := exclude [0] (fun u v => edge r57 v u) (a 26) (a 22) 19 d22 c57 (by decide +kernel)
  have t0 : a 26 ∈ [0] := remove (a 26) 19 [0,19] d26 b0
  have b1 : a 28 ≠ 2 := exclude [0] (fun u v => edge r60 v u) (a 28) (a 24) 2 d24 c60 (by decide +kernel)
  have t1 : a 28 ∈ [0] := remove (a 28) 2 [0,2] d28 b1
  have b2 : a 27 ≠ 1 := exclude [0] (fun u v => edge r62 v u) (a 27) (a 25) 1 d25 c62 (by decide +kernel)
  have t2 : a 27 ∈ [0,2,3,4,5] := remove (a 27) 1 [0,1,2,3,4,5] d27 b2
  have b3 : a 27 ≠ 2 := exclude [0] (fun u v => edge r62 v u) (a 27) (a 25) 2 d25 c62 (by decide +kernel)
  have t3 : a 27 ∈ [0,3,4,5] := remove (a 27) 2 [0,2,3,4,5] t2 b3
  have b4 : a 27 ≠ 3 := exclude [0] (fun u v => edge r62 v u) (a 27) (a 25) 3 d25 c62 (by decide +kernel)
  have t4 : a 27 ∈ [0,4,5] := remove (a 27) 3 [0,3,4,5] t3 b4
  have b5 : a 27 ≠ 4 := exclude [0] (fun u v => edge r62 v u) (a 27) (a 25) 4 d25 c62 (by decide +kernel)
  have t5 : a 27 ∈ [0,5] := remove (a 27) 4 [0,4,5] t4 b5
  have b6 : a 27 ≠ 5 := exclude [0] (edge r64) (a 27) (a 28) 5 t1 c64 (by decide +kernel)
  have t6 : a 27 ∈ [0] := remove (a 27) 5 [0,5] t5 b6
  have b7 : a 2 ≠ 1 := exclude [0] (edge r7) (a 2) (a 6) 1 d6 c7 (by decide +kernel)
  have t7 : a 2 ∈ [0] := remove (a 2) 1 [0,1] d2 b7
  have b8 : a 4 ≠ 3 := exclude [0] (edge r14) (a 4) (a 12) 3 d12 c14 (by decide +kernel)
  have t8 : a 4 ∈ [0] := remove (a 4) 3 [0,3] d4 b8
  have b9 : a 5 ≠ 18 := exclude [0] (edge r18) (a 5) (a 19) 18 d19 c18 (by decide +kernel)
  have t9 : a 5 ∈ [0] := remove (a 5) 18 [0,18] d5 b9
  have b10 : a 7 ≠ 2 := exclude [0] (edge r22) (a 7) (a 9) 2 d9 c22 (by decide +kernel)
  have t10 : a 7 ∈ [0] := remove (a 7) 2 [0,2] d7 b10
  have b11 : a 11 ≠ 3 := exclude [0] (fun u v => edge r23 v u) (a 11) (a 7) 3 t10 c23 (by decide +kernel)
  have t11 : a 11 ∈ [0] := remove (a 11) 3 [0,3] d11 b11
  have b12 : a 8 ≠ 3 := exclude [0] (edge r26) (a 8) (a 12) 3 d12 c26 (by decide +kernel)
  have t12 : a 8 ∈ [0] := remove (a 8) 3 [0,3] d8 b12
  have b13 : a 14 ≠ 3 := exclude [0] (edge r40) (a 14) (a 28) 3 t1 c40 (by decide +kernel)
  have t13 : a 14 ∈ [0] := remove (a 14) 3 [0,3] d14 b13
  have b14 : a 16 ≠ 18 := exclude [0] (edge r43) (a 16) (a 19) 18 d19 c43 (by decide +kernel)
  have t14 : a 16 ∈ [0] := remove (a 16) 18 [0,18] d16 b14
  have b15 : a 20 ≠ 3 := exclude [0] (edge r52) (a 20) (a 28) 3 t1 c52 (by decide +kernel)
  have t15 : a 20 ∈ [0] := remove (a 20) 3 [0,3] d20 b15
  exact And.intro t0 (And.intro t1 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))
#print axioms chunk12
#print axioms chunk13
#print axioms chunk14
#print axioms chunk15
end PartitionCover205_215
