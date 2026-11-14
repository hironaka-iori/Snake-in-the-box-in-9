import PartitionData205_206
namespace PartitionCover205_206
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk20 (a : Nat → Nat)
    (d16 : a 16 ∈ [0,6,8,12,13,15,17])
    (d20 : a 20 ∈ [0,6])
    (d17 : a 17 ∈ [0,3,4,6,7,8])
    (d21 : a 21 ∈ [0,2])
    (d25 : a 25 ∈ [0,1,3,4,5,6,7,8,9,10])
    (d19 : a 19 ∈ [0,1,3,4,6,7])
    (d18 : a 18 ∈ [0,1,4,5])
    (c50 : edge r50 (a 16) (a 20)=true)
    (c53 : edge r53 (a 17) (a 21)=true)
    (c54 : edge r54 (a 17) (a 25)=true)
    (c55 : edge r55 (a 18) (a 19)=true)
    : a 16 ∈ [0,6,8,12] ∧ a 17 ∈ [0,4] ∧ a 25 ∈ [0,1,9,10] ∧ a 19 ∈ [0,1,7] := by
  have b0 : a 16 ≠ 13 := exclude [0,6] (edge r50) (a 16) (a 20) 13 d20 c50 (by decide +kernel)
  have t0 : a 16 ∈ [0,6,8,12,15,17] := remove (a 16) 13 [0,6,8,12,13,15,17] d16 b0
  have b1 : a 16 ≠ 15 := exclude [0,6] (edge r50) (a 16) (a 20) 15 d20 c50 (by decide +kernel)
  have t1 : a 16 ∈ [0,6,8,12,17] := remove (a 16) 15 [0,6,8,12,15,17] t0 b1
  have b2 : a 16 ≠ 17 := exclude [0,6] (edge r50) (a 16) (a 20) 17 d20 c50 (by decide +kernel)
  have t2 : a 16 ∈ [0,6,8,12] := remove (a 16) 17 [0,6,8,12,17] t1 b2
  have b3 : a 17 ≠ 3 := exclude [0,2] (edge r53) (a 17) (a 21) 3 d21 c53 (by decide +kernel)
  have t3 : a 17 ∈ [0,4,6,7,8] := remove (a 17) 3 [0,3,4,6,7,8] d17 b3
  have b4 : a 17 ≠ 6 := exclude [0,2] (edge r53) (a 17) (a 21) 6 d21 c53 (by decide +kernel)
  have t4 : a 17 ∈ [0,4,7,8] := remove (a 17) 6 [0,4,6,7,8] t3 b4
  have b5 : a 17 ≠ 7 := exclude [0,2] (edge r53) (a 17) (a 21) 7 d21 c53 (by decide +kernel)
  have t5 : a 17 ∈ [0,4,8] := remove (a 17) 7 [0,4,7,8] t4 b5
  have b6 : a 17 ≠ 8 := exclude [0,2] (edge r53) (a 17) (a 21) 8 d21 c53 (by decide +kernel)
  have t6 : a 17 ∈ [0,4] := remove (a 17) 8 [0,4,8] t5 b6
  have b7 : a 25 ≠ 3 := exclude [0,4] (fun u v => edge r54 v u) (a 25) (a 17) 3 t6 c54 (by decide +kernel)
  have t7 : a 25 ∈ [0,1,4,5,6,7,8,9,10] := remove (a 25) 3 [0,1,3,4,5,6,7,8,9,10] d25 b7
  have b8 : a 25 ≠ 4 := exclude [0,4] (fun u v => edge r54 v u) (a 25) (a 17) 4 t6 c54 (by decide +kernel)
  have t8 : a 25 ∈ [0,1,5,6,7,8,9,10] := remove (a 25) 4 [0,1,4,5,6,7,8,9,10] t7 b8
  have b9 : a 25 ≠ 5 := exclude [0,4] (fun u v => edge r54 v u) (a 25) (a 17) 5 t6 c54 (by decide +kernel)
  have t9 : a 25 ∈ [0,1,6,7,8,9,10] := remove (a 25) 5 [0,1,5,6,7,8,9,10] t8 b9
  have b10 : a 25 ≠ 6 := exclude [0,4] (fun u v => edge r54 v u) (a 25) (a 17) 6 t6 c54 (by decide +kernel)
  have t10 : a 25 ∈ [0,1,7,8,9,10] := remove (a 25) 6 [0,1,6,7,8,9,10] t9 b10
  have b11 : a 25 ≠ 7 := exclude [0,4] (fun u v => edge r54 v u) (a 25) (a 17) 7 t6 c54 (by decide +kernel)
  have t11 : a 25 ∈ [0,1,8,9,10] := remove (a 25) 7 [0,1,7,8,9,10] t10 b11
  have b12 : a 25 ≠ 8 := exclude [0,4] (fun u v => edge r54 v u) (a 25) (a 17) 8 t6 c54 (by decide +kernel)
  have t12 : a 25 ∈ [0,1,9,10] := remove (a 25) 8 [0,1,8,9,10] t11 b12
  have b13 : a 19 ≠ 3 := exclude [0,1,4,5] (fun u v => edge r55 v u) (a 19) (a 18) 3 d18 c55 (by decide +kernel)
  have t13 : a 19 ∈ [0,1,4,6,7] := remove (a 19) 3 [0,1,3,4,6,7] d19 b13
  have b14 : a 19 ≠ 4 := exclude [0,1,4,5] (fun u v => edge r55 v u) (a 19) (a 18) 4 d18 c55 (by decide +kernel)
  have t14 : a 19 ∈ [0,1,6,7] := remove (a 19) 4 [0,1,4,6,7] t13 b14
  have b15 : a 19 ≠ 6 := exclude [0,1,4,5] (fun u v => edge r55 v u) (a 19) (a 18) 6 d18 c55 (by decide +kernel)
  have t15 : a 19 ∈ [0,1,7] := remove (a 19) 6 [0,1,6,7] t14 b15
  exact And.intro t2 (And.intro t6 (And.intro t12 (t15)))

theorem chunk21 (a : Nat → Nat)
    (d19 : a 19 ∈ [0,1,7])
    (d18 : a 18 ∈ [0,1,4,5])
    (d22 : a 22 ∈ [0,1,4,5,6,7,10,11])
    (d26 : a 26 ∈ [0,8,12,20])
    (d27 : a 27 ∈ [0,1,2])
    (d28 : a 28 ∈ [0,1,2,3,8,9,11])
    (d20 : a 20 ∈ [0,6])
    (d23 : a 23 ∈ [0,1,4,5])
    (d21 : a 21 ∈ [0,2])
    (d24 : a 24 ∈ [0,12,16,18])
    (d25 : a 25 ∈ [0,1,9,10])
    (c55 : edge r55 (a 18) (a 19)=true)
    (c56 : edge r56 (a 18) (a 22)=true)
    (c57 : edge r57 (a 18) (a 26)=true)
    (c59 : edge r59 (a 19) (a 27)=true)
    (c62 : edge r62 (a 20) (a 28)=true)
    (c63 : edge r63 (a 21) (a 23)=true)
    (c68 : edge r68 (a 24) (a 25)=true)
    : a 19 ∈ [0,1] ∧ a 22 ∈ [0,1,6,7] ∧ a 18 ∈ [0,4] ∧ a 27 ∈ [0,2] ∧ a 28 ∈ [0,1,9,11] ∧ a 23 ∈ [0,4] ∧ a 24 ∈ [0,18] ∧ a 25 ∈ [0,9,10] := by
  have b0 : a 19 ≠ 7 := exclude [0,1,4,5] (fun u v => edge r55 v u) (a 19) (a 18) 7 d18 c55 (by decide +kernel)
  have t0 : a 19 ∈ [0,1] := remove (a 19) 7 [0,1,7] d19 b0
  have b1 : a 22 ≠ 4 := exclude [0,1,4,5] (fun u v => edge r56 v u) (a 22) (a 18) 4 d18 c56 (by decide +kernel)
  have t1 : a 22 ∈ [0,1,5,6,7,10,11] := remove (a 22) 4 [0,1,4,5,6,7,10,11] d22 b1
  have b2 : a 22 ≠ 5 := exclude [0,1,4,5] (fun u v => edge r56 v u) (a 22) (a 18) 5 d18 c56 (by decide +kernel)
  have t2 : a 22 ∈ [0,1,6,7,10,11] := remove (a 22) 5 [0,1,5,6,7,10,11] t1 b2
  have b3 : a 22 ≠ 10 := exclude [0,1,4,5] (fun u v => edge r56 v u) (a 22) (a 18) 10 d18 c56 (by decide +kernel)
  have t3 : a 22 ∈ [0,1,6,7,11] := remove (a 22) 10 [0,1,6,7,10,11] t2 b3
  have b4 : a 22 ≠ 11 := exclude [0,1,4,5] (fun u v => edge r56 v u) (a 22) (a 18) 11 d18 c56 (by decide +kernel)
  have t4 : a 22 ∈ [0,1,6,7] := remove (a 22) 11 [0,1,6,7,11] t3 b4
  have b5 : a 18 ≠ 1 := exclude [0,8,12,20] (edge r57) (a 18) (a 26) 1 d26 c57 (by decide +kernel)
  have t5 : a 18 ∈ [0,4,5] := remove (a 18) 1 [0,1,4,5] d18 b5
  have b6 : a 18 ≠ 5 := exclude [0,8,12,20] (edge r57) (a 18) (a 26) 5 d26 c57 (by decide +kernel)
  have t6 : a 18 ∈ [0,4] := remove (a 18) 5 [0,4,5] t5 b6
  have b7 : a 27 ≠ 1 := exclude [0,1] (fun u v => edge r59 v u) (a 27) (a 19) 1 t0 c59 (by decide +kernel)
  have t7 : a 27 ∈ [0,2] := remove (a 27) 1 [0,1,2] d27 b7
  have b8 : a 28 ≠ 2 := exclude [0,6] (fun u v => edge r62 v u) (a 28) (a 20) 2 d20 c62 (by decide +kernel)
  have t8 : a 28 ∈ [0,1,3,8,9,11] := remove (a 28) 2 [0,1,2,3,8,9,11] d28 b8
  have b9 : a 28 ≠ 3 := exclude [0,6] (fun u v => edge r62 v u) (a 28) (a 20) 3 d20 c62 (by decide +kernel)
  have t9 : a 28 ∈ [0,1,8,9,11] := remove (a 28) 3 [0,1,3,8,9,11] t8 b9
  have b10 : a 28 ≠ 8 := exclude [0,6] (fun u v => edge r62 v u) (a 28) (a 20) 8 d20 c62 (by decide +kernel)
  have t10 : a 28 ∈ [0,1,9,11] := remove (a 28) 8 [0,1,8,9,11] t9 b10
  have b11 : a 23 ≠ 1 := exclude [0,2] (fun u v => edge r63 v u) (a 23) (a 21) 1 d21 c63 (by decide +kernel)
  have t11 : a 23 ∈ [0,4,5] := remove (a 23) 1 [0,1,4,5] d23 b11
  have b12 : a 23 ≠ 5 := exclude [0,2] (fun u v => edge r63 v u) (a 23) (a 21) 5 d21 c63 (by decide +kernel)
  have t12 : a 23 ∈ [0,4] := remove (a 23) 5 [0,4,5] t11 b12
  have b13 : a 24 ≠ 12 := exclude [0,1,9,10] (edge r68) (a 24) (a 25) 12 d25 c68 (by decide +kernel)
  have t13 : a 24 ∈ [0,16,18] := remove (a 24) 12 [0,12,16,18] d24 b13
  have b14 : a 24 ≠ 16 := exclude [0,1,9,10] (edge r68) (a 24) (a 25) 16 d25 c68 (by decide +kernel)
  have t14 : a 24 ∈ [0,18] := remove (a 24) 16 [0,16,18] t13 b14
  have b15 : a 25 ≠ 1 := exclude [0,18] (fun u v => edge r68 v u) (a 25) (a 24) 1 t14 c68 (by decide +kernel)
  have t15 : a 25 ∈ [0,9,10] := remove (a 25) 1 [0,1,9,10] d25 b15
  exact And.intro t0 (And.intro t4 (And.intro t6 (And.intro t7 (And.intro t10 (And.intro t12 (And.intro t14 (t15)))))))

theorem chunk22 (a : Nat → Nat)
    (d25 : a 25 ∈ [0,9,10])
    (d24 : a 24 ∈ [0,18])
    (d26 : a 26 ∈ [0,8,12,20])
    (d27 : a 27 ∈ [0,2])
    (d30 : a 30 ∈ [0,1,13,23])
    (d28 : a 28 ∈ [0,1,9,11])
    (d31 : a 31 ∈ [0,1,4,5])
    (d29 : a 29 ∈ [0,18])
    (d1 : a 1 ∈ [0,1,2])
    (d5 : a 5 ∈ [0,2])
    (d6 : a 6 ∈ [0,1,4])
    (d14 : a 14 ∈ [0,3,12,15])
    (d9 : a 9 ∈ [0,1,2,3])
    (d11 : a 11 ∈ [0,4])
    (d16 : a 16 ∈ [0,6,8,12])
    (d17 : a 17 ∈ [0,4])
    (c6 : edge r6 (a 1) (a 5)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c68 : edge r68 (a 24) (a 25)=true)
    (c73 : edge r73 (a 26) (a 27)=true)
    (c74 : edge r74 (a 26) (a 30)=true)
    (c77 : edge r77 (a 28) (a 30)=true)
    (c78 : edge r78 (a 29) (a 31)=true)
    : a 25 ∈ [0,9] ∧ a 26 ∈ [0,8] ∧ a 30 ∈ [0,1] ∧ a 28 ∈ [0,9] ∧ a 31 ∈ [0,1] ∧ a 1 ∈ [0,1] ∧ a 6 ∈ [0,4] ∧ a 9 ∈ [0,2] ∧ a 14 ∈ [0,12] ∧ a 16 ∈ [0,8,12] := by
  have b0 : a 25 ≠ 10 := exclude [0,18] (fun u v => edge r68 v u) (a 25) (a 24) 10 d24 c68 (by decide +kernel)
  have t0 : a 25 ∈ [0,9] := remove (a 25) 10 [0,9,10] d25 b0
  have b1 : a 26 ≠ 12 := exclude [0,2] (edge r73) (a 26) (a 27) 12 d27 c73 (by decide +kernel)
  have t1 : a 26 ∈ [0,8,20] := remove (a 26) 12 [0,8,12,20] d26 b1
  have b2 : a 26 ≠ 20 := exclude [0,2] (edge r73) (a 26) (a 27) 20 d27 c73 (by decide +kernel)
  have t2 : a 26 ∈ [0,8] := remove (a 26) 20 [0,8,20] t1 b2
  have b3 : a 30 ≠ 13 := exclude [0,8] (fun u v => edge r74 v u) (a 30) (a 26) 13 t2 c74 (by decide +kernel)
  have t3 : a 30 ∈ [0,1,23] := remove (a 30) 13 [0,1,13,23] d30 b3
  have b4 : a 30 ≠ 23 := exclude [0,8] (fun u v => edge r74 v u) (a 30) (a 26) 23 t2 c74 (by decide +kernel)
  have t4 : a 30 ∈ [0,1] := remove (a 30) 23 [0,1,23] t3 b4
  have b5 : a 28 ≠ 1 := exclude [0,1] (edge r77) (a 28) (a 30) 1 t4 c77 (by decide +kernel)
  have t5 : a 28 ∈ [0,9,11] := remove (a 28) 1 [0,1,9,11] d28 b5
  have b6 : a 28 ≠ 11 := exclude [0,1] (edge r77) (a 28) (a 30) 11 t4 c77 (by decide +kernel)
  have t6 : a 28 ∈ [0,9] := remove (a 28) 11 [0,9,11] t5 b6
  have b7 : a 31 ≠ 4 := exclude [0,18] (fun u v => edge r78 v u) (a 31) (a 29) 4 d29 c78 (by decide +kernel)
  have t7 : a 31 ∈ [0,1,5] := remove (a 31) 4 [0,1,4,5] d31 b7
  have b8 : a 31 ≠ 5 := exclude [0,18] (fun u v => edge r78 v u) (a 31) (a 29) 5 d29 c78 (by decide +kernel)
  have t8 : a 31 ∈ [0,1] := remove (a 31) 5 [0,1,5] t7 b8
  have b9 : a 1 ≠ 2 := exclude [0,2] (edge r6) (a 1) (a 5) 2 d5 c6 (by decide +kernel)
  have t9 : a 1 ∈ [0,1] := remove (a 1) 2 [0,1,2] d1 b9
  have b10 : a 6 ≠ 1 := exclude [0,3,12,15] (edge r24) (a 6) (a 14) 1 d14 c24 (by decide +kernel)
  have t10 : a 6 ∈ [0,4] := remove (a 6) 1 [0,1,4] d6 b10
  have b11 : a 9 ≠ 1 := exclude [0,4] (edge r32) (a 9) (a 11) 1 d11 c32 (by decide +kernel)
  have t11 : a 9 ∈ [0,2,3] := remove (a 9) 1 [0,1,2,3] d9 b11
  have b12 : a 9 ≠ 3 := exclude [0,4] (edge r32) (a 9) (a 11) 3 d11 c32 (by decide +kernel)
  have t12 : a 9 ∈ [0,2] := remove (a 9) 3 [0,2,3] t11 b12
  have b13 : a 14 ≠ 3 := exclude [0,1] (edge r46) (a 14) (a 30) 3 t4 c46 (by decide +kernel)
  have t13 : a 14 ∈ [0,12,15] := remove (a 14) 3 [0,3,12,15] d14 b13
  have b14 : a 14 ≠ 15 := exclude [0,1] (edge r46) (a 14) (a 30) 15 t4 c46 (by decide +kernel)
  have t14 : a 14 ∈ [0,12] := remove (a 14) 15 [0,12,15] t13 b14
  have b15 : a 16 ≠ 6 := exclude [0,4] (edge r48) (a 16) (a 17) 6 d17 c48 (by decide +kernel)
  have t15 : a 16 ∈ [0,8,12] := remove (a 16) 6 [0,6,8,12] d16 b15
  exact And.intro t0 (And.intro t2 (And.intro t4 (And.intro t6 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t12 (And.intro t14 (t15)))))))))

theorem chunk23 (a : Nat → Nat)
    (d16 : a 16 ∈ [0,8,12])
    (d17 : a 17 ∈ [0,4])
    (d22 : a 22 ∈ [0,1,6,7])
    (d30 : a 30 ∈ [0,1])
    (d8 : a 8 ∈ [0,4,6,10])
    (d9 : a 9 ∈ [0,2])
    (c28 : edge r28 (a 8) (a 9)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c66 : edge r66 (a 22) (a 30)=true)
    : a 16 ∈ [0,8] ∧ a 22 ∈ [0,6] ∧ a 8 ∈ [0,6] := by
  have b0 : a 16 ≠ 12 := exclude [0,4] (edge r48) (a 16) (a 17) 12 d17 c48 (by decide +kernel)
  have t0 : a 16 ∈ [0,8] := remove (a 16) 12 [0,8,12] d16 b0
  have b1 : a 22 ≠ 1 := exclude [0,1] (edge r66) (a 22) (a 30) 1 d30 c66 (by decide +kernel)
  have t1 : a 22 ∈ [0,6,7] := remove (a 22) 1 [0,1,6,7] d22 b1
  have b2 : a 22 ≠ 7 := exclude [0,1] (edge r66) (a 22) (a 30) 7 d30 c66 (by decide +kernel)
  have t2 : a 22 ∈ [0,6] := remove (a 22) 7 [0,6,7] t1 b2
  have b3 : a 8 ≠ 4 := exclude [0,2] (edge r28) (a 8) (a 9) 4 d9 c28 (by decide +kernel)
  have t3 : a 8 ∈ [0,6,10] := remove (a 8) 4 [0,4,6,10] d8 b3
  have b4 : a 8 ≠ 10 := exclude [0,2] (edge r28) (a 8) (a 9) 10 d9 c28 (by decide +kernel)
  have t4 : a 8 ∈ [0,6] := remove (a 8) 10 [0,6,10] t3 b4
  exact And.intro t0 (And.intro t2 (t4))

#print axioms chunk20
#print axioms chunk21
#print axioms chunk22
#print axioms chunk23
end PartitionCover205_206
