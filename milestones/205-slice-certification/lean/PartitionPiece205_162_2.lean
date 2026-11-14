import PartitionData205_162
namespace PartitionCover205_162
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d5 : a 5 ∈ [0,1,15,16,17])
    (d21 : a 21 ∈ [0,1])
    (d6 : a 6 ∈ [0,1,2,3,4,5,8,9,10,11,14,15,16,17])
    (d14 : a 14 ∈ [0,2,6,8,12,14])
    (d22 : a 22 ∈ [0,2])
    (c22 : edge r22 (a 5) (a 21)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    : a 5 ∈ [0,1] ∧ a 6 ∈ [0,2,8,14] ∧ a 14 ∈ [0,2,8,14] ∧ a 22 ∈ [0] := by
  have b0 : a 5 ≠ 15 := exclude [0,1] (edge r22) (a 5) (a 21) 15 d21 c22 (by decide +kernel)
  have t0 : a 5 ∈ [0,1,16,17] := remove (a 5) 15 [0,1,15,16,17] d5 b0
  have b1 : a 5 ≠ 16 := exclude [0,1] (edge r22) (a 5) (a 21) 16 d21 c22 (by decide +kernel)
  have t1 : a 5 ∈ [0,1,17] := remove (a 5) 16 [0,1,16,17] t0 b1
  have b2 : a 5 ≠ 17 := exclude [0,1] (edge r22) (a 5) (a 21) 17 d21 c22 (by decide +kernel)
  have t2 : a 5 ∈ [0,1] := remove (a 5) 17 [0,1,17] t1 b2
  have b3 : a 6 ≠ 1 := exclude [0,2,6,8,12,14] (edge r24) (a 6) (a 14) 1 d14 c24 (by decide +kernel)
  have t3 : a 6 ∈ [0,2,3,4,5,8,9,10,11,14,15,16,17] := remove (a 6) 1 [0,1,2,3,4,5,8,9,10,11,14,15,16,17] d6 b3
  have b4 : a 6 ≠ 3 := exclude [0,2,6,8,12,14] (edge r24) (a 6) (a 14) 3 d14 c24 (by decide +kernel)
  have t4 : a 6 ∈ [0,2,4,5,8,9,10,11,14,15,16,17] := remove (a 6) 3 [0,2,3,4,5,8,9,10,11,14,15,16,17] t3 b4
  have b5 : a 6 ≠ 4 := exclude [0,2,6,8,12,14] (edge r24) (a 6) (a 14) 4 d14 c24 (by decide +kernel)
  have t5 : a 6 ∈ [0,2,5,8,9,10,11,14,15,16,17] := remove (a 6) 4 [0,2,4,5,8,9,10,11,14,15,16,17] t4 b5
  have b6 : a 6 ≠ 5 := exclude [0,2,6,8,12,14] (edge r24) (a 6) (a 14) 5 d14 c24 (by decide +kernel)
  have t6 : a 6 ∈ [0,2,8,9,10,11,14,15,16,17] := remove (a 6) 5 [0,2,5,8,9,10,11,14,15,16,17] t5 b6
  have b7 : a 6 ≠ 9 := exclude [0,2,6,8,12,14] (edge r24) (a 6) (a 14) 9 d14 c24 (by decide +kernel)
  have t7 : a 6 ∈ [0,2,8,10,11,14,15,16,17] := remove (a 6) 9 [0,2,8,9,10,11,14,15,16,17] t6 b7
  have b8 : a 6 ≠ 10 := exclude [0,2,6,8,12,14] (edge r24) (a 6) (a 14) 10 d14 c24 (by decide +kernel)
  have t8 : a 6 ∈ [0,2,8,11,14,15,16,17] := remove (a 6) 10 [0,2,8,10,11,14,15,16,17] t7 b8
  have b9 : a 6 ≠ 11 := exclude [0,2,6,8,12,14] (edge r24) (a 6) (a 14) 11 d14 c24 (by decide +kernel)
  have t9 : a 6 ∈ [0,2,8,14,15,16,17] := remove (a 6) 11 [0,2,8,11,14,15,16,17] t8 b9
  have b10 : a 6 ≠ 15 := exclude [0,2,6,8,12,14] (edge r24) (a 6) (a 14) 15 d14 c24 (by decide +kernel)
  have t10 : a 6 ∈ [0,2,8,14,16,17] := remove (a 6) 15 [0,2,8,14,15,16,17] t9 b10
  have b11 : a 6 ≠ 16 := exclude [0,2,6,8,12,14] (edge r24) (a 6) (a 14) 16 d14 c24 (by decide +kernel)
  have t11 : a 6 ∈ [0,2,8,14,17] := remove (a 6) 16 [0,2,8,14,16,17] t10 b11
  have b12 : a 6 ≠ 17 := exclude [0,2,6,8,12,14] (edge r24) (a 6) (a 14) 17 d14 c24 (by decide +kernel)
  have t12 : a 6 ∈ [0,2,8,14] := remove (a 6) 17 [0,2,8,14,17] t11 b12
  have b13 : a 14 ≠ 6 := exclude [0,2,8,14] (fun u v => edge r24 v u) (a 14) (a 6) 6 t12 c24 (by decide +kernel)
  have t13 : a 14 ∈ [0,2,8,12,14] := remove (a 14) 6 [0,2,6,8,12,14] d14 b13
  have b14 : a 14 ≠ 12 := exclude [0,2,8,14] (fun u v => edge r24 v u) (a 14) (a 6) 12 t12 c24 (by decide +kernel)
  have t14 : a 14 ∈ [0,2,8,14] := remove (a 14) 12 [0,2,8,12,14] t13 b14
  have b15 : a 22 ≠ 2 := exclude [0,2,8,14] (fun u v => edge r25 v u) (a 22) (a 6) 2 t12 c25 (by decide +kernel)
  have t15 : a 22 ∈ [0] := remove (a 22) 2 [0,2] d22 b15
  exact And.intro t2 (And.intro t12 (And.intro t14 (t15)))

theorem chunk9 (a : Nat → Nat)
    (d7 : a 7 ∈ [0,1,2,3,4,5])
    (d23 : a 23 ∈ [0,2])
    (d8 : a 8 ∈ [0,1])
    (d9 : a 9 ∈ [0,2])
    (d11 : a 11 ∈ [0,2])
    (d12 : a 12 ∈ [0,1,2,3,4,5])
    (d28 : a 28 ∈ [0])
    (d14 : a 14 ∈ [0,2,8,14])
    (d30 : a 30 ∈ [0])
    (d15 : a 15 ∈ [0,1,2,3,4,5])
    (d31 : a 31 ∈ [0])
    (c27 : edge r27 (a 7) (a 23)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    : a 7 ∈ [0,1] ∧ a 8 ∈ [0] ∧ a 9 ∈ [0] ∧ a 11 ∈ [0] ∧ a 12 ∈ [0] ∧ a 14 ∈ [0] ∧ a 15 ∈ [0,1,3,4,5] := by
  have b0 : a 7 ≠ 2 := exclude [0,2] (edge r27) (a 7) (a 23) 2 d23 c27 (by decide +kernel)
  have t0 : a 7 ∈ [0,1,3,4,5] := remove (a 7) 2 [0,1,2,3,4,5] d7 b0
  have b1 : a 7 ≠ 3 := exclude [0,2] (edge r27) (a 7) (a 23) 3 d23 c27 (by decide +kernel)
  have t1 : a 7 ∈ [0,1,4,5] := remove (a 7) 3 [0,1,3,4,5] t0 b1
  have b2 : a 7 ≠ 4 := exclude [0,2] (edge r27) (a 7) (a 23) 4 d23 c27 (by decide +kernel)
  have t2 : a 7 ∈ [0,1,5] := remove (a 7) 4 [0,1,4,5] t1 b2
  have b3 : a 7 ≠ 5 := exclude [0,2] (edge r27) (a 7) (a 23) 5 d23 c27 (by decide +kernel)
  have t3 : a 7 ∈ [0,1] := remove (a 7) 5 [0,1,5] t2 b3
  have b4 : a 8 ≠ 1 := exclude [0,2] (edge r28) (a 8) (a 9) 1 d9 c28 (by decide +kernel)
  have t4 : a 8 ∈ [0] := remove (a 8) 1 [0,1] d8 b4
  have b5 : a 9 ≠ 2 := exclude [0] (fun u v => edge r28 v u) (a 9) (a 8) 2 t4 c28 (by decide +kernel)
  have t5 : a 9 ∈ [0] := remove (a 9) 2 [0,2] d9 b5
  have b6 : a 11 ≠ 2 := exclude [0] (fun u v => edge r32 v u) (a 11) (a 9) 2 t5 c32 (by decide +kernel)
  have t6 : a 11 ∈ [0] := remove (a 11) 2 [0,2] d11 b6
  have b7 : a 12 ≠ 1 := exclude [0] (edge r42) (a 12) (a 28) 1 d28 c42 (by decide +kernel)
  have t7 : a 12 ∈ [0,2,3,4,5] := remove (a 12) 1 [0,1,2,3,4,5] d12 b7
  have b8 : a 12 ≠ 2 := exclude [0] (edge r42) (a 12) (a 28) 2 d28 c42 (by decide +kernel)
  have t8 : a 12 ∈ [0,3,4,5] := remove (a 12) 2 [0,2,3,4,5] t7 b8
  have b9 : a 12 ≠ 3 := exclude [0] (edge r42) (a 12) (a 28) 3 d28 c42 (by decide +kernel)
  have t9 : a 12 ∈ [0,4,5] := remove (a 12) 3 [0,3,4,5] t8 b9
  have b10 : a 12 ≠ 4 := exclude [0] (edge r42) (a 12) (a 28) 4 d28 c42 (by decide +kernel)
  have t10 : a 12 ∈ [0,5] := remove (a 12) 4 [0,4,5] t9 b10
  have b11 : a 12 ≠ 5 := exclude [0] (edge r42) (a 12) (a 28) 5 d28 c42 (by decide +kernel)
  have t11 : a 12 ∈ [0] := remove (a 12) 5 [0,5] t10 b11
  have b12 : a 14 ≠ 2 := exclude [0] (edge r46) (a 14) (a 30) 2 d30 c46 (by decide +kernel)
  have t12 : a 14 ∈ [0,8,14] := remove (a 14) 2 [0,2,8,14] d14 b12
  have b13 : a 14 ≠ 8 := exclude [0] (edge r46) (a 14) (a 30) 8 d30 c46 (by decide +kernel)
  have t13 : a 14 ∈ [0,14] := remove (a 14) 8 [0,8,14] t12 b13
  have b14 : a 14 ≠ 14 := exclude [0] (edge r46) (a 14) (a 30) 14 d30 c46 (by decide +kernel)
  have t14 : a 14 ∈ [0] := remove (a 14) 14 [0,14] t13 b14
  have b15 : a 15 ≠ 2 := exclude [0] (edge r47) (a 15) (a 31) 2 d31 c47 (by decide +kernel)
  have t15 : a 15 ∈ [0,1,3,4,5] := remove (a 15) 2 [0,1,2,3,4,5] d15 b15
  exact And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t11 (And.intro t14 (t15))))))

theorem chunk10 (a : Nat → Nat)
    (d15 : a 15 ∈ [0,1,3,4,5])
    (d31 : a 31 ∈ [0])
    (d18 : a 18 ∈ [0,1])
    (d22 : a 22 ∈ [0])
    (d20 : a 20 ∈ [0,1])
    (d28 : a 28 ∈ [0])
    (d4 : a 4 ∈ [0,1,14,16])
    (d5 : a 5 ∈ [0,1])
    (d6 : a 6 ∈ [0,2,8,14])
    (d13 : a 13 ∈ [0,1,2,3,4,5])
    (d12 : a 12 ∈ [0])
    (c16 : edge r16 (a 4) (a 5)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c40 : edge r40 (a 12) (a 13)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c56 : edge r56 (a 18) (a 22)=true)
    (c62 : edge r62 (a 20) (a 28)=true)
    : a 15 ∈ [0,1] ∧ a 18 ∈ [0] ∧ a 20 ∈ [0] ∧ a 4 ∈ [0] ∧ a 6 ∈ [0] ∧ a 13 ∈ [0] := by
  have b0 : a 15 ≠ 3 := exclude [0] (edge r47) (a 15) (a 31) 3 d31 c47 (by decide +kernel)
  have t0 : a 15 ∈ [0,1,4,5] := remove (a 15) 3 [0,1,3,4,5] d15 b0
  have b1 : a 15 ≠ 4 := exclude [0] (edge r47) (a 15) (a 31) 4 d31 c47 (by decide +kernel)
  have t1 : a 15 ∈ [0,1,5] := remove (a 15) 4 [0,1,4,5] t0 b1
  have b2 : a 15 ≠ 5 := exclude [0] (edge r47) (a 15) (a 31) 5 d31 c47 (by decide +kernel)
  have t2 : a 15 ∈ [0,1] := remove (a 15) 5 [0,1,5] t1 b2
  have b3 : a 18 ≠ 1 := exclude [0] (edge r56) (a 18) (a 22) 1 d22 c56 (by decide +kernel)
  have t3 : a 18 ∈ [0] := remove (a 18) 1 [0,1] d18 b3
  have b4 : a 20 ≠ 1 := exclude [0] (edge r62) (a 20) (a 28) 1 d28 c62 (by decide +kernel)
  have t4 : a 20 ∈ [0] := remove (a 20) 1 [0,1] d20 b4
  have b5 : a 4 ≠ 14 := exclude [0,1] (edge r16) (a 4) (a 5) 14 d5 c16 (by decide +kernel)
  have t5 : a 4 ∈ [0,1,16] := remove (a 4) 14 [0,1,14,16] d4 b5
  have b6 : a 4 ≠ 16 := exclude [0,1] (edge r16) (a 4) (a 5) 16 d5 c16 (by decide +kernel)
  have t6 : a 4 ∈ [0,1] := remove (a 4) 16 [0,1,16] t5 b6
  have b7 : a 4 ≠ 1 := exclude [0,2,8,14] (edge r17) (a 4) (a 6) 1 d6 c17 (by decide +kernel)
  have t7 : a 4 ∈ [0] := remove (a 4) 1 [0,1] t6 b7
  have b8 : a 6 ≠ 2 := exclude [0] (fun u v => edge r17 v u) (a 6) (a 4) 2 t7 c17 (by decide +kernel)
  have t8 : a 6 ∈ [0,8,14] := remove (a 6) 2 [0,2,8,14] d6 b8
  have b9 : a 6 ≠ 8 := exclude [0] (fun u v => edge r17 v u) (a 6) (a 4) 8 t7 c17 (by decide +kernel)
  have t9 : a 6 ∈ [0,14] := remove (a 6) 8 [0,8,14] t8 b9
  have b10 : a 6 ≠ 14 := exclude [0] (fun u v => edge r17 v u) (a 6) (a 4) 14 t7 c17 (by decide +kernel)
  have t10 : a 6 ∈ [0] := remove (a 6) 14 [0,14] t9 b10
  have b11 : a 13 ≠ 1 := exclude [0] (fun u v => edge r40 v u) (a 13) (a 12) 1 d12 c40 (by decide +kernel)
  have t11 : a 13 ∈ [0,2,3,4,5] := remove (a 13) 1 [0,1,2,3,4,5] d13 b11
  have b12 : a 13 ≠ 2 := exclude [0] (fun u v => edge r40 v u) (a 13) (a 12) 2 d12 c40 (by decide +kernel)
  have t12 : a 13 ∈ [0,3,4,5] := remove (a 13) 2 [0,2,3,4,5] t11 b12
  have b13 : a 13 ≠ 3 := exclude [0] (fun u v => edge r40 v u) (a 13) (a 12) 3 d12 c40 (by decide +kernel)
  have t13 : a 13 ∈ [0,4,5] := remove (a 13) 3 [0,3,4,5] t12 b13
  have b14 : a 13 ≠ 4 := exclude [0] (fun u v => edge r40 v u) (a 13) (a 12) 4 d12 c40 (by decide +kernel)
  have t14 : a 13 ∈ [0,5] := remove (a 13) 4 [0,4,5] t13 b14
  have b15 : a 13 ≠ 5 := exclude [0] (fun u v => edge r40 v u) (a 13) (a 12) 5 d12 c40 (by decide +kernel)
  have t15 : a 13 ∈ [0] := remove (a 13) 5 [0,5] t14 b15
  exact And.intro t2 (And.intro t3 (And.intro t4 (And.intro t7 (And.intro t10 (t15)))))

theorem chunk11 (a : Nat → Nat)
    (d15 : a 15 ∈ [0,1])
    (d13 : a 13 ∈ [0])
    (d5 : a 5 ∈ [0,1])
    (d4 : a 4 ∈ [0])
    (d21 : a 21 ∈ [0,1])
    (d7 : a 7 ∈ [0,1])
    (d23 : a 23 ∈ [0,2])
    (c16 : edge r16 (a 4) (a 5)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    (c43 : edge r43 (a 13) (a 15)=true)
    : a 15 ∈ [0] ∧ a 5 ∈ [0] ∧ a 21 ∈ [0] ∧ a 7 ∈ [0] ∧ a 23 ∈ [0] := by
  have b0 : a 15 ≠ 1 := exclude [0] (fun u v => edge r43 v u) (a 15) (a 13) 1 d13 c43 (by decide +kernel)
  have t0 : a 15 ∈ [0] := remove (a 15) 1 [0,1] d15 b0
  have b1 : a 5 ≠ 1 := exclude [0] (fun u v => edge r16 v u) (a 5) (a 4) 1 d4 c16 (by decide +kernel)
  have t1 : a 5 ∈ [0] := remove (a 5) 1 [0,1] d5 b1
  have b2 : a 21 ≠ 1 := exclude [0] (fun u v => edge r22 v u) (a 21) (a 5) 1 t1 c22 (by decide +kernel)
  have t2 : a 21 ∈ [0] := remove (a 21) 1 [0,1] d21 b2
  have b3 : a 7 ≠ 1 := exclude [0] (edge r26) (a 7) (a 15) 1 t0 c26 (by decide +kernel)
  have t3 : a 7 ∈ [0] := remove (a 7) 1 [0,1] d7 b3
  have b4 : a 23 ≠ 2 := exclude [0] (fun u v => edge r27 v u) (a 23) (a 7) 2 t3 c27 (by decide +kernel)
  have t4 : a 23 ∈ [0] := remove (a 23) 2 [0,2] d23 b4
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (t4))))
#print axioms chunk8
#print axioms chunk9
#print axioms chunk10
#print axioms chunk11
end PartitionCover205_162
