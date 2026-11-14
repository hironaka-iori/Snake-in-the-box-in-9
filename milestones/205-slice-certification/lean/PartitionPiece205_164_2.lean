import PartitionData205_164
namespace PartitionCover205_164
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d29 : a 29 ∈ [0,1,6,7,8,9,10,11])
    (d21 : a 21 ∈ [0])
    (d30 : a 30 ∈ [0,1,4])
    (d22 : a 22 ∈ [0,1])
    (d24 : a 24 ∈ [0,1,2])
    (d25 : a 25 ∈ [0,2])
    (d31 : a 31 ∈ [0,1,3,4,5,7,9,11])
    (d27 : a 27 ∈ [0])
    (c64 : edge r64 (a 21) (a 29)=true)
    (c66 : edge r66 (a 22) (a 30)=true)
    (c68 : edge r68 (a 24) (a 25)=true)
    (c75 : edge r75 (a 27) (a 31)=true)
    : a 29 ∈ [0,1] ∧ a 30 ∈ [0] ∧ a 24 ∈ [0] ∧ a 25 ∈ [0] ∧ a 31 ∈ [0,1,11] := by
  have b0 : a 29 ≠ 6 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 6 d21 c64 (by decide +kernel)
  have t0 : a 29 ∈ [0,1,7,8,9,10,11] := remove (a 29) 6 [0,1,6,7,8,9,10,11] d29 b0
  have b1 : a 29 ≠ 7 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 7 d21 c64 (by decide +kernel)
  have t1 : a 29 ∈ [0,1,8,9,10,11] := remove (a 29) 7 [0,1,7,8,9,10,11] t0 b1
  have b2 : a 29 ≠ 8 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 8 d21 c64 (by decide +kernel)
  have t2 : a 29 ∈ [0,1,9,10,11] := remove (a 29) 8 [0,1,8,9,10,11] t1 b2
  have b3 : a 29 ≠ 9 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 9 d21 c64 (by decide +kernel)
  have t3 : a 29 ∈ [0,1,10,11] := remove (a 29) 9 [0,1,9,10,11] t2 b3
  have b4 : a 29 ≠ 10 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 10 d21 c64 (by decide +kernel)
  have t4 : a 29 ∈ [0,1,11] := remove (a 29) 10 [0,1,10,11] t3 b4
  have b5 : a 29 ≠ 11 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 11 d21 c64 (by decide +kernel)
  have t5 : a 29 ∈ [0,1] := remove (a 29) 11 [0,1,11] t4 b5
  have b6 : a 30 ≠ 1 := exclude [0,1] (fun u v => edge r66 v u) (a 30) (a 22) 1 d22 c66 (by decide +kernel)
  have t6 : a 30 ∈ [0,4] := remove (a 30) 1 [0,1,4] d30 b6
  have b7 : a 30 ≠ 4 := exclude [0,1] (fun u v => edge r66 v u) (a 30) (a 22) 4 d22 c66 (by decide +kernel)
  have t7 : a 30 ∈ [0] := remove (a 30) 4 [0,4] t6 b7
  have b8 : a 24 ≠ 1 := exclude [0,2] (edge r68) (a 24) (a 25) 1 d25 c68 (by decide +kernel)
  have t8 : a 24 ∈ [0,2] := remove (a 24) 1 [0,1,2] d24 b8
  have b9 : a 24 ≠ 2 := exclude [0,2] (edge r68) (a 24) (a 25) 2 d25 c68 (by decide +kernel)
  have t9 : a 24 ∈ [0] := remove (a 24) 2 [0,2] t8 b9
  have b10 : a 25 ≠ 2 := exclude [0] (fun u v => edge r68 v u) (a 25) (a 24) 2 t9 c68 (by decide +kernel)
  have t10 : a 25 ∈ [0] := remove (a 25) 2 [0,2] d25 b10
  have b11 : a 31 ≠ 3 := exclude [0] (fun u v => edge r75 v u) (a 31) (a 27) 3 d27 c75 (by decide +kernel)
  have t11 : a 31 ∈ [0,1,4,5,7,9,11] := remove (a 31) 3 [0,1,3,4,5,7,9,11] d31 b11
  have b12 : a 31 ≠ 4 := exclude [0] (fun u v => edge r75 v u) (a 31) (a 27) 4 d27 c75 (by decide +kernel)
  have t12 : a 31 ∈ [0,1,5,7,9,11] := remove (a 31) 4 [0,1,4,5,7,9,11] t11 b12
  have b13 : a 31 ≠ 5 := exclude [0] (fun u v => edge r75 v u) (a 31) (a 27) 5 d27 c75 (by decide +kernel)
  have t13 : a 31 ∈ [0,1,7,9,11] := remove (a 31) 5 [0,1,5,7,9,11] t12 b13
  have b14 : a 31 ≠ 7 := exclude [0] (fun u v => edge r75 v u) (a 31) (a 27) 7 d27 c75 (by decide +kernel)
  have t14 : a 31 ∈ [0,1,9,11] := remove (a 31) 7 [0,1,7,9,11] t13 b14
  have b15 : a 31 ≠ 9 := exclude [0] (fun u v => edge r75 v u) (a 31) (a 27) 9 d27 c75 (by decide +kernel)
  have t15 : a 31 ∈ [0,1,11] := remove (a 31) 9 [0,1,9,11] t14 b15
  exact And.intro t5 (And.intro t7 (And.intro t9 (And.intro t10 (t15))))

theorem chunk9 (a : Nat → Nat)
    (d31 : a 31 ∈ [0,1,11])
    (d27 : a 27 ∈ [0])
    (d7 : a 7 ∈ [0,1,3,5])
    (d15 : a 15 ∈ [0])
    (d11 : a 11 ∈ [0,1,4,5])
    (c26 : edge r26 (a 7) (a 15)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    (c75 : edge r75 (a 27) (a 31)=true)
    : a 31 ∈ [0,1] ∧ a 7 ∈ [0,1] ∧ a 11 ∈ [0,4] := by
  have b0 : a 31 ≠ 11 := exclude [0] (fun u v => edge r75 v u) (a 31) (a 27) 11 d27 c75 (by decide +kernel)
  have t0 : a 31 ∈ [0,1] := remove (a 31) 11 [0,1,11] d31 b0
  have b1 : a 7 ≠ 3 := exclude [0] (edge r26) (a 7) (a 15) 3 d15 c26 (by decide +kernel)
  have t1 : a 7 ∈ [0,1,5] := remove (a 7) 3 [0,1,3,5] d7 b1
  have b2 : a 7 ≠ 5 := exclude [0] (edge r26) (a 7) (a 15) 5 d15 c26 (by decide +kernel)
  have t2 : a 7 ∈ [0,1] := remove (a 7) 5 [0,1,5] t1 b2
  have b3 : a 11 ≠ 1 := exclude [0] (edge r39) (a 11) (a 27) 1 d27 c39 (by decide +kernel)
  have t3 : a 11 ∈ [0,4,5] := remove (a 11) 1 [0,1,4,5] d11 b3
  have b4 : a 11 ≠ 5 := exclude [0] (edge r39) (a 11) (a 27) 5 d27 c39 (by decide +kernel)
  have t4 : a 11 ∈ [0,4] := remove (a 11) 5 [0,4,5] t3 b4
  exact And.intro t0 (And.intro t2 (t4))

theorem chunk10 (a : Nat → Nat)
    (d5 : a 5 ∈ [0,1])
    (d1 : a 1 ∈ [0])
    (d9 : a 9 ∈ [0,1])
    (d17 : a 17 ∈ [0,1])
    (d4 : a 4 ∈ [0,2])
    (d6 : a 6 ∈ [0,2])
    (d20 : a 20 ∈ [0,1])
    (d7 : a 7 ∈ [0,1])
    (d14 : a 14 ∈ [0,1])
    (d22 : a 22 ∈ [0,1])
    (d23 : a 23 ∈ [0,2])
    (d8 : a 8 ∈ [0,1])
    (d10 : a 10 ∈ [0,1])
    (d11 : a 11 ∈ [0,4])
    (d26 : a 26 ∈ [0,2])
    (d16 : a 16 ∈ [0,2])
    (d18 : a 18 ∈ [0,2])
    (c6 : edge r6 (a 1) (a 5)=true)
    (c7 : edge r7 (a 1) (a 9)=true)
    (c8 : edge r8 (a 1) (a 17)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    (c20 : edge r20 (a 5) (a 7)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c49 : edge r49 (a 16) (a 18)=true)
    : a 5 ∈ [0] ∧ a 9 ∈ [0] ∧ a 17 ∈ [0] ∧ a 4 ∈ [0] ∧ a 6 ∈ [0] ∧ a 20 ∈ [0] ∧ a 7 ∈ [0] ∧ a 14 ∈ [0] ∧ a 22 ∈ [0] ∧ a 23 ∈ [0] ∧ a 8 ∈ [0] ∧ a 10 ∈ [0] ∧ a 11 ∈ [0] ∧ a 26 ∈ [0] ∧ a 16 ∈ [0] ∧ a 18 ∈ [0] := by
  have b0 : a 5 ≠ 1 := exclude [0] (fun u v => edge r6 v u) (a 5) (a 1) 1 d1 c6 (by decide +kernel)
  have t0 : a 5 ∈ [0] := remove (a 5) 1 [0,1] d5 b0
  have b1 : a 9 ≠ 1 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 1 d1 c7 (by decide +kernel)
  have t1 : a 9 ∈ [0] := remove (a 9) 1 [0,1] d9 b1
  have b2 : a 17 ≠ 1 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 1 d1 c8 (by decide +kernel)
  have t2 : a 17 ∈ [0] := remove (a 17) 1 [0,1] d17 b2
  have b3 : a 4 ≠ 2 := exclude [0] (edge r16) (a 4) (a 5) 2 t0 c16 (by decide +kernel)
  have t3 : a 4 ∈ [0] := remove (a 4) 2 [0,2] d4 b3
  have b4 : a 6 ≠ 2 := exclude [0] (fun u v => edge r17 v u) (a 6) (a 4) 2 t3 c17 (by decide +kernel)
  have t4 : a 6 ∈ [0] := remove (a 6) 2 [0,2] d6 b4
  have b5 : a 20 ≠ 1 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 1 t3 c19 (by decide +kernel)
  have t5 : a 20 ∈ [0] := remove (a 20) 1 [0,1] d20 b5
  have b6 : a 7 ≠ 1 := exclude [0] (fun u v => edge r20 v u) (a 7) (a 5) 1 t0 c20 (by decide +kernel)
  have t6 : a 7 ∈ [0] := remove (a 7) 1 [0,1] d7 b6
  have b7 : a 14 ≠ 1 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 1 t4 c24 (by decide +kernel)
  have t7 : a 14 ∈ [0] := remove (a 14) 1 [0,1] d14 b7
  have b8 : a 22 ≠ 1 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 1 t4 c25 (by decide +kernel)
  have t8 : a 22 ∈ [0] := remove (a 22) 1 [0,1] d22 b8
  have b9 : a 23 ≠ 2 := exclude [0] (fun u v => edge r27 v u) (a 23) (a 7) 2 t6 c27 (by decide +kernel)
  have t9 : a 23 ∈ [0] := remove (a 23) 2 [0,2] d23 b9
  have b10 : a 8 ≠ 1 := exclude [0] (edge r28) (a 8) (a 9) 1 t1 c28 (by decide +kernel)
  have t10 : a 8 ∈ [0] := remove (a 8) 1 [0,1] d8 b10
  have b11 : a 10 ≠ 1 := exclude [0] (fun u v => edge r29 v u) (a 10) (a 8) 1 t10 c29 (by decide +kernel)
  have t11 : a 10 ∈ [0] := remove (a 10) 1 [0,1] d10 b11
  have b12 : a 11 ≠ 4 := exclude [0] (fun u v => edge r32 v u) (a 11) (a 9) 4 t1 c32 (by decide +kernel)
  have t12 : a 11 ∈ [0] := remove (a 11) 4 [0,4] d11 b12
  have b13 : a 26 ≠ 2 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 2 t11 c37 (by decide +kernel)
  have t13 : a 26 ∈ [0] := remove (a 26) 2 [0,2] d26 b13
  have b14 : a 16 ≠ 2 := exclude [0] (edge r48) (a 16) (a 17) 2 t2 c48 (by decide +kernel)
  have t14 : a 16 ∈ [0] := remove (a 16) 2 [0,2] d16 b14
  have b15 : a 18 ≠ 2 := exclude [0] (fun u v => edge r49 v u) (a 18) (a 16) 2 t14 c49 (by decide +kernel)
  have t15 : a 18 ∈ [0] := remove (a 18) 2 [0,2] d18 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk11 (a : Nat → Nat)
    (d19 : a 19 ∈ [0,2])
    (d17 : a 17 ∈ [0])
    (d28 : a 28 ∈ [0,1])
    (d20 : a 20 ∈ [0])
    (d31 : a 31 ∈ [0,1])
    (d23 : a 23 ∈ [0])
    (d29 : a 29 ∈ [0,1])
    (d2 : a 2 ∈ [0,1])
    (d6 : a 6 ∈ [0])
    (c10 : edge r10 (a 2) (a 6)=true)
    (c52 : edge r52 (a 17) (a 19)=true)
    (c62 : edge r62 (a 20) (a 28)=true)
    (c67 : edge r67 (a 23) (a 31)=true)
    (c76 : edge r76 (a 28) (a 29)=true)
    : a 19 ∈ [0] ∧ a 28 ∈ [0] ∧ a 31 ∈ [0] ∧ a 29 ∈ [0] ∧ a 2 ∈ [0] := by
  have b0 : a 19 ≠ 2 := exclude [0] (fun u v => edge r52 v u) (a 19) (a 17) 2 d17 c52 (by decide +kernel)
  have t0 : a 19 ∈ [0] := remove (a 19) 2 [0,2] d19 b0
  have b1 : a 28 ≠ 1 := exclude [0] (fun u v => edge r62 v u) (a 28) (a 20) 1 d20 c62 (by decide +kernel)
  have t1 : a 28 ∈ [0] := remove (a 28) 1 [0,1] d28 b1
  have b2 : a 31 ≠ 1 := exclude [0] (fun u v => edge r67 v u) (a 31) (a 23) 1 d23 c67 (by decide +kernel)
  have t2 : a 31 ∈ [0] := remove (a 31) 1 [0,1] d31 b2
  have b3 : a 29 ≠ 1 := exclude [0] (fun u v => edge r76 v u) (a 29) (a 28) 1 t1 c76 (by decide +kernel)
  have t3 : a 29 ∈ [0] := remove (a 29) 1 [0,1] d29 b3
  have b4 : a 2 ≠ 1 := exclude [0] (edge r10) (a 2) (a 6) 1 d6 c10 (by decide +kernel)
  have t4 : a 2 ∈ [0] := remove (a 2) 1 [0,1] d2 b4
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (t4))))

#print axioms chunk8
#print axioms chunk9
#print axioms chunk10
#print axioms chunk11
end PartitionCover205_164
