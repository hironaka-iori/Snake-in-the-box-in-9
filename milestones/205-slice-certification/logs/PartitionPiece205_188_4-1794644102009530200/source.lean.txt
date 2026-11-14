import PartitionData205_188
namespace PartitionCover205_188
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk16 (a : Nat → Nat)
    (d22 : a 22 ∈ [0,6,8])
    (d23 : a 23 ∈ [0,1])
    (d31 : a 31 ∈ [0,2,9])
    (d24 : a 24 ∈ [0,2,4,8])
    (d25 : a 25 ∈ [0,1,2,3])
    (d29 : a 29 ∈ [0,2])
    (d26 : a 26 ∈ [0,2,9,21])
    (d27 : a 27 ∈ [0,2,4,5])
    (d30 : a 30 ∈ [0,1,2])
    (d4 : a 4 ∈ [0,1,2])
    (d12 : a 12 ∈ [0,4])
    (d5 : a 5 ∈ [0,1,2])
    (d13 : a 13 ∈ [0,1])
    (d6 : a 6 ∈ [0,2,3,5])
    (d14 : a 14 ∈ [0,6])
    (c18 : edge r18 (a 4) (a 12)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c65 : edge r65 (a 22) (a 23)=true)
    (c67 : edge r67 (a 23) (a 31)=true)
    (c68 : edge r68 (a 24) (a 25)=true)
    (c72 : edge r72 (a 25) (a 29)=true)
    (c73 : edge r73 (a 26) (a 27)=true)
    (c74 : edge r74 (a 26) (a 30)=true)
    : a 22 ∈ [0,6] ∧ a 31 ∈ [0,2] ∧ a 24 ∈ [0,2] ∧ a 25 ∈ [0,2] ∧ a 26 ∈ [0,2] ∧ a 27 ∈ [0,2] ∧ a 30 ∈ [0,1] ∧ a 4 ∈ [0] ∧ a 5 ∈ [0] ∧ a 6 ∈ [0,3,5] := by
  have b0 : a 22 ≠ 8 := exclude [0,1] (edge r65) (a 22) (a 23) 8 d23 c65 (by decide +kernel)
  have t0 : a 22 ∈ [0,6] := remove (a 22) 8 [0,6,8] d22 b0
  have b1 : a 31 ≠ 9 := exclude [0,1] (fun u v => edge r67 v u) (a 31) (a 23) 9 d23 c67 (by decide +kernel)
  have t1 : a 31 ∈ [0,2] := remove (a 31) 9 [0,2,9] d31 b1
  have b2 : a 24 ≠ 4 := exclude [0,1,2,3] (edge r68) (a 24) (a 25) 4 d25 c68 (by decide +kernel)
  have t2 : a 24 ∈ [0,2,8] := remove (a 24) 4 [0,2,4,8] d24 b2
  have b3 : a 24 ≠ 8 := exclude [0,1,2,3] (edge r68) (a 24) (a 25) 8 d25 c68 (by decide +kernel)
  have t3 : a 24 ∈ [0,2] := remove (a 24) 8 [0,2,8] t2 b3
  have b4 : a 25 ≠ 1 := exclude [0,2] (edge r72) (a 25) (a 29) 1 d29 c72 (by decide +kernel)
  have t4 : a 25 ∈ [0,2,3] := remove (a 25) 1 [0,1,2,3] d25 b4
  have b5 : a 25 ≠ 3 := exclude [0,2] (edge r72) (a 25) (a 29) 3 d29 c72 (by decide +kernel)
  have t5 : a 25 ∈ [0,2] := remove (a 25) 3 [0,2,3] t4 b5
  have b6 : a 26 ≠ 9 := exclude [0,2,4,5] (edge r73) (a 26) (a 27) 9 d27 c73 (by decide +kernel)
  have t6 : a 26 ∈ [0,2,21] := remove (a 26) 9 [0,2,9,21] d26 b6
  have b7 : a 26 ≠ 21 := exclude [0,2,4,5] (edge r73) (a 26) (a 27) 21 d27 c73 (by decide +kernel)
  have t7 : a 26 ∈ [0,2] := remove (a 26) 21 [0,2,21] t6 b7
  have b8 : a 27 ≠ 4 := exclude [0,2] (fun u v => edge r73 v u) (a 27) (a 26) 4 t7 c73 (by decide +kernel)
  have t8 : a 27 ∈ [0,2,5] := remove (a 27) 4 [0,2,4,5] d27 b8
  have b9 : a 27 ≠ 5 := exclude [0,2] (fun u v => edge r73 v u) (a 27) (a 26) 5 t7 c73 (by decide +kernel)
  have t9 : a 27 ∈ [0,2] := remove (a 27) 5 [0,2,5] t8 b9
  have b10 : a 30 ≠ 2 := exclude [0,2] (fun u v => edge r74 v u) (a 30) (a 26) 2 t7 c74 (by decide +kernel)
  have t10 : a 30 ∈ [0,1] := remove (a 30) 2 [0,1,2] d30 b10
  have b11 : a 4 ≠ 1 := exclude [0,4] (edge r18) (a 4) (a 12) 1 d12 c18 (by decide +kernel)
  have t11 : a 4 ∈ [0,2] := remove (a 4) 1 [0,1,2] d4 b11
  have b12 : a 4 ≠ 2 := exclude [0,4] (edge r18) (a 4) (a 12) 2 d12 c18 (by decide +kernel)
  have t12 : a 4 ∈ [0] := remove (a 4) 2 [0,2] t11 b12
  have b13 : a 5 ≠ 1 := exclude [0,1] (edge r21) (a 5) (a 13) 1 d13 c21 (by decide +kernel)
  have t13 : a 5 ∈ [0,2] := remove (a 5) 1 [0,1,2] d5 b13
  have b14 : a 5 ≠ 2 := exclude [0,1] (edge r21) (a 5) (a 13) 2 d13 c21 (by decide +kernel)
  have t14 : a 5 ∈ [0] := remove (a 5) 2 [0,2] t13 b14
  have b15 : a 6 ≠ 2 := exclude [0,6] (edge r24) (a 6) (a 14) 2 d14 c24 (by decide +kernel)
  have t15 : a 6 ∈ [0,3,5] := remove (a 6) 2 [0,2,3,5] d6 b15
  exact And.intro t0 (And.intro t1 (And.intro t3 (And.intro t5 (And.intro t7 (And.intro t9 (And.intro t10 (And.intro t12 (And.intro t14 (t15)))))))))

theorem chunk17 (a : Nat → Nat)
    (d6 : a 6 ∈ [0,3,5])
    (d14 : a 14 ∈ [0,6])
    (c24 : edge r24 (a 6) (a 14)=true)
    : a 6 ∈ [0,3] := by
  have b0 : a 6 ≠ 5 := exclude [0,6] (edge r24) (a 6) (a 14) 5 d14 c24 (by decide +kernel)
  have t0 : a 6 ∈ [0,3] := remove (a 6) 5 [0,3,5] d6 b0
  exact t0

theorem chunk18 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,1])
    (d2 : a 2 ∈ [0])
    (d6 : a 6 ∈ [0,3])
    (d10 : a 10 ∈ [0,6])
    (d18 : a 18 ∈ [0,6])
    (d7 : a 7 ∈ [0,3])
    (d11 : a 11 ∈ [0,6])
    (d14 : a 14 ∈ [0,6])
    (d22 : a 22 ∈ [0,6])
    (d8 : a 8 ∈ [0,2])
    (d12 : a 12 ∈ [0,4])
    (d24 : a 24 ∈ [0,2])
    (d9 : a 9 ∈ [0,2])
    (d13 : a 13 ∈ [0,1])
    (d25 : a 25 ∈ [0,2])
    (d26 : a 26 ∈ [0,2])
    (d15 : a 15 ∈ [0,3])
    (c9 : edge r9 (a 2) (a 3)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    (c12 : edge r12 (a 2) (a 18)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c30 : edge r30 (a 8) (a 12)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c33 : edge r33 (a 9) (a 13)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    : a 3 ∈ [0] ∧ a 6 ∈ [0] ∧ a 10 ∈ [0] ∧ a 18 ∈ [0] ∧ a 7 ∈ [0] ∧ a 11 ∈ [0] ∧ a 14 ∈ [0] ∧ a 22 ∈ [0] ∧ a 8 ∈ [0] ∧ a 12 ∈ [0] ∧ a 24 ∈ [0] ∧ a 9 ∈ [0] ∧ a 13 ∈ [0] ∧ a 25 ∈ [0] ∧ a 26 ∈ [0] ∧ a 15 ∈ [0] := by
  have b0 : a 3 ≠ 1 := exclude [0] (fun u v => edge r9 v u) (a 3) (a 2) 1 d2 c9 (by decide +kernel)
  have t0 : a 3 ∈ [0] := remove (a 3) 1 [0,1] d3 b0
  have b1 : a 6 ≠ 3 := exclude [0] (fun u v => edge r10 v u) (a 6) (a 2) 3 d2 c10 (by decide +kernel)
  have t1 : a 6 ∈ [0] := remove (a 6) 3 [0,3] d6 b1
  have b2 : a 10 ≠ 6 := exclude [0] (fun u v => edge r11 v u) (a 10) (a 2) 6 d2 c11 (by decide +kernel)
  have t2 : a 10 ∈ [0] := remove (a 10) 6 [0,6] d10 b2
  have b3 : a 18 ≠ 6 := exclude [0] (fun u v => edge r12 v u) (a 18) (a 2) 6 d2 c12 (by decide +kernel)
  have t3 : a 18 ∈ [0] := remove (a 18) 6 [0,6] d18 b3
  have b4 : a 7 ≠ 3 := exclude [0] (fun u v => edge r13 v u) (a 7) (a 3) 3 t0 c13 (by decide +kernel)
  have t4 : a 7 ∈ [0] := remove (a 7) 3 [0,3] d7 b4
  have b5 : a 11 ≠ 6 := exclude [0] (fun u v => edge r14 v u) (a 11) (a 3) 6 t0 c14 (by decide +kernel)
  have t5 : a 11 ∈ [0] := remove (a 11) 6 [0,6] d11 b5
  have b6 : a 14 ≠ 6 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 6 t1 c24 (by decide +kernel)
  have t6 : a 14 ∈ [0] := remove (a 14) 6 [0,6] d14 b6
  have b7 : a 22 ≠ 6 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 6 t1 c25 (by decide +kernel)
  have t7 : a 22 ∈ [0] := remove (a 22) 6 [0,6] d22 b7
  have b8 : a 8 ≠ 2 := exclude [0] (edge r29) (a 8) (a 10) 2 t2 c29 (by decide +kernel)
  have t8 : a 8 ∈ [0] := remove (a 8) 2 [0,2] d8 b8
  have b9 : a 12 ≠ 4 := exclude [0] (fun u v => edge r30 v u) (a 12) (a 8) 4 t8 c30 (by decide +kernel)
  have t9 : a 12 ∈ [0] := remove (a 12) 4 [0,4] d12 b9
  have b10 : a 24 ≠ 2 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 2 t8 c31 (by decide +kernel)
  have t10 : a 24 ∈ [0] := remove (a 24) 2 [0,2] d24 b10
  have b11 : a 9 ≠ 2 := exclude [0] (edge r32) (a 9) (a 11) 2 t5 c32 (by decide +kernel)
  have t11 : a 9 ∈ [0] := remove (a 9) 2 [0,2] d9 b11
  have b12 : a 13 ≠ 1 := exclude [0] (fun u v => edge r33 v u) (a 13) (a 9) 1 t11 c33 (by decide +kernel)
  have t12 : a 13 ∈ [0] := remove (a 13) 1 [0,1] d13 b12
  have b13 : a 25 ≠ 2 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 2 t11 c34 (by decide +kernel)
  have t13 : a 25 ∈ [0] := remove (a 25) 2 [0,2] d25 b13
  have b14 : a 26 ≠ 2 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 2 t2 c37 (by decide +kernel)
  have t14 : a 26 ∈ [0] := remove (a 26) 2 [0,2] d26 b14
  have b15 : a 15 ≠ 3 := exclude [0] (fun u v => edge r38 v u) (a 15) (a 11) 3 t5 c38 (by decide +kernel)
  have t15 : a 15 ∈ [0] := remove (a 15) 3 [0,3] d15 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk19 (a : Nat → Nat)
    (d27 : a 27 ∈ [0,2])
    (d11 : a 11 ∈ [0])
    (d28 : a 28 ∈ [0,3])
    (d12 : a 12 ∈ [0])
    (d29 : a 29 ∈ [0,2])
    (d13 : a 13 ∈ [0])
    (d16 : a 16 ∈ [0,1])
    (d18 : a 18 ∈ [0])
    (d20 : a 20 ∈ [0,2])
    (d17 : a 17 ∈ [0,1])
    (d25 : a 25 ∈ [0])
    (d21 : a 21 ∈ [0,3])
    (d23 : a 23 ∈ [0,1])
    (d30 : a 30 ∈ [0,1])
    (d22 : a 22 ∈ [0])
    (d31 : a 31 ∈ [0,2])
    (c39 : edge r39 (a 11) (a 27)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    (c49 : edge r49 (a 16) (a 18)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    (c54 : edge r54 (a 17) (a 25)=true)
    (c60 : edge r60 (a 20) (a 21)=true)
    (c63 : edge r63 (a 21) (a 23)=true)
    (c66 : edge r66 (a 22) (a 30)=true)
    (c75 : edge r75 (a 27) (a 31)=true)
    : a 27 ∈ [0] ∧ a 28 ∈ [0] ∧ a 29 ∈ [0] ∧ a 16 ∈ [0] ∧ a 20 ∈ [0] ∧ a 17 ∈ [0] ∧ a 21 ∈ [0] ∧ a 23 ∈ [0] ∧ a 30 ∈ [0] ∧ a 31 ∈ [0] := by
  have b0 : a 27 ≠ 2 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 2 d11 c39 (by decide +kernel)
  have t0 : a 27 ∈ [0] := remove (a 27) 2 [0,2] d27 b0
  have b1 : a 28 ≠ 3 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 3 d12 c42 (by decide +kernel)
  have t1 : a 28 ∈ [0] := remove (a 28) 3 [0,3] d28 b1
  have b2 : a 29 ≠ 2 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 2 d13 c44 (by decide +kernel)
  have t2 : a 29 ∈ [0] := remove (a 29) 2 [0,2] d29 b2
  have b3 : a 16 ≠ 1 := exclude [0] (edge r49) (a 16) (a 18) 1 d18 c49 (by decide +kernel)
  have t3 : a 16 ∈ [0] := remove (a 16) 1 [0,1] d16 b3
  have b4 : a 20 ≠ 2 := exclude [0] (fun u v => edge r50 v u) (a 20) (a 16) 2 t3 c50 (by decide +kernel)
  have t4 : a 20 ∈ [0] := remove (a 20) 2 [0,2] d20 b4
  have b5 : a 17 ≠ 1 := exclude [0] (edge r54) (a 17) (a 25) 1 d25 c54 (by decide +kernel)
  have t5 : a 17 ∈ [0] := remove (a 17) 1 [0,1] d17 b5
  have b6 : a 21 ≠ 3 := exclude [0] (fun u v => edge r60 v u) (a 21) (a 20) 3 t4 c60 (by decide +kernel)
  have t6 : a 21 ∈ [0] := remove (a 21) 3 [0,3] d21 b6
  have b7 : a 23 ≠ 1 := exclude [0] (fun u v => edge r63 v u) (a 23) (a 21) 1 t6 c63 (by decide +kernel)
  have t7 : a 23 ∈ [0] := remove (a 23) 1 [0,1] d23 b7
  have b8 : a 30 ≠ 1 := exclude [0] (fun u v => edge r66 v u) (a 30) (a 22) 1 d22 c66 (by decide +kernel)
  have t8 : a 30 ∈ [0] := remove (a 30) 1 [0,1] d30 b8
  have b9 : a 31 ≠ 2 := exclude [0] (fun u v => edge r75 v u) (a 31) (a 27) 2 t0 c75 (by decide +kernel)
  have t9 : a 31 ∈ [0] := remove (a 31) 2 [0,2] d31 b9
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (t9)))))))))

#print axioms chunk16
#print axioms chunk17
#print axioms chunk18
#print axioms chunk19
end PartitionCover205_188
