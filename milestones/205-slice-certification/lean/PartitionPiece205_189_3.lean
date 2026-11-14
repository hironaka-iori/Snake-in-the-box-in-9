import PartitionData205_189
namespace PartitionCover205_189
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk12 (a : Nat → Nat)
    (d28 : a 28 ∈ [0,2,6,7,8,9])
    (d20 : a 20 ∈ [0,3])
    (d21 : a 21 ∈ [0,1,2,3])
    (d22 : a 22 ∈ [0])
    (d30 : a 30 ∈ [0,2,4])
    (d24 : a 24 ∈ [0,1,2,3,6,7,8,9])
    (d23 : a 23 ∈ [0])
    (d25 : a 25 ∈ [0,4,8,10])
    (d26 : a 26 ∈ [0,4])
    (d29 : a 29 ∈ [0,1,2,3])
    (c59 : edge r59 (a 20) (a 28)=true)
    (c60 : edge r60 (a 21) (a 22)=true)
    (c62 : edge r62 (a 22) (a 30)=true)
    (c63 : edge r63 (a 23) (a 24)=true)
    (c67 : edge r67 (a 24) (a 28)=true)
    (c68 : edge r68 (a 25) (a 26)=true)
    (c69 : edge r69 (a 25) (a 29)=true)
    : a 28 ∈ [0,6] ∧ a 21 ∈ [0,1] ∧ a 30 ∈ [0,2] ∧ a 24 ∈ [0,6] ∧ a 25 ∈ [0,4] ∧ a 29 ∈ [0,2,3] := by
  have b0 : a 28 ≠ 7 := exclude [0,3] (fun u v => edge r59 v u) (a 28) (a 20) 7 d20 c59 (by decide +kernel)
  have t0 : a 28 ∈ [0,2,6,8,9] := remove (a 28) 7 [0,2,6,7,8,9] d28 b0
  have b1 : a 28 ≠ 9 := exclude [0,3] (fun u v => edge r59 v u) (a 28) (a 20) 9 d20 c59 (by decide +kernel)
  have t1 : a 28 ∈ [0,2,6,8] := remove (a 28) 9 [0,2,6,8,9] t0 b1
  have b2 : a 21 ≠ 2 := exclude [0] (edge r60) (a 21) (a 22) 2 d22 c60 (by decide +kernel)
  have t2 : a 21 ∈ [0,1,3] := remove (a 21) 2 [0,1,2,3] d21 b2
  have b3 : a 21 ≠ 3 := exclude [0] (edge r60) (a 21) (a 22) 3 d22 c60 (by decide +kernel)
  have t3 : a 21 ∈ [0,1] := remove (a 21) 3 [0,1,3] t2 b3
  have b4 : a 30 ≠ 4 := exclude [0] (fun u v => edge r62 v u) (a 30) (a 22) 4 d22 c62 (by decide +kernel)
  have t4 : a 30 ∈ [0,2] := remove (a 30) 4 [0,2,4] d30 b4
  have b5 : a 24 ≠ 2 := exclude [0] (fun u v => edge r63 v u) (a 24) (a 23) 2 d23 c63 (by decide +kernel)
  have t5 : a 24 ∈ [0,1,3,6,7,8,9] := remove (a 24) 2 [0,1,2,3,6,7,8,9] d24 b5
  have b6 : a 24 ≠ 3 := exclude [0] (fun u v => edge r63 v u) (a 24) (a 23) 3 d23 c63 (by decide +kernel)
  have t6 : a 24 ∈ [0,1,6,7,8,9] := remove (a 24) 3 [0,1,3,6,7,8,9] t5 b6
  have b7 : a 24 ≠ 8 := exclude [0] (fun u v => edge r63 v u) (a 24) (a 23) 8 d23 c63 (by decide +kernel)
  have t7 : a 24 ∈ [0,1,6,7,9] := remove (a 24) 8 [0,1,6,7,8,9] t6 b7
  have b8 : a 24 ≠ 9 := exclude [0] (fun u v => edge r63 v u) (a 24) (a 23) 9 d23 c63 (by decide +kernel)
  have t8 : a 24 ∈ [0,1,6,7] := remove (a 24) 9 [0,1,6,7,9] t7 b8
  have b9 : a 24 ≠ 1 := exclude [0,2,6,8] (edge r67) (a 24) (a 28) 1 t1 c67 (by decide +kernel)
  have t9 : a 24 ∈ [0,6,7] := remove (a 24) 1 [0,1,6,7] t8 b9
  have b10 : a 24 ≠ 7 := exclude [0,2,6,8] (edge r67) (a 24) (a 28) 7 t1 c67 (by decide +kernel)
  have t10 : a 24 ∈ [0,6] := remove (a 24) 7 [0,6,7] t9 b10
  have b11 : a 28 ≠ 2 := exclude [0,6] (fun u v => edge r67 v u) (a 28) (a 24) 2 t10 c67 (by decide +kernel)
  have t11 : a 28 ∈ [0,6,8] := remove (a 28) 2 [0,2,6,8] t1 b11
  have b12 : a 28 ≠ 8 := exclude [0,6] (fun u v => edge r67 v u) (a 28) (a 24) 8 t10 c67 (by decide +kernel)
  have t12 : a 28 ∈ [0,6] := remove (a 28) 8 [0,6,8] t11 b12
  have b13 : a 25 ≠ 8 := exclude [0,4] (edge r68) (a 25) (a 26) 8 d26 c68 (by decide +kernel)
  have t13 : a 25 ∈ [0,4,10] := remove (a 25) 8 [0,4,8,10] d25 b13
  have b14 : a 25 ≠ 10 := exclude [0,4] (edge r68) (a 25) (a 26) 10 d26 c68 (by decide +kernel)
  have t14 : a 25 ∈ [0,4] := remove (a 25) 10 [0,4,10] t13 b14
  have b15 : a 29 ≠ 1 := exclude [0,4] (fun u v => edge r69 v u) (a 29) (a 25) 1 t14 c69 (by decide +kernel)
  have t15 : a 29 ∈ [0,2,3] := remove (a 29) 1 [0,1,2,3] d29 b15
  exact And.intro t12 (And.intro t3 (And.intro t4 (And.intro t10 (And.intro t14 (t15)))))

theorem chunk13 (a : Nat → Nat)
    (d29 : a 29 ∈ [0,2,3])
    (d25 : a 25 ∈ [0,4])
    (d13 : a 13 ∈ [0,1,3,4])
    (d28 : a 28 ∈ [0,6])
    (c43 : edge r43 (a 13) (a 28)=true)
    (c69 : edge r69 (a 25) (a 29)=true)
    : a 29 ∈ [0,2] ∧ a 13 ∈ [0,3] := by
  have b0 : a 29 ≠ 3 := exclude [0,4] (fun u v => edge r69 v u) (a 29) (a 25) 3 d25 c69 (by decide +kernel)
  have t0 : a 29 ∈ [0,2] := remove (a 29) 3 [0,2,3] d29 b0
  have b1 : a 13 ≠ 1 := exclude [0,6] (edge r43) (a 13) (a 28) 1 d28 c43 (by decide +kernel)
  have t1 : a 13 ∈ [0,3,4] := remove (a 13) 1 [0,1,3,4] d13 b1
  have b2 : a 13 ≠ 4 := exclude [0,6] (edge r43) (a 13) (a 28) 4 d28 c43 (by decide +kernel)
  have t2 : a 13 ∈ [0,3] := remove (a 13) 4 [0,3,4] t1 b2
  exact And.intro t0 (t2)

theorem chunk14 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,1])
    (d2 : a 2 ∈ [0])
    (d6 : a 6 ∈ [0,3])
    (d10 : a 10 ∈ [0,18])
    (d7 : a 7 ∈ [0,1])
    (d11 : a 11 ∈ [0,19])
    (d4 : a 4 ∈ [0,1])
    (d12 : a 12 ∈ [0,2])
    (d14 : a 14 ∈ [0,18])
    (d21 : a 21 ∈ [0,1])
    (d8 : a 8 ∈ [0,2])
    (d9 : a 9 ∈ [0,2])
    (d13 : a 13 ∈ [0,3])
    (d24 : a 24 ∈ [0,6])
    (d25 : a 25 ∈ [0,4])
    (d15 : a 15 ∈ [0,1])
    (d26 : a 26 ∈ [0,4])
    (c9 : edge r9 (a 2) (a 3)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c23 : edge r23 (a 6) (a 14)=true)
    (c24 : edge r24 (a 6) (a 21)=true)
    (c28 : edge r28 (a 8) (a 10)=true)
    (c31 : edge r31 (a 9) (a 11)=true)
    (c32 : edge r32 (a 9) (a 13)=true)
    (c33 : edge r33 (a 9) (a 24)=true)
    (c36 : edge r36 (a 10) (a 25)=true)
    (c37 : edge r37 (a 11) (a 15)=true)
    (c38 : edge r38 (a 11) (a 26)=true)
    : a 3 ∈ [0] ∧ a 6 ∈ [0] ∧ a 10 ∈ [0] ∧ a 7 ∈ [0] ∧ a 11 ∈ [0] ∧ a 4 ∈ [0] ∧ a 12 ∈ [0] ∧ a 14 ∈ [0] ∧ a 21 ∈ [0] ∧ a 8 ∈ [0] ∧ a 9 ∈ [0] ∧ a 13 ∈ [0] ∧ a 24 ∈ [0] ∧ a 25 ∈ [0] ∧ a 15 ∈ [0] ∧ a 26 ∈ [0] := by
  have b0 : a 3 ≠ 1 := exclude [0] (fun u v => edge r9 v u) (a 3) (a 2) 1 d2 c9 (by decide +kernel)
  have t0 : a 3 ∈ [0] := remove (a 3) 1 [0,1] d3 b0
  have b1 : a 6 ≠ 3 := exclude [0] (fun u v => edge r10 v u) (a 6) (a 2) 3 d2 c10 (by decide +kernel)
  have t1 : a 6 ∈ [0] := remove (a 6) 3 [0,3] d6 b1
  have b2 : a 10 ≠ 18 := exclude [0] (fun u v => edge r11 v u) (a 10) (a 2) 18 d2 c11 (by decide +kernel)
  have t2 : a 10 ∈ [0] := remove (a 10) 18 [0,18] d10 b2
  have b3 : a 7 ≠ 1 := exclude [0] (fun u v => edge r13 v u) (a 7) (a 3) 1 t0 c13 (by decide +kernel)
  have t3 : a 7 ∈ [0] := remove (a 7) 1 [0,1] d7 b3
  have b4 : a 11 ≠ 19 := exclude [0] (fun u v => edge r14 v u) (a 11) (a 3) 19 t0 c14 (by decide +kernel)
  have t4 : a 11 ∈ [0] := remove (a 11) 19 [0,19] d11 b4
  have b5 : a 4 ≠ 1 := exclude [0] (edge r17) (a 4) (a 6) 1 t1 c17 (by decide +kernel)
  have t5 : a 4 ∈ [0] := remove (a 4) 1 [0,1] d4 b5
  have b6 : a 12 ≠ 2 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 2 t5 c18 (by decide +kernel)
  have t6 : a 12 ∈ [0] := remove (a 12) 2 [0,2] d12 b6
  have b7 : a 14 ≠ 18 := exclude [0] (fun u v => edge r23 v u) (a 14) (a 6) 18 t1 c23 (by decide +kernel)
  have t7 : a 14 ∈ [0] := remove (a 14) 18 [0,18] d14 b7
  have b8 : a 21 ≠ 1 := exclude [0] (fun u v => edge r24 v u) (a 21) (a 6) 1 t1 c24 (by decide +kernel)
  have t8 : a 21 ∈ [0] := remove (a 21) 1 [0,1] d21 b8
  have b9 : a 8 ≠ 2 := exclude [0] (edge r28) (a 8) (a 10) 2 t2 c28 (by decide +kernel)
  have t9 : a 8 ∈ [0] := remove (a 8) 2 [0,2] d8 b9
  have b10 : a 9 ≠ 2 := exclude [0] (edge r31) (a 9) (a 11) 2 t4 c31 (by decide +kernel)
  have t10 : a 9 ∈ [0] := remove (a 9) 2 [0,2] d9 b10
  have b11 : a 13 ≠ 3 := exclude [0] (fun u v => edge r32 v u) (a 13) (a 9) 3 t10 c32 (by decide +kernel)
  have t11 : a 13 ∈ [0] := remove (a 13) 3 [0,3] d13 b11
  have b12 : a 24 ≠ 6 := exclude [0] (fun u v => edge r33 v u) (a 24) (a 9) 6 t10 c33 (by decide +kernel)
  have t12 : a 24 ∈ [0] := remove (a 24) 6 [0,6] d24 b12
  have b13 : a 25 ≠ 4 := exclude [0] (fun u v => edge r36 v u) (a 25) (a 10) 4 t2 c36 (by decide +kernel)
  have t13 : a 25 ∈ [0] := remove (a 25) 4 [0,4] d25 b13
  have b14 : a 15 ≠ 1 := exclude [0] (fun u v => edge r37 v u) (a 15) (a 11) 1 t4 c37 (by decide +kernel)
  have t14 : a 15 ∈ [0] := remove (a 15) 1 [0,1] d15 b14
  have b15 : a 26 ≠ 4 := exclude [0] (fun u v => edge r38 v u) (a 26) (a 11) 4 t4 c38 (by decide +kernel)
  have t15 : a 26 ∈ [0] := remove (a 26) 4 [0,4] d26 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk15 (a : Nat → Nat)
    (d27 : a 27 ∈ [0,2])
    (d12 : a 12 ∈ [0])
    (d28 : a 28 ∈ [0,6])
    (d13 : a 13 ∈ [0])
    (d29 : a 29 ∈ [0,2])
    (d14 : a 14 ∈ [0])
    (d20 : a 20 ∈ [0,3])
    (d30 : a 30 ∈ [0,2])
    (d26 : a 26 ∈ [0])
    (d17 : a 17 ∈ [0,3])
    (d16 : a 16 ∈ [0,6])
    (c41 : edge r41 (a 12) (a 27)=true)
    (c43 : edge r43 (a 13) (a 28)=true)
    (c45 : edge r45 (a 14) (a 29)=true)
    (c47 : edge r47 (a 16) (a 17)=true)
    (c51 : edge r51 (a 17) (a 20)=true)
    (c59 : edge r59 (a 20) (a 28)=true)
    (c70 : edge r70 (a 26) (a 30)=true)
    : a 27 ∈ [0] ∧ a 28 ∈ [0] ∧ a 29 ∈ [0] ∧ a 20 ∈ [0] ∧ a 30 ∈ [0] ∧ a 17 ∈ [0] ∧ a 16 ∈ [0] := by
  have b0 : a 27 ≠ 2 := exclude [0] (fun u v => edge r41 v u) (a 27) (a 12) 2 d12 c41 (by decide +kernel)
  have t0 : a 27 ∈ [0] := remove (a 27) 2 [0,2] d27 b0
  have b1 : a 28 ≠ 6 := exclude [0] (fun u v => edge r43 v u) (a 28) (a 13) 6 d13 c43 (by decide +kernel)
  have t1 : a 28 ∈ [0] := remove (a 28) 6 [0,6] d28 b1
  have b2 : a 29 ≠ 2 := exclude [0] (fun u v => edge r45 v u) (a 29) (a 14) 2 d14 c45 (by decide +kernel)
  have t2 : a 29 ∈ [0] := remove (a 29) 2 [0,2] d29 b2
  have b3 : a 20 ≠ 3 := exclude [0] (edge r59) (a 20) (a 28) 3 t1 c59 (by decide +kernel)
  have t3 : a 20 ∈ [0] := remove (a 20) 3 [0,3] d20 b3
  have b4 : a 30 ≠ 2 := exclude [0] (fun u v => edge r70 v u) (a 30) (a 26) 2 d26 c70 (by decide +kernel)
  have t4 : a 30 ∈ [0] := remove (a 30) 2 [0,2] d30 b4
  have b5 : a 17 ≠ 3 := exclude [0] (edge r51) (a 17) (a 20) 3 t3 c51 (by decide +kernel)
  have t5 : a 17 ∈ [0] := remove (a 17) 3 [0,3] d17 b5
  have b6 : a 16 ≠ 6 := exclude [0] (edge r47) (a 16) (a 17) 6 t5 c47 (by decide +kernel)
  have t6 : a 16 ∈ [0] := remove (a 16) 6 [0,6] d16 b6
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (t6))))))

#print axioms chunk12
#print axioms chunk13
#print axioms chunk14
#print axioms chunk15
end PartitionCover205_189
