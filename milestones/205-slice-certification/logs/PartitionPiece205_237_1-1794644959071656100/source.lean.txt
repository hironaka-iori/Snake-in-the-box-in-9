import PartitionData205_237
namespace PartitionCover205_237
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,1])
    (d1 : a 1 ∈ [0])
    (d8 : a 8 ∈ [0,2])
    (d15 : a 15 ∈ [0,2])
    (d30 : a 30 ∈ [0,1])
    (d2 : a 2 ∈ [0,1])
    (d5 : a 5 ∈ [0,2])
    (d9 : a 9 ∈ [0,1])
    (d16 : a 16 ∈ [0,1])
    (d31 : a 31 ∈ [0,1])
    (d4 : a 4 ∈ [0,1])
    (d10 : a 10 ∈ [0,1])
    (d18 : a 18 ∈ [0,2])
    (d34 : a 34 ∈ [0,1])
    (d7 : a 7 ∈ [0,1])
    (d21 : a 21 ∈ [0,1])
    (d36 : a 36 ∈ [0,2])
    (c6 : edge r6 (a 1) (a 3)=true)
    (c7 : edge r7 (a 1) (a 8)=true)
    (c8 : edge r8 (a 1) (a 15)=true)
    (c9 : edge r9 (a 1) (a 30)=true)
    (c10 : edge r10 (a 2) (a 3)=true)
    (c11 : edge r11 (a 2) (a 5)=true)
    (c12 : edge r12 (a 2) (a 9)=true)
    (c13 : edge r13 (a 2) (a 16)=true)
    (c14 : edge r14 (a 2) (a 31)=true)
    (c18 : edge r18 (a 4) (a 5)=true)
    (c19 : edge r19 (a 4) (a 10)=true)
    (c20 : edge r20 (a 4) (a 18)=true)
    (c23 : edge r23 (a 5) (a 34)=true)
    (c27 : edge r27 (a 7) (a 8)=true)
    (c30 : edge r30 (a 7) (a 21)=true)
    (c31 : edge r31 (a 7) (a 36)=true)
    : a 3 ∈ [0] ∧ a 8 ∈ [0] ∧ a 15 ∈ [0] ∧ a 30 ∈ [0] ∧ a 2 ∈ [0] ∧ a 5 ∈ [0] ∧ a 9 ∈ [0] ∧ a 16 ∈ [0] ∧ a 31 ∈ [0] ∧ a 4 ∈ [0] ∧ a 10 ∈ [0] ∧ a 18 ∈ [0] ∧ a 34 ∈ [0] ∧ a 7 ∈ [0] ∧ a 21 ∈ [0] ∧ a 36 ∈ [0] := by
  have b0 : a 3 ≠ 1 := exclude [0] (fun u v => edge r6 v u) (a 3) (a 1) 1 d1 c6 (by decide +kernel)
  have t0 : a 3 ∈ [0] := remove (a 3) 1 [0,1] d3 b0
  have b1 : a 8 ≠ 2 := exclude [0] (fun u v => edge r7 v u) (a 8) (a 1) 2 d1 c7 (by decide +kernel)
  have t1 : a 8 ∈ [0] := remove (a 8) 2 [0,2] d8 b1
  have b2 : a 15 ≠ 2 := exclude [0] (fun u v => edge r8 v u) (a 15) (a 1) 2 d1 c8 (by decide +kernel)
  have t2 : a 15 ∈ [0] := remove (a 15) 2 [0,2] d15 b2
  have b3 : a 30 ≠ 1 := exclude [0] (fun u v => edge r9 v u) (a 30) (a 1) 1 d1 c9 (by decide +kernel)
  have t3 : a 30 ∈ [0] := remove (a 30) 1 [0,1] d30 b3
  have b4 : a 2 ≠ 1 := exclude [0] (edge r10) (a 2) (a 3) 1 t0 c10 (by decide +kernel)
  have t4 : a 2 ∈ [0] := remove (a 2) 1 [0,1] d2 b4
  have b5 : a 5 ≠ 2 := exclude [0] (fun u v => edge r11 v u) (a 5) (a 2) 2 t4 c11 (by decide +kernel)
  have t5 : a 5 ∈ [0] := remove (a 5) 2 [0,2] d5 b5
  have b6 : a 9 ≠ 1 := exclude [0] (fun u v => edge r12 v u) (a 9) (a 2) 1 t4 c12 (by decide +kernel)
  have t6 : a 9 ∈ [0] := remove (a 9) 1 [0,1] d9 b6
  have b7 : a 16 ≠ 1 := exclude [0] (fun u v => edge r13 v u) (a 16) (a 2) 1 t4 c13 (by decide +kernel)
  have t7 : a 16 ∈ [0] := remove (a 16) 1 [0,1] d16 b7
  have b8 : a 31 ≠ 1 := exclude [0] (fun u v => edge r14 v u) (a 31) (a 2) 1 t4 c14 (by decide +kernel)
  have t8 : a 31 ∈ [0] := remove (a 31) 1 [0,1] d31 b8
  have b9 : a 4 ≠ 1 := exclude [0] (edge r18) (a 4) (a 5) 1 t5 c18 (by decide +kernel)
  have t9 : a 4 ∈ [0] := remove (a 4) 1 [0,1] d4 b9
  have b10 : a 10 ≠ 1 := exclude [0] (fun u v => edge r19 v u) (a 10) (a 4) 1 t9 c19 (by decide +kernel)
  have t10 : a 10 ∈ [0] := remove (a 10) 1 [0,1] d10 b10
  have b11 : a 18 ≠ 2 := exclude [0] (fun u v => edge r20 v u) (a 18) (a 4) 2 t9 c20 (by decide +kernel)
  have t11 : a 18 ∈ [0] := remove (a 18) 2 [0,2] d18 b11
  have b12 : a 34 ≠ 1 := exclude [0] (fun u v => edge r23 v u) (a 34) (a 5) 1 t5 c23 (by decide +kernel)
  have t12 : a 34 ∈ [0] := remove (a 34) 1 [0,1] d34 b12
  have b13 : a 7 ≠ 1 := exclude [0] (edge r27) (a 7) (a 8) 1 t1 c27 (by decide +kernel)
  have t13 : a 7 ∈ [0] := remove (a 7) 1 [0,1] d7 b13
  have b14 : a 21 ≠ 1 := exclude [0] (fun u v => edge r30 v u) (a 21) (a 7) 1 t13 c30 (by decide +kernel)
  have t14 : a 21 ∈ [0] := remove (a 21) 1 [0,1] d21 b14
  have b15 : a 36 ≠ 2 := exclude [0] (fun u v => edge r31 v u) (a 36) (a 7) 2 t13 c31 (by decide +kernel)
  have t15 : a 36 ∈ [0] := remove (a 36) 2 [0,2] d36 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk5 (a : Nat → Nat)
    (d23 : a 23 ∈ [0,1])
    (d9 : a 9 ∈ [0])
    (d38 : a 38 ∈ [0,1])
    (d40 : a 40 ∈ [0,1])
    (d10 : a 10 ∈ [0])
    (d14 : a 14 ∈ [0,1])
    (d15 : a 15 ∈ [0])
    (d44 : a 44 ∈ [0,2])
    (d46 : a 46 ∈ [0,1])
    (d16 : a 16 ∈ [0])
    (d24 : a 24 ∈ [0,2])
    (d27 : a 27 ∈ [0,1])
    (d52 : a 52 ∈ [0,1])
    (d28 : a 28 ∈ [0,1])
    (d57 : a 57 ∈ [0,1])
    (d29 : a 29 ∈ [0,2])
    (d30 : a 30 ∈ [0])
    (d33 : a 33 ∈ [0,1])
    (d48 : a 48 ∈ [0,1])
    (d42 : a 42 ∈ [0,1])
    (d34 : a 34 ∈ [0])
    (d49 : a 49 ∈ [0,2])
    (c36 : edge r36 (a 9) (a 23)=true)
    (c37 : edge r37 (a 9) (a 38)=true)
    (c41 : edge r41 (a 10) (a 40)=true)
    (c50 : edge r50 (a 14) (a 15)=true)
    (c54 : edge r54 (a 14) (a 44)=true)
    (c61 : edge r61 (a 16) (a 46)=true)
    (c78 : edge r78 (a 23) (a 24)=true)
    (c79 : edge r79 (a 23) (a 27)=true)
    (c80 : edge r80 (a 23) (a 52)=true)
    (c81 : edge r81 (a 24) (a 28)=true)
    (c90 : edge r90 (a 28) (a 57)=true)
    (c91 : edge r91 (a 29) (a 30)=true)
    (c96 : edge r96 (a 30) (a 33)=true)
    (c108 : edge r108 (a 33) (a 48)=true)
    (c110 : edge r110 (a 34) (a 42)=true)
    (c111 : edge r111 (a 34) (a 49)=true)
    : a 23 ∈ [0] ∧ a 38 ∈ [0] ∧ a 40 ∈ [0] ∧ a 14 ∈ [0] ∧ a 44 ∈ [0] ∧ a 46 ∈ [0] ∧ a 24 ∈ [0] ∧ a 27 ∈ [0] ∧ a 52 ∈ [0] ∧ a 28 ∈ [0] ∧ a 57 ∈ [0] ∧ a 29 ∈ [0] ∧ a 33 ∈ [0] ∧ a 48 ∈ [0] ∧ a 42 ∈ [0] ∧ a 49 ∈ [0] := by
  have b0 : a 23 ≠ 1 := exclude [0] (fun u v => edge r36 v u) (a 23) (a 9) 1 d9 c36 (by decide +kernel)
  have t0 : a 23 ∈ [0] := remove (a 23) 1 [0,1] d23 b0
  have b1 : a 38 ≠ 1 := exclude [0] (fun u v => edge r37 v u) (a 38) (a 9) 1 d9 c37 (by decide +kernel)
  have t1 : a 38 ∈ [0] := remove (a 38) 1 [0,1] d38 b1
  have b2 : a 40 ≠ 1 := exclude [0] (fun u v => edge r41 v u) (a 40) (a 10) 1 d10 c41 (by decide +kernel)
  have t2 : a 40 ∈ [0] := remove (a 40) 1 [0,1] d40 b2
  have b3 : a 14 ≠ 1 := exclude [0] (edge r50) (a 14) (a 15) 1 d15 c50 (by decide +kernel)
  have t3 : a 14 ∈ [0] := remove (a 14) 1 [0,1] d14 b3
  have b4 : a 44 ≠ 2 := exclude [0] (fun u v => edge r54 v u) (a 44) (a 14) 2 t3 c54 (by decide +kernel)
  have t4 : a 44 ∈ [0] := remove (a 44) 2 [0,2] d44 b4
  have b5 : a 46 ≠ 1 := exclude [0] (fun u v => edge r61 v u) (a 46) (a 16) 1 d16 c61 (by decide +kernel)
  have t5 : a 46 ∈ [0] := remove (a 46) 1 [0,1] d46 b5
  have b6 : a 24 ≠ 2 := exclude [0] (fun u v => edge r78 v u) (a 24) (a 23) 2 t0 c78 (by decide +kernel)
  have t6 : a 24 ∈ [0] := remove (a 24) 2 [0,2] d24 b6
  have b7 : a 27 ≠ 1 := exclude [0] (fun u v => edge r79 v u) (a 27) (a 23) 1 t0 c79 (by decide +kernel)
  have t7 : a 27 ∈ [0] := remove (a 27) 1 [0,1] d27 b7
  have b8 : a 52 ≠ 1 := exclude [0] (fun u v => edge r80 v u) (a 52) (a 23) 1 t0 c80 (by decide +kernel)
  have t8 : a 52 ∈ [0] := remove (a 52) 1 [0,1] d52 b8
  have b9 : a 28 ≠ 1 := exclude [0] (fun u v => edge r81 v u) (a 28) (a 24) 1 t6 c81 (by decide +kernel)
  have t9 : a 28 ∈ [0] := remove (a 28) 1 [0,1] d28 b9
  have b10 : a 57 ≠ 1 := exclude [0] (fun u v => edge r90 v u) (a 57) (a 28) 1 t9 c90 (by decide +kernel)
  have t10 : a 57 ∈ [0] := remove (a 57) 1 [0,1] d57 b10
  have b11 : a 29 ≠ 2 := exclude [0] (edge r91) (a 29) (a 30) 2 d30 c91 (by decide +kernel)
  have t11 : a 29 ∈ [0] := remove (a 29) 2 [0,2] d29 b11
  have b12 : a 33 ≠ 1 := exclude [0] (fun u v => edge r96 v u) (a 33) (a 30) 1 d30 c96 (by decide +kernel)
  have t12 : a 33 ∈ [0] := remove (a 33) 1 [0,1] d33 b12
  have b13 : a 48 ≠ 1 := exclude [0] (fun u v => edge r108 v u) (a 48) (a 33) 1 t12 c108 (by decide +kernel)
  have t13 : a 48 ∈ [0] := remove (a 48) 1 [0,1] d48 b13
  have b14 : a 42 ≠ 1 := exclude [0] (fun u v => edge r110 v u) (a 42) (a 34) 1 d34 c110 (by decide +kernel)
  have t14 : a 42 ∈ [0] := remove (a 42) 1 [0,1] d42 b14
  have b15 : a 49 ≠ 2 := exclude [0] (fun u v => edge r111 v u) (a 49) (a 34) 2 d34 c111 (by decide +kernel)
  have t15 : a 49 ∈ [0] := remove (a 49) 2 [0,2] d49 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk6 (a : Nat → Nat)
    (d39 : a 39 ∈ [0,2])
    (d38 : a 38 ∈ [0])
    (d43 : a 43 ∈ [0,1])
    (d47 : a 47 ∈ [0,1])
    (d46 : a 46 ∈ [0])
    (d55 : a 55 ∈ [0,1])
    (d48 : a 48 ∈ [0])
    (d51 : a 51 ∈ [0,2])
    (d13 : a 13 ∈ [0,1])
    (d28 : a 28 ∈ [0])
    (c48 : edge r48 (a 13) (a 28)=true)
    (c120 : edge r120 (a 38) (a 39)=true)
    (c123 : edge r123 (a 39) (a 43)=true)
    (c138 : edge r138 (a 46) (a 47)=true)
    (c144 : edge r144 (a 48) (a 55)=true)
    (c149 : edge r149 (a 51) (a 55)=true)
    : a 39 ∈ [0] ∧ a 43 ∈ [0] ∧ a 47 ∈ [0] ∧ a 55 ∈ [0] ∧ a 51 ∈ [0] ∧ a 13 ∈ [0] := by
  have b0 : a 39 ≠ 2 := exclude [0] (fun u v => edge r120 v u) (a 39) (a 38) 2 d38 c120 (by decide +kernel)
  have t0 : a 39 ∈ [0] := remove (a 39) 2 [0,2] d39 b0
  have b1 : a 43 ≠ 1 := exclude [0] (fun u v => edge r123 v u) (a 43) (a 39) 1 t0 c123 (by decide +kernel)
  have t1 : a 43 ∈ [0] := remove (a 43) 1 [0,1] d43 b1
  have b2 : a 47 ≠ 1 := exclude [0] (fun u v => edge r138 v u) (a 47) (a 46) 1 d46 c138 (by decide +kernel)
  have t2 : a 47 ∈ [0] := remove (a 47) 1 [0,1] d47 b2
  have b3 : a 55 ≠ 1 := exclude [0] (fun u v => edge r144 v u) (a 55) (a 48) 1 d48 c144 (by decide +kernel)
  have t3 : a 55 ∈ [0] := remove (a 55) 1 [0,1] d55 b3
  have b4 : a 51 ≠ 2 := exclude [0] (edge r149) (a 51) (a 55) 2 t3 c149 (by decide +kernel)
  have t4 : a 51 ∈ [0] := remove (a 51) 2 [0,2] d51 b4
  have b5 : a 13 ≠ 1 := exclude [0] (edge r48) (a 13) (a 28) 1 d28 c48 (by decide +kernel)
  have t5 : a 13 ∈ [0] := remove (a 13) 1 [0,1] d13 b5
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (t5)))))

theorem chunk7 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,1])
    (d1 : a 1 ∈ [1])
    (d8 : a 8 ∈ [0,2])
    (d15 : a 15 ∈ [0,2])
    (d30 : a 30 ∈ [0,1])
    (d2 : a 2 ∈ [0,1])
    (d5 : a 5 ∈ [0,2])
    (d9 : a 9 ∈ [0,1])
    (d16 : a 16 ∈ [0,1])
    (d31 : a 31 ∈ [0,1])
    (d4 : a 4 ∈ [0,1])
    (d10 : a 10 ∈ [0,1])
    (d18 : a 18 ∈ [0,2])
    (d34 : a 34 ∈ [0,1])
    (d7 : a 7 ∈ [0,1])
    (d21 : a 21 ∈ [0,1])
    (d36 : a 36 ∈ [0,2])
    (c6 : edge r6 (a 1) (a 3)=true)
    (c7 : edge r7 (a 1) (a 8)=true)
    (c8 : edge r8 (a 1) (a 15)=true)
    (c9 : edge r9 (a 1) (a 30)=true)
    (c10 : edge r10 (a 2) (a 3)=true)
    (c11 : edge r11 (a 2) (a 5)=true)
    (c12 : edge r12 (a 2) (a 9)=true)
    (c13 : edge r13 (a 2) (a 16)=true)
    (c14 : edge r14 (a 2) (a 31)=true)
    (c18 : edge r18 (a 4) (a 5)=true)
    (c19 : edge r19 (a 4) (a 10)=true)
    (c20 : edge r20 (a 4) (a 18)=true)
    (c23 : edge r23 (a 5) (a 34)=true)
    (c27 : edge r27 (a 7) (a 8)=true)
    (c30 : edge r30 (a 7) (a 21)=true)
    (c31 : edge r31 (a 7) (a 36)=true)
    : a 3 ∈ [1] ∧ a 8 ∈ [2] ∧ a 15 ∈ [2] ∧ a 30 ∈ [1] ∧ a 2 ∈ [1] ∧ a 5 ∈ [2] ∧ a 9 ∈ [1] ∧ a 16 ∈ [1] ∧ a 31 ∈ [1] ∧ a 4 ∈ [1] ∧ a 10 ∈ [1] ∧ a 18 ∈ [2] ∧ a 34 ∈ [1] ∧ a 7 ∈ [1] ∧ a 21 ∈ [1] ∧ a 36 ∈ [2] := by
  have b0 : a 3 ≠ 0 := exclude [1] (fun u v => edge r6 v u) (a 3) (a 1) 0 d1 c6 (by decide +kernel)
  have t0 : a 3 ∈ [1] := remove (a 3) 0 [0,1] d3 b0
  have b1 : a 8 ≠ 0 := exclude [1] (fun u v => edge r7 v u) (a 8) (a 1) 0 d1 c7 (by decide +kernel)
  have t1 : a 8 ∈ [2] := remove (a 8) 0 [0,2] d8 b1
  have b2 : a 15 ≠ 0 := exclude [1] (fun u v => edge r8 v u) (a 15) (a 1) 0 d1 c8 (by decide +kernel)
  have t2 : a 15 ∈ [2] := remove (a 15) 0 [0,2] d15 b2
  have b3 : a 30 ≠ 0 := exclude [1] (fun u v => edge r9 v u) (a 30) (a 1) 0 d1 c9 (by decide +kernel)
  have t3 : a 30 ∈ [1] := remove (a 30) 0 [0,1] d30 b3
  have b4 : a 2 ≠ 0 := exclude [1] (edge r10) (a 2) (a 3) 0 t0 c10 (by decide +kernel)
  have t4 : a 2 ∈ [1] := remove (a 2) 0 [0,1] d2 b4
  have b5 : a 5 ≠ 0 := exclude [1] (fun u v => edge r11 v u) (a 5) (a 2) 0 t4 c11 (by decide +kernel)
  have t5 : a 5 ∈ [2] := remove (a 5) 0 [0,2] d5 b5
  have b6 : a 9 ≠ 0 := exclude [1] (fun u v => edge r12 v u) (a 9) (a 2) 0 t4 c12 (by decide +kernel)
  have t6 : a 9 ∈ [1] := remove (a 9) 0 [0,1] d9 b6
  have b7 : a 16 ≠ 0 := exclude [1] (fun u v => edge r13 v u) (a 16) (a 2) 0 t4 c13 (by decide +kernel)
  have t7 : a 16 ∈ [1] := remove (a 16) 0 [0,1] d16 b7
  have b8 : a 31 ≠ 0 := exclude [1] (fun u v => edge r14 v u) (a 31) (a 2) 0 t4 c14 (by decide +kernel)
  have t8 : a 31 ∈ [1] := remove (a 31) 0 [0,1] d31 b8
  have b9 : a 4 ≠ 0 := exclude [2] (edge r18) (a 4) (a 5) 0 t5 c18 (by decide +kernel)
  have t9 : a 4 ∈ [1] := remove (a 4) 0 [0,1] d4 b9
  have b10 : a 10 ≠ 0 := exclude [1] (fun u v => edge r19 v u) (a 10) (a 4) 0 t9 c19 (by decide +kernel)
  have t10 : a 10 ∈ [1] := remove (a 10) 0 [0,1] d10 b10
  have b11 : a 18 ≠ 0 := exclude [1] (fun u v => edge r20 v u) (a 18) (a 4) 0 t9 c20 (by decide +kernel)
  have t11 : a 18 ∈ [2] := remove (a 18) 0 [0,2] d18 b11
  have b12 : a 34 ≠ 0 := exclude [2] (fun u v => edge r23 v u) (a 34) (a 5) 0 t5 c23 (by decide +kernel)
  have t12 : a 34 ∈ [1] := remove (a 34) 0 [0,1] d34 b12
  have b13 : a 7 ≠ 0 := exclude [2] (edge r27) (a 7) (a 8) 0 t1 c27 (by decide +kernel)
  have t13 : a 7 ∈ [1] := remove (a 7) 0 [0,1] d7 b13
  have b14 : a 21 ≠ 0 := exclude [1] (fun u v => edge r30 v u) (a 21) (a 7) 0 t13 c30 (by decide +kernel)
  have t14 : a 21 ∈ [1] := remove (a 21) 0 [0,1] d21 b14
  have b15 : a 36 ≠ 0 := exclude [1] (fun u v => edge r31 v u) (a 36) (a 7) 0 t13 c31 (by decide +kernel)
  have t15 : a 36 ∈ [2] := remove (a 36) 0 [0,2] d36 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_237
