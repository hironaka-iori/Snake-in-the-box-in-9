import PartitionData205_235
namespace PartitionCover205_235
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d2 : a 2 ∈ [0,1,2,3])
    (d0 : a 0 ∈ [0])
    (d8 : a 8 ∈ [0,1,2,3])
    (d15 : a 15 ∈ [0,1,2,3])
    (d31 : a 31 ∈ [0,1,2,3])
    (d5 : a 5 ∈ [0,1,2,3])
    (d1 : a 1 ∈ [0,1])
    (d6 : a 6 ∈ [0,1])
    (d17 : a 17 ∈ [0,1,2,3])
    (d33 : a 33 ∈ [0,1,2,3])
    (d7 : a 7 ∈ [0,1,2,3])
    (c1 : edge r1 (a 0) (a 2)=true)
    (c3 : edge r3 (a 0) (a 8)=true)
    (c4 : edge r4 (a 0) (a 15)=true)
    (c5 : edge r5 (a 0) (a 31)=true)
    (c7 : edge r7 (a 1) (a 5)=true)
    (c12 : edge r12 (a 2) (a 6)=true)
    (c14 : edge r14 (a 2) (a 17)=true)
    (c15 : edge r15 (a 2) (a 33)=true)
    (c25 : edge r25 (a 5) (a 7)=true)
    : a 2 ∈ [0,1] ∧ a 8 ∈ [0,1] ∧ a 15 ∈ [0,1] ∧ a 31 ∈ [0,2] ∧ a 5 ∈ [0,2] ∧ a 6 ∈ [0] ∧ a 17 ∈ [0,2] ∧ a 33 ∈ [0,1] ∧ a 7 ∈ [0,2,3] := by
  have b0 : a 2 ≠ 2 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 2 d0 c1 (by decide +kernel)
  have t0 : a 2 ∈ [0,1,3] := remove (a 2) 2 [0,1,2,3] d2 b0
  have b1 : a 2 ≠ 3 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 3 d0 c1 (by decide +kernel)
  have t1 : a 2 ∈ [0,1] := remove (a 2) 3 [0,1,3] t0 b1
  have b2 : a 8 ≠ 2 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 2 d0 c3 (by decide +kernel)
  have t2 : a 8 ∈ [0,1,3] := remove (a 8) 2 [0,1,2,3] d8 b2
  have b3 : a 8 ≠ 3 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 3 d0 c3 (by decide +kernel)
  have t3 : a 8 ∈ [0,1] := remove (a 8) 3 [0,1,3] t2 b3
  have b4 : a 15 ≠ 2 := exclude [0] (fun u v => edge r4 v u) (a 15) (a 0) 2 d0 c4 (by decide +kernel)
  have t4 : a 15 ∈ [0,1,3] := remove (a 15) 2 [0,1,2,3] d15 b4
  have b5 : a 15 ≠ 3 := exclude [0] (fun u v => edge r4 v u) (a 15) (a 0) 3 d0 c4 (by decide +kernel)
  have t5 : a 15 ∈ [0,1] := remove (a 15) 3 [0,1,3] t4 b5
  have b6 : a 31 ≠ 1 := exclude [0] (fun u v => edge r5 v u) (a 31) (a 0) 1 d0 c5 (by decide +kernel)
  have t6 : a 31 ∈ [0,2,3] := remove (a 31) 1 [0,1,2,3] d31 b6
  have b7 : a 31 ≠ 3 := exclude [0] (fun u v => edge r5 v u) (a 31) (a 0) 3 d0 c5 (by decide +kernel)
  have t7 : a 31 ∈ [0,2] := remove (a 31) 3 [0,2,3] t6 b7
  have b8 : a 5 ≠ 1 := exclude [0,1] (fun u v => edge r7 v u) (a 5) (a 1) 1 d1 c7 (by decide +kernel)
  have t8 : a 5 ∈ [0,2,3] := remove (a 5) 1 [0,1,2,3] d5 b8
  have b9 : a 5 ≠ 3 := exclude [0,1] (fun u v => edge r7 v u) (a 5) (a 1) 3 d1 c7 (by decide +kernel)
  have t9 : a 5 ∈ [0,2] := remove (a 5) 3 [0,2,3] t8 b9
  have b10 : a 6 ≠ 1 := exclude [0,1] (fun u v => edge r12 v u) (a 6) (a 2) 1 t1 c12 (by decide +kernel)
  have t10 : a 6 ∈ [0] := remove (a 6) 1 [0,1] d6 b10
  have b11 : a 17 ≠ 1 := exclude [0,1] (fun u v => edge r14 v u) (a 17) (a 2) 1 t1 c14 (by decide +kernel)
  have t11 : a 17 ∈ [0,2,3] := remove (a 17) 1 [0,1,2,3] d17 b11
  have b12 : a 17 ≠ 3 := exclude [0,1] (fun u v => edge r14 v u) (a 17) (a 2) 3 t1 c14 (by decide +kernel)
  have t12 : a 17 ∈ [0,2] := remove (a 17) 3 [0,2,3] t11 b12
  have b13 : a 33 ≠ 2 := exclude [0,1] (fun u v => edge r15 v u) (a 33) (a 2) 2 t1 c15 (by decide +kernel)
  have t13 : a 33 ∈ [0,1,3] := remove (a 33) 2 [0,1,2,3] d33 b13
  have b14 : a 33 ≠ 3 := exclude [0,1] (fun u v => edge r15 v u) (a 33) (a 2) 3 t1 c15 (by decide +kernel)
  have t14 : a 33 ∈ [0,1] := remove (a 33) 3 [0,1,3] t13 b14
  have b15 : a 7 ≠ 1 := exclude [0,2] (fun u v => edge r25 v u) (a 7) (a 5) 1 t9 c25 (by decide +kernel)
  have t15 : a 7 ∈ [0,2,3] := remove (a 7) 1 [0,1,2,3] d7 b15
  exact And.intro t1 (And.intro t3 (And.intro t5 (And.intro t7 (And.intro t9 (And.intro t10 (And.intro t12 (And.intro t14 (t15))))))))

theorem chunk1 (a : Nat → Nat)
    (d7 : a 7 ∈ [0,2,3])
    (d5 : a 5 ∈ [0,2])
    (d13 : a 13 ∈ [0,1])
    (d20 : a 20 ∈ [0,1,2,3])
    (d36 : a 36 ∈ [0,1])
    (d14 : a 14 ∈ [0,1,2,3])
    (d6 : a 6 ∈ [0])
    (d22 : a 22 ∈ [0,1,2,3])
    (d38 : a 38 ∈ [0,1,2,3])
    (d23 : a 23 ∈ [0,1,2,3])
    (d8 : a 8 ∈ [0,1])
    (d39 : a 39 ∈ [0,1])
    (d44 : a 44 ∈ [0,1,2,3])
    (c25 : edge r25 (a 5) (a 7)=true)
    (c26 : edge r26 (a 5) (a 13)=true)
    (c27 : edge r27 (a 5) (a 20)=true)
    (c28 : edge r28 (a 5) (a 36)=true)
    (c30 : edge r30 (a 6) (a 14)=true)
    (c33 : edge r33 (a 7) (a 22)=true)
    (c34 : edge r34 (a 7) (a 38)=true)
    (c38 : edge r38 (a 8) (a 23)=true)
    (c39 : edge r39 (a 8) (a 39)=true)
    (c55 : edge r55 (a 13) (a 44)=true)
    : a 7 ∈ [0,2] ∧ a 13 ∈ [0] ∧ a 20 ∈ [0,2] ∧ a 36 ∈ [0] ∧ a 14 ∈ [0,1] ∧ a 22 ∈ [0,2] ∧ a 38 ∈ [0,1] ∧ a 23 ∈ [0,1] ∧ a 39 ∈ [0] ∧ a 44 ∈ [0,1] := by
  have b0 : a 7 ≠ 3 := exclude [0,2] (fun u v => edge r25 v u) (a 7) (a 5) 3 d5 c25 (by decide +kernel)
  have t0 : a 7 ∈ [0,2] := remove (a 7) 3 [0,2,3] d7 b0
  have b1 : a 13 ≠ 1 := exclude [0,2] (fun u v => edge r26 v u) (a 13) (a 5) 1 d5 c26 (by decide +kernel)
  have t1 : a 13 ∈ [0] := remove (a 13) 1 [0,1] d13 b1
  have b2 : a 20 ≠ 1 := exclude [0,2] (fun u v => edge r27 v u) (a 20) (a 5) 1 d5 c27 (by decide +kernel)
  have t2 : a 20 ∈ [0,2,3] := remove (a 20) 1 [0,1,2,3] d20 b2
  have b3 : a 20 ≠ 3 := exclude [0,2] (fun u v => edge r27 v u) (a 20) (a 5) 3 d5 c27 (by decide +kernel)
  have t3 : a 20 ∈ [0,2] := remove (a 20) 3 [0,2,3] t2 b3
  have b4 : a 36 ≠ 1 := exclude [0,2] (fun u v => edge r28 v u) (a 36) (a 5) 1 d5 c28 (by decide +kernel)
  have t4 : a 36 ∈ [0] := remove (a 36) 1 [0,1] d36 b4
  have b5 : a 14 ≠ 2 := exclude [0] (fun u v => edge r30 v u) (a 14) (a 6) 2 d6 c30 (by decide +kernel)
  have t5 : a 14 ∈ [0,1,3] := remove (a 14) 2 [0,1,2,3] d14 b5
  have b6 : a 14 ≠ 3 := exclude [0] (fun u v => edge r30 v u) (a 14) (a 6) 3 d6 c30 (by decide +kernel)
  have t6 : a 14 ∈ [0,1] := remove (a 14) 3 [0,1,3] t5 b6
  have b7 : a 22 ≠ 1 := exclude [0,2] (fun u v => edge r33 v u) (a 22) (a 7) 1 t0 c33 (by decide +kernel)
  have t7 : a 22 ∈ [0,2,3] := remove (a 22) 1 [0,1,2,3] d22 b7
  have b8 : a 22 ≠ 3 := exclude [0,2] (fun u v => edge r33 v u) (a 22) (a 7) 3 t0 c33 (by decide +kernel)
  have t8 : a 22 ∈ [0,2] := remove (a 22) 3 [0,2,3] t7 b8
  have b9 : a 38 ≠ 2 := exclude [0,2] (fun u v => edge r34 v u) (a 38) (a 7) 2 t0 c34 (by decide +kernel)
  have t9 : a 38 ∈ [0,1,3] := remove (a 38) 2 [0,1,2,3] d38 b9
  have b10 : a 38 ≠ 3 := exclude [0,2] (fun u v => edge r34 v u) (a 38) (a 7) 3 t0 c34 (by decide +kernel)
  have t10 : a 38 ∈ [0,1] := remove (a 38) 3 [0,1,3] t9 b10
  have b11 : a 23 ≠ 2 := exclude [0,1] (fun u v => edge r38 v u) (a 23) (a 8) 2 d8 c38 (by decide +kernel)
  have t11 : a 23 ∈ [0,1,3] := remove (a 23) 2 [0,1,2,3] d23 b11
  have b12 : a 23 ≠ 3 := exclude [0,1] (fun u v => edge r38 v u) (a 23) (a 8) 3 d8 c38 (by decide +kernel)
  have t12 : a 23 ∈ [0,1] := remove (a 23) 3 [0,1,3] t11 b12
  have b13 : a 39 ≠ 1 := exclude [0,1] (fun u v => edge r39 v u) (a 39) (a 8) 1 d8 c39 (by decide +kernel)
  have t13 : a 39 ∈ [0] := remove (a 39) 1 [0,1] d39 b13
  have b14 : a 44 ≠ 2 := exclude [0] (fun u v => edge r55 v u) (a 44) (a 13) 2 t1 c55 (by decide +kernel)
  have t14 : a 44 ∈ [0,1,3] := remove (a 44) 2 [0,1,2,3] d44 b14
  have b15 : a 44 ≠ 3 := exclude [0] (fun u v => edge r55 v u) (a 44) (a 13) 3 t1 c55 (by decide +kernel)
  have t15 : a 44 ∈ [0,1] := remove (a 44) 3 [0,1,3] t14 b15
  exact And.intro t0 (And.intro t1 (And.intro t3 (And.intro t4 (And.intro t6 (And.intro t8 (And.intro t10 (And.intro t12 (And.intro t13 (t15)))))))))

theorem chunk2 (a : Nat → Nat)
    (d19 : a 19 ∈ [0,1])
    (d15 : a 15 ∈ [0,1])
    (d46 : a 46 ∈ [0,1,2,3])
    (d18 : a 18 ∈ [0,1])
    (d17 : a 17 ∈ [0,2])
    (d48 : a 48 ∈ [0,1,2,3])
    (d26 : a 26 ∈ [0,1])
    (d27 : a 27 ∈ [0,1])
    (d51 : a 51 ∈ [0,1,2,3])
    (d20 : a 20 ∈ [0,2])
    (d53 : a 53 ∈ [0,1,2,3])
    (d22 : a 22 ∈ [0,2])
    (d57 : a 57 ∈ [0,1])
    (d35 : a 35 ∈ [0,1,2,3])
    (d31 : a 31 ∈ [0,2])
    (d34 : a 34 ∈ [0,1])
    (d33 : a 33 ∈ [0,1])
    (c60 : edge r60 (a 15) (a 19)=true)
    (c62 : edge r62 (a 15) (a 46)=true)
    (c67 : edge r67 (a 17) (a 18)=true)
    (c70 : edge r70 (a 17) (a 48)=true)
    (c72 : edge r72 (a 18) (a 26)=true)
    (c76 : edge r76 (a 19) (a 27)=true)
    (c80 : edge r80 (a 20) (a 51)=true)
    (c85 : edge r85 (a 22) (a 53)=true)
    (c99 : edge r99 (a 27) (a 57)=true)
    (c107 : edge r107 (a 31) (a 35)=true)
    (c114 : edge r114 (a 33) (a 34)=true)
    : a 19 ∈ [0] ∧ a 46 ∈ [0,2] ∧ a 18 ∈ [0] ∧ a 48 ∈ [0,2] ∧ a 26 ∈ [0] ∧ a 27 ∈ [0] ∧ a 51 ∈ [0,1] ∧ a 53 ∈ [0,2] ∧ a 57 ∈ [0] ∧ a 35 ∈ [0,1] ∧ a 34 ∈ [0] := by
  have b0 : a 19 ≠ 1 := exclude [0,1] (fun u v => edge r60 v u) (a 19) (a 15) 1 d15 c60 (by decide +kernel)
  have t0 : a 19 ∈ [0] := remove (a 19) 1 [0,1] d19 b0
  have b1 : a 46 ≠ 1 := exclude [0,1] (fun u v => edge r62 v u) (a 46) (a 15) 1 d15 c62 (by decide +kernel)
  have t1 : a 46 ∈ [0,2,3] := remove (a 46) 1 [0,1,2,3] d46 b1
  have b2 : a 46 ≠ 3 := exclude [0,1] (fun u v => edge r62 v u) (a 46) (a 15) 3 d15 c62 (by decide +kernel)
  have t2 : a 46 ∈ [0,2] := remove (a 46) 3 [0,2,3] t1 b2
  have b3 : a 18 ≠ 1 := exclude [0,2] (fun u v => edge r67 v u) (a 18) (a 17) 1 d17 c67 (by decide +kernel)
  have t3 : a 18 ∈ [0] := remove (a 18) 1 [0,1] d18 b3
  have b4 : a 48 ≠ 1 := exclude [0,2] (fun u v => edge r70 v u) (a 48) (a 17) 1 d17 c70 (by decide +kernel)
  have t4 : a 48 ∈ [0,2,3] := remove (a 48) 1 [0,1,2,3] d48 b4
  have b5 : a 48 ≠ 3 := exclude [0,2] (fun u v => edge r70 v u) (a 48) (a 17) 3 d17 c70 (by decide +kernel)
  have t5 : a 48 ∈ [0,2] := remove (a 48) 3 [0,2,3] t4 b5
  have b6 : a 26 ≠ 1 := exclude [0] (fun u v => edge r72 v u) (a 26) (a 18) 1 t3 c72 (by decide +kernel)
  have t6 : a 26 ∈ [0] := remove (a 26) 1 [0,1] d26 b6
  have b7 : a 27 ≠ 1 := exclude [0] (fun u v => edge r76 v u) (a 27) (a 19) 1 t0 c76 (by decide +kernel)
  have t7 : a 27 ∈ [0] := remove (a 27) 1 [0,1] d27 b7
  have b8 : a 51 ≠ 2 := exclude [0,2] (fun u v => edge r80 v u) (a 51) (a 20) 2 d20 c80 (by decide +kernel)
  have t8 : a 51 ∈ [0,1,3] := remove (a 51) 2 [0,1,2,3] d51 b8
  have b9 : a 51 ≠ 3 := exclude [0,2] (fun u v => edge r80 v u) (a 51) (a 20) 3 d20 c80 (by decide +kernel)
  have t9 : a 51 ∈ [0,1] := remove (a 51) 3 [0,1,3] t8 b9
  have b10 : a 53 ≠ 1 := exclude [0,2] (fun u v => edge r85 v u) (a 53) (a 22) 1 d22 c85 (by decide +kernel)
  have t10 : a 53 ∈ [0,2,3] := remove (a 53) 1 [0,1,2,3] d53 b10
  have b11 : a 53 ≠ 3 := exclude [0,2] (fun u v => edge r85 v u) (a 53) (a 22) 3 d22 c85 (by decide +kernel)
  have t11 : a 53 ∈ [0,2] := remove (a 53) 3 [0,2,3] t10 b11
  have b12 : a 57 ≠ 1 := exclude [0] (fun u v => edge r99 v u) (a 57) (a 27) 1 t7 c99 (by decide +kernel)
  have t12 : a 57 ∈ [0] := remove (a 57) 1 [0,1] d57 b12
  have b13 : a 35 ≠ 2 := exclude [0,2] (fun u v => edge r107 v u) (a 35) (a 31) 2 d31 c107 (by decide +kernel)
  have t13 : a 35 ∈ [0,1,3] := remove (a 35) 2 [0,1,2,3] d35 b13
  have b14 : a 35 ≠ 3 := exclude [0,2] (fun u v => edge r107 v u) (a 35) (a 31) 3 d31 c107 (by decide +kernel)
  have t14 : a 35 ∈ [0,1] := remove (a 35) 3 [0,1,3] t13 b14
  have b15 : a 34 ≠ 1 := exclude [0,1] (fun u v => edge r114 v u) (a 34) (a 33) 1 d33 c114 (by decide +kernel)
  have t15 : a 34 ∈ [0] := remove (a 34) 1 [0,1] d34 b15
  exact And.intro t0 (And.intro t2 (And.intro t3 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t9 (And.intro t11 (And.intro t12 (And.intro t14 (t15))))))))))

theorem chunk3 (a : Nat → Nat)
    (d42 : a 42 ∈ [0,1])
    (d34 : a 34 ∈ [0])
    (d47 : a 47 ∈ [0,1])
    (d46 : a 46 ∈ [0,2])
    (d54 : a 54 ∈ [0,1,2,3])
    (d52 : a 52 ∈ [0,1])
    (d48 : a 48 ∈ [0,2])
    (d55 : a 55 ∈ [0,1,2,3])
    (d59 : a 59 ∈ [0,1])
    (d11 : a 11 ∈ [0,1])
    (d26 : a 26 ∈ [0])
    (c48 : edge r48 (a 11) (a 26)=true)
    (c119 : edge r119 (a 34) (a 42)=true)
    (c147 : edge r147 (a 46) (a 47)=true)
    (c152 : edge r152 (a 47) (a 54)=true)
    (c154 : edge r154 (a 48) (a 52)=true)
    (c155 : edge r155 (a 48) (a 55)=true)
    (c164 : edge r164 (a 52) (a 59)=true)
    : a 42 ∈ [0] ∧ a 47 ∈ [0] ∧ a 54 ∈ [0,1] ∧ a 52 ∈ [0] ∧ a 55 ∈ [0,2] ∧ a 59 ∈ [0] ∧ a 11 ∈ [0] := by
  have b0 : a 42 ≠ 1 := exclude [0] (fun u v => edge r119 v u) (a 42) (a 34) 1 d34 c119 (by decide +kernel)
  have t0 : a 42 ∈ [0] := remove (a 42) 1 [0,1] d42 b0
  have b1 : a 47 ≠ 1 := exclude [0,2] (fun u v => edge r147 v u) (a 47) (a 46) 1 d46 c147 (by decide +kernel)
  have t1 : a 47 ∈ [0] := remove (a 47) 1 [0,1] d47 b1
  have b2 : a 54 ≠ 2 := exclude [0] (fun u v => edge r152 v u) (a 54) (a 47) 2 t1 c152 (by decide +kernel)
  have t2 : a 54 ∈ [0,1,3] := remove (a 54) 2 [0,1,2,3] d54 b2
  have b3 : a 54 ≠ 3 := exclude [0] (fun u v => edge r152 v u) (a 54) (a 47) 3 t1 c152 (by decide +kernel)
  have t3 : a 54 ∈ [0,1] := remove (a 54) 3 [0,1,3] t2 b3
  have b4 : a 52 ≠ 1 := exclude [0,2] (fun u v => edge r154 v u) (a 52) (a 48) 1 d48 c154 (by decide +kernel)
  have t4 : a 52 ∈ [0] := remove (a 52) 1 [0,1] d52 b4
  have b5 : a 55 ≠ 1 := exclude [0,2] (fun u v => edge r155 v u) (a 55) (a 48) 1 d48 c155 (by decide +kernel)
  have t5 : a 55 ∈ [0,2,3] := remove (a 55) 1 [0,1,2,3] d55 b5
  have b6 : a 55 ≠ 3 := exclude [0,2] (fun u v => edge r155 v u) (a 55) (a 48) 3 d48 c155 (by decide +kernel)
  have t6 : a 55 ∈ [0,2] := remove (a 55) 3 [0,2,3] t5 b6
  have b7 : a 59 ≠ 1 := exclude [0] (fun u v => edge r164 v u) (a 59) (a 52) 1 t4 c164 (by decide +kernel)
  have t7 : a 59 ∈ [0] := remove (a 59) 1 [0,1] d59 b7
  have b8 : a 11 ≠ 1 := exclude [0] (edge r48) (a 11) (a 26) 1 d26 c48 (by decide +kernel)
  have t8 : a 11 ∈ [0] := remove (a 11) 1 [0,1] d11 b8
  exact And.intro t0 (And.intro t1 (And.intro t3 (And.intro t4 (And.intro t6 (And.intro t7 (t8))))))

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_235
