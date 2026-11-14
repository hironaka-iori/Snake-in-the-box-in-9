import PartitionData205_238
namespace PartitionCover205_238
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,1])
    (d1 : a 1 ∈ [0])
    (d5 : a 5 ∈ [0,1])
    (d15 : a 15 ∈ [0,1])
    (d30 : a 30 ∈ [0,1])
    (d2 : a 2 ∈ [0,1])
    (d6 : a 6 ∈ [0,2])
    (d31 : a 31 ∈ [0,1])
    (d9 : a 9 ∈ [0,1])
    (d17 : a 17 ∈ [0,1])
    (d4 : a 4 ∈ [0,1])
    (d10 : a 10 ∈ [0,1])
    (d18 : a 18 ∈ [0,2])
    (d19 : a 19 ∈ [0,1])
    (d34 : a 34 ∈ [0,1])
    (d7 : a 7 ∈ [0,1])
    (d22 : a 22 ∈ [0,2])
    (c6 : edge r6 (a 1) (a 3)=true)
    (c7 : edge r7 (a 1) (a 5)=true)
    (c8 : edge r8 (a 1) (a 15)=true)
    (c9 : edge r9 (a 1) (a 30)=true)
    (c10 : edge r10 (a 2) (a 3)=true)
    (c11 : edge r11 (a 2) (a 6)=true)
    (c14 : edge r14 (a 2) (a 31)=true)
    (c15 : edge r15 (a 3) (a 9)=true)
    (c16 : edge r16 (a 3) (a 17)=true)
    (c18 : edge r18 (a 4) (a 5)=true)
    (c20 : edge r20 (a 4) (a 10)=true)
    (c21 : edge r21 (a 4) (a 18)=true)
    (c24 : edge r24 (a 5) (a 19)=true)
    (c25 : edge r25 (a 5) (a 34)=true)
    (c29 : edge r29 (a 7) (a 10)=true)
    (c30 : edge r30 (a 7) (a 22)=true)
    : a 3 ∈ [0] ∧ a 5 ∈ [0] ∧ a 15 ∈ [0] ∧ a 30 ∈ [0] ∧ a 2 ∈ [0] ∧ a 6 ∈ [0] ∧ a 31 ∈ [0] ∧ a 9 ∈ [0] ∧ a 17 ∈ [0] ∧ a 4 ∈ [0] ∧ a 10 ∈ [0] ∧ a 18 ∈ [0] ∧ a 19 ∈ [0] ∧ a 34 ∈ [0] ∧ a 7 ∈ [0] ∧ a 22 ∈ [0] := by
  have b0 : a 3 ≠ 1 := exclude [0] (fun u v => edge r6 v u) (a 3) (a 1) 1 d1 c6 (by decide +kernel)
  have t0 : a 3 ∈ [0] := remove (a 3) 1 [0,1] d3 b0
  have b1 : a 5 ≠ 1 := exclude [0] (fun u v => edge r7 v u) (a 5) (a 1) 1 d1 c7 (by decide +kernel)
  have t1 : a 5 ∈ [0] := remove (a 5) 1 [0,1] d5 b1
  have b2 : a 15 ≠ 1 := exclude [0] (fun u v => edge r8 v u) (a 15) (a 1) 1 d1 c8 (by decide +kernel)
  have t2 : a 15 ∈ [0] := remove (a 15) 1 [0,1] d15 b2
  have b3 : a 30 ≠ 1 := exclude [0] (fun u v => edge r9 v u) (a 30) (a 1) 1 d1 c9 (by decide +kernel)
  have t3 : a 30 ∈ [0] := remove (a 30) 1 [0,1] d30 b3
  have b4 : a 2 ≠ 1 := exclude [0] (edge r10) (a 2) (a 3) 1 t0 c10 (by decide +kernel)
  have t4 : a 2 ∈ [0] := remove (a 2) 1 [0,1] d2 b4
  have b5 : a 6 ≠ 2 := exclude [0] (fun u v => edge r11 v u) (a 6) (a 2) 2 t4 c11 (by decide +kernel)
  have t5 : a 6 ∈ [0] := remove (a 6) 2 [0,2] d6 b5
  have b6 : a 31 ≠ 1 := exclude [0] (fun u v => edge r14 v u) (a 31) (a 2) 1 t4 c14 (by decide +kernel)
  have t6 : a 31 ∈ [0] := remove (a 31) 1 [0,1] d31 b6
  have b7 : a 9 ≠ 1 := exclude [0] (fun u v => edge r15 v u) (a 9) (a 3) 1 t0 c15 (by decide +kernel)
  have t7 : a 9 ∈ [0] := remove (a 9) 1 [0,1] d9 b7
  have b8 : a 17 ≠ 1 := exclude [0] (fun u v => edge r16 v u) (a 17) (a 3) 1 t0 c16 (by decide +kernel)
  have t8 : a 17 ∈ [0] := remove (a 17) 1 [0,1] d17 b8
  have b9 : a 4 ≠ 1 := exclude [0] (edge r18) (a 4) (a 5) 1 t1 c18 (by decide +kernel)
  have t9 : a 4 ∈ [0] := remove (a 4) 1 [0,1] d4 b9
  have b10 : a 10 ≠ 1 := exclude [0] (fun u v => edge r20 v u) (a 10) (a 4) 1 t9 c20 (by decide +kernel)
  have t10 : a 10 ∈ [0] := remove (a 10) 1 [0,1] d10 b10
  have b11 : a 18 ≠ 2 := exclude [0] (fun u v => edge r21 v u) (a 18) (a 4) 2 t9 c21 (by decide +kernel)
  have t11 : a 18 ∈ [0] := remove (a 18) 2 [0,2] d18 b11
  have b12 : a 19 ≠ 1 := exclude [0] (fun u v => edge r24 v u) (a 19) (a 5) 1 t1 c24 (by decide +kernel)
  have t12 : a 19 ∈ [0] := remove (a 19) 1 [0,1] d19 b12
  have b13 : a 34 ≠ 1 := exclude [0] (fun u v => edge r25 v u) (a 34) (a 5) 1 t1 c25 (by decide +kernel)
  have t13 : a 34 ∈ [0] := remove (a 34) 1 [0,1] d34 b13
  have b14 : a 7 ≠ 1 := exclude [0] (edge r29) (a 7) (a 10) 1 t10 c29 (by decide +kernel)
  have t14 : a 7 ∈ [0] := remove (a 7) 1 [0,1] d7 b14
  have b15 : a 22 ≠ 2 := exclude [0] (fun u v => edge r30 v u) (a 22) (a 7) 2 t14 c30 (by decide +kernel)
  have t15 : a 22 ∈ [0] := remove (a 22) 2 [0,2] d22 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk5 (a : Nat → Nat)
    (d36 : a 36 ∈ [0,2])
    (d7 : a 7 ∈ [0])
    (d13 : a 13 ∈ [0,1])
    (d9 : a 9 ∈ [0])
    (d25 : a 25 ∈ [0,2])
    (d39 : a 39 ∈ [0,1])
    (d26 : a 26 ∈ [0,1])
    (d10 : a 10 ∈ [0])
    (d40 : a 40 ∈ [0,1])
    (d43 : a 43 ∈ [0,1])
    (d14 : a 14 ∈ [0,1])
    (d15 : a 15 ∈ [0])
    (d44 : a 44 ∈ [0,2])
    (d21 : a 21 ∈ [0,1])
    (d17 : a 17 ∈ [0])
    (d47 : a 47 ∈ [0,2])
    (d48 : a 48 ∈ [0,1])
    (d18 : a 18 ∈ [0])
    (d49 : a 49 ∈ [0,1])
    (d19 : a 19 ∈ [0])
    (d24 : a 24 ∈ [0,1])
    (d22 : a 22 ∈ [0])
    (d52 : a 52 ∈ [0,1])
    (d28 : a 28 ∈ [0,1])
    (c31 : edge r31 (a 7) (a 36)=true)
    (c36 : edge r36 (a 9) (a 13)=true)
    (c37 : edge r37 (a 9) (a 25)=true)
    (c38 : edge r38 (a 9) (a 39)=true)
    (c41 : edge r41 (a 10) (a 26)=true)
    (c42 : edge r42 (a 10) (a 40)=true)
    (c49 : edge r49 (a 13) (a 43)=true)
    (c50 : edge r50 (a 14) (a 15)=true)
    (c54 : edge r54 (a 14) (a 44)=true)
    (c63 : edge r63 (a 17) (a 21)=true)
    (c65 : edge r65 (a 17) (a 47)=true)
    (c69 : edge r69 (a 18) (a 48)=true)
    (c72 : edge r72 (a 19) (a 49)=true)
    (c78 : edge r78 (a 22) (a 24)=true)
    (c80 : edge r80 (a 22) (a 52)=true)
    (c85 : edge r85 (a 24) (a 28)=true)
    : a 36 ∈ [0] ∧ a 13 ∈ [0] ∧ a 25 ∈ [0] ∧ a 39 ∈ [0] ∧ a 26 ∈ [0] ∧ a 40 ∈ [0] ∧ a 43 ∈ [0] ∧ a 14 ∈ [0] ∧ a 44 ∈ [0] ∧ a 21 ∈ [0] ∧ a 47 ∈ [0] ∧ a 48 ∈ [0] ∧ a 49 ∈ [0] ∧ a 24 ∈ [0] ∧ a 52 ∈ [0] ∧ a 28 ∈ [0] := by
  have b0 : a 36 ≠ 2 := exclude [0] (fun u v => edge r31 v u) (a 36) (a 7) 2 d7 c31 (by decide +kernel)
  have t0 : a 36 ∈ [0] := remove (a 36) 2 [0,2] d36 b0
  have b1 : a 13 ≠ 1 := exclude [0] (fun u v => edge r36 v u) (a 13) (a 9) 1 d9 c36 (by decide +kernel)
  have t1 : a 13 ∈ [0] := remove (a 13) 1 [0,1] d13 b1
  have b2 : a 25 ≠ 2 := exclude [0] (fun u v => edge r37 v u) (a 25) (a 9) 2 d9 c37 (by decide +kernel)
  have t2 : a 25 ∈ [0] := remove (a 25) 2 [0,2] d25 b2
  have b3 : a 39 ≠ 1 := exclude [0] (fun u v => edge r38 v u) (a 39) (a 9) 1 d9 c38 (by decide +kernel)
  have t3 : a 39 ∈ [0] := remove (a 39) 1 [0,1] d39 b3
  have b4 : a 26 ≠ 1 := exclude [0] (fun u v => edge r41 v u) (a 26) (a 10) 1 d10 c41 (by decide +kernel)
  have t4 : a 26 ∈ [0] := remove (a 26) 1 [0,1] d26 b4
  have b5 : a 40 ≠ 1 := exclude [0] (fun u v => edge r42 v u) (a 40) (a 10) 1 d10 c42 (by decide +kernel)
  have t5 : a 40 ∈ [0] := remove (a 40) 1 [0,1] d40 b5
  have b6 : a 43 ≠ 1 := exclude [0] (fun u v => edge r49 v u) (a 43) (a 13) 1 t1 c49 (by decide +kernel)
  have t6 : a 43 ∈ [0] := remove (a 43) 1 [0,1] d43 b6
  have b7 : a 14 ≠ 1 := exclude [0] (edge r50) (a 14) (a 15) 1 d15 c50 (by decide +kernel)
  have t7 : a 14 ∈ [0] := remove (a 14) 1 [0,1] d14 b7
  have b8 : a 44 ≠ 2 := exclude [0] (fun u v => edge r54 v u) (a 44) (a 14) 2 t7 c54 (by decide +kernel)
  have t8 : a 44 ∈ [0] := remove (a 44) 2 [0,2] d44 b8
  have b9 : a 21 ≠ 1 := exclude [0] (fun u v => edge r63 v u) (a 21) (a 17) 1 d17 c63 (by decide +kernel)
  have t9 : a 21 ∈ [0] := remove (a 21) 1 [0,1] d21 b9
  have b10 : a 47 ≠ 2 := exclude [0] (fun u v => edge r65 v u) (a 47) (a 17) 2 d17 c65 (by decide +kernel)
  have t10 : a 47 ∈ [0] := remove (a 47) 2 [0,2] d47 b10
  have b11 : a 48 ≠ 1 := exclude [0] (fun u v => edge r69 v u) (a 48) (a 18) 1 d18 c69 (by decide +kernel)
  have t11 : a 48 ∈ [0] := remove (a 48) 1 [0,1] d48 b11
  have b12 : a 49 ≠ 1 := exclude [0] (fun u v => edge r72 v u) (a 49) (a 19) 1 d19 c72 (by decide +kernel)
  have t12 : a 49 ∈ [0] := remove (a 49) 1 [0,1] d49 b12
  have b13 : a 24 ≠ 1 := exclude [0] (fun u v => edge r78 v u) (a 24) (a 22) 1 d22 c78 (by decide +kernel)
  have t13 : a 24 ∈ [0] := remove (a 24) 1 [0,1] d24 b13
  have b14 : a 52 ≠ 1 := exclude [0] (fun u v => edge r80 v u) (a 52) (a 22) 1 d22 c80 (by decide +kernel)
  have t14 : a 52 ∈ [0] := remove (a 52) 1 [0,1] d52 b14
  have b15 : a 28 ≠ 1 := exclude [0] (fun u v => edge r85 v u) (a 28) (a 24) 1 t13 c85 (by decide +kernel)
  have t15 : a 28 ∈ [0] := remove (a 28) 1 [0,1] d28 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk6 (a : Nat → Nat)
    (d55 : a 55 ∈ [0,2])
    (d25 : a 25 ∈ [0])
    (d57 : a 57 ∈ [0,2])
    (d28 : a 28 ∈ [0])
    (d29 : a 29 ∈ [0,2])
    (d30 : a 30 ∈ [0])
    (d38 : a 38 ∈ [0,1])
    (d31 : a 31 ∈ [0])
    (d46 : a 46 ∈ [0,1])
    (d35 : a 35 ∈ [0,2])
    (d34 : a 34 ∈ [0])
    (d42 : a 42 ∈ [0,1])
    (d58 : a 58 ∈ [0,2])
    (d43 : a 43 ∈ [0])
    (d50 : a 50 ∈ [0,1])
    (d56 : a 56 ∈ [0,1])
    (d49 : a 49 ∈ [0])
    (d53 : a 53 ∈ [0,1])
    (d52 : a 52 ∈ [0])
    (c87 : edge r87 (a 25) (a 55)=true)
    (c91 : edge r91 (a 28) (a 57)=true)
    (c92 : edge r92 (a 29) (a 30)=true)
    (c102 : edge r102 (a 31) (a 38)=true)
    (c103 : edge r103 (a 31) (a 46)=true)
    (c110 : edge r110 (a 34) (a 35)=true)
    (c123 : edge r123 (a 38) (a 42)=true)
    (c133 : edge r133 (a 43) (a 58)=true)
    (c142 : edge r142 (a 46) (a 50)=true)
    (c149 : edge r149 (a 49) (a 56)=true)
    (c153 : edge r153 (a 52) (a 53)=true)
    : a 55 ∈ [0] ∧ a 57 ∈ [0] ∧ a 29 ∈ [0] ∧ a 38 ∈ [0] ∧ a 46 ∈ [0] ∧ a 35 ∈ [0] ∧ a 42 ∈ [0] ∧ a 58 ∈ [0] ∧ a 50 ∈ [0] ∧ a 56 ∈ [0] ∧ a 53 ∈ [0] := by
  have b0 : a 55 ≠ 2 := exclude [0] (fun u v => edge r87 v u) (a 55) (a 25) 2 d25 c87 (by decide +kernel)
  have t0 : a 55 ∈ [0] := remove (a 55) 2 [0,2] d55 b0
  have b1 : a 57 ≠ 2 := exclude [0] (fun u v => edge r91 v u) (a 57) (a 28) 2 d28 c91 (by decide +kernel)
  have t1 : a 57 ∈ [0] := remove (a 57) 2 [0,2] d57 b1
  have b2 : a 29 ≠ 2 := exclude [0] (edge r92) (a 29) (a 30) 2 d30 c92 (by decide +kernel)
  have t2 : a 29 ∈ [0] := remove (a 29) 2 [0,2] d29 b2
  have b3 : a 38 ≠ 1 := exclude [0] (fun u v => edge r102 v u) (a 38) (a 31) 1 d31 c102 (by decide +kernel)
  have t3 : a 38 ∈ [0] := remove (a 38) 1 [0,1] d38 b3
  have b4 : a 46 ≠ 1 := exclude [0] (fun u v => edge r103 v u) (a 46) (a 31) 1 d31 c103 (by decide +kernel)
  have t4 : a 46 ∈ [0] := remove (a 46) 1 [0,1] d46 b4
  have b5 : a 35 ≠ 2 := exclude [0] (fun u v => edge r110 v u) (a 35) (a 34) 2 d34 c110 (by decide +kernel)
  have t5 : a 35 ∈ [0] := remove (a 35) 2 [0,2] d35 b5
  have b6 : a 42 ≠ 1 := exclude [0] (fun u v => edge r123 v u) (a 42) (a 38) 1 t3 c123 (by decide +kernel)
  have t6 : a 42 ∈ [0] := remove (a 42) 1 [0,1] d42 b6
  have b7 : a 58 ≠ 2 := exclude [0] (fun u v => edge r133 v u) (a 58) (a 43) 2 d43 c133 (by decide +kernel)
  have t7 : a 58 ∈ [0] := remove (a 58) 2 [0,2] d58 b7
  have b8 : a 50 ≠ 1 := exclude [0] (fun u v => edge r142 v u) (a 50) (a 46) 1 t4 c142 (by decide +kernel)
  have t8 : a 50 ∈ [0] := remove (a 50) 1 [0,1] d50 b8
  have b9 : a 56 ≠ 1 := exclude [0] (fun u v => edge r149 v u) (a 56) (a 49) 1 d49 c149 (by decide +kernel)
  have t9 : a 56 ∈ [0] := remove (a 56) 1 [0,1] d56 b9
  have b10 : a 53 ≠ 1 := exclude [0] (fun u v => edge r153 v u) (a 53) (a 52) 1 d52 c153 (by decide +kernel)
  have t10 : a 53 ∈ [0] := remove (a 53) 1 [0,1] d53 b10
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (t10))))))))))

theorem chunk7 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,1])
    (d1 : a 1 ∈ [1])
    (d5 : a 5 ∈ [0,1])
    (d15 : a 15 ∈ [0,1])
    (d30 : a 30 ∈ [0,1])
    (d2 : a 2 ∈ [0,1])
    (d6 : a 6 ∈ [0,2])
    (d31 : a 31 ∈ [0,1])
    (d9 : a 9 ∈ [0,1])
    (d17 : a 17 ∈ [0,1])
    (d4 : a 4 ∈ [0,1])
    (d10 : a 10 ∈ [0,1])
    (d18 : a 18 ∈ [0,2])
    (d19 : a 19 ∈ [0,1])
    (d34 : a 34 ∈ [0,1])
    (d7 : a 7 ∈ [0,1])
    (d22 : a 22 ∈ [0,2])
    (c6 : edge r6 (a 1) (a 3)=true)
    (c7 : edge r7 (a 1) (a 5)=true)
    (c8 : edge r8 (a 1) (a 15)=true)
    (c9 : edge r9 (a 1) (a 30)=true)
    (c10 : edge r10 (a 2) (a 3)=true)
    (c11 : edge r11 (a 2) (a 6)=true)
    (c14 : edge r14 (a 2) (a 31)=true)
    (c15 : edge r15 (a 3) (a 9)=true)
    (c16 : edge r16 (a 3) (a 17)=true)
    (c18 : edge r18 (a 4) (a 5)=true)
    (c20 : edge r20 (a 4) (a 10)=true)
    (c21 : edge r21 (a 4) (a 18)=true)
    (c24 : edge r24 (a 5) (a 19)=true)
    (c25 : edge r25 (a 5) (a 34)=true)
    (c29 : edge r29 (a 7) (a 10)=true)
    (c30 : edge r30 (a 7) (a 22)=true)
    : a 3 ∈ [1] ∧ a 5 ∈ [1] ∧ a 15 ∈ [1] ∧ a 30 ∈ [1] ∧ a 2 ∈ [1] ∧ a 6 ∈ [2] ∧ a 31 ∈ [1] ∧ a 9 ∈ [1] ∧ a 17 ∈ [1] ∧ a 4 ∈ [1] ∧ a 10 ∈ [1] ∧ a 18 ∈ [2] ∧ a 19 ∈ [1] ∧ a 34 ∈ [1] ∧ a 7 ∈ [1] ∧ a 22 ∈ [2] := by
  have b0 : a 3 ≠ 0 := exclude [1] (fun u v => edge r6 v u) (a 3) (a 1) 0 d1 c6 (by decide +kernel)
  have t0 : a 3 ∈ [1] := remove (a 3) 0 [0,1] d3 b0
  have b1 : a 5 ≠ 0 := exclude [1] (fun u v => edge r7 v u) (a 5) (a 1) 0 d1 c7 (by decide +kernel)
  have t1 : a 5 ∈ [1] := remove (a 5) 0 [0,1] d5 b1
  have b2 : a 15 ≠ 0 := exclude [1] (fun u v => edge r8 v u) (a 15) (a 1) 0 d1 c8 (by decide +kernel)
  have t2 : a 15 ∈ [1] := remove (a 15) 0 [0,1] d15 b2
  have b3 : a 30 ≠ 0 := exclude [1] (fun u v => edge r9 v u) (a 30) (a 1) 0 d1 c9 (by decide +kernel)
  have t3 : a 30 ∈ [1] := remove (a 30) 0 [0,1] d30 b3
  have b4 : a 2 ≠ 0 := exclude [1] (edge r10) (a 2) (a 3) 0 t0 c10 (by decide +kernel)
  have t4 : a 2 ∈ [1] := remove (a 2) 0 [0,1] d2 b4
  have b5 : a 6 ≠ 0 := exclude [1] (fun u v => edge r11 v u) (a 6) (a 2) 0 t4 c11 (by decide +kernel)
  have t5 : a 6 ∈ [2] := remove (a 6) 0 [0,2] d6 b5
  have b6 : a 31 ≠ 0 := exclude [1] (fun u v => edge r14 v u) (a 31) (a 2) 0 t4 c14 (by decide +kernel)
  have t6 : a 31 ∈ [1] := remove (a 31) 0 [0,1] d31 b6
  have b7 : a 9 ≠ 0 := exclude [1] (fun u v => edge r15 v u) (a 9) (a 3) 0 t0 c15 (by decide +kernel)
  have t7 : a 9 ∈ [1] := remove (a 9) 0 [0,1] d9 b7
  have b8 : a 17 ≠ 0 := exclude [1] (fun u v => edge r16 v u) (a 17) (a 3) 0 t0 c16 (by decide +kernel)
  have t8 : a 17 ∈ [1] := remove (a 17) 0 [0,1] d17 b8
  have b9 : a 4 ≠ 0 := exclude [1] (edge r18) (a 4) (a 5) 0 t1 c18 (by decide +kernel)
  have t9 : a 4 ∈ [1] := remove (a 4) 0 [0,1] d4 b9
  have b10 : a 10 ≠ 0 := exclude [1] (fun u v => edge r20 v u) (a 10) (a 4) 0 t9 c20 (by decide +kernel)
  have t10 : a 10 ∈ [1] := remove (a 10) 0 [0,1] d10 b10
  have b11 : a 18 ≠ 0 := exclude [1] (fun u v => edge r21 v u) (a 18) (a 4) 0 t9 c21 (by decide +kernel)
  have t11 : a 18 ∈ [2] := remove (a 18) 0 [0,2] d18 b11
  have b12 : a 19 ≠ 0 := exclude [1] (fun u v => edge r24 v u) (a 19) (a 5) 0 t1 c24 (by decide +kernel)
  have t12 : a 19 ∈ [1] := remove (a 19) 0 [0,1] d19 b12
  have b13 : a 34 ≠ 0 := exclude [1] (fun u v => edge r25 v u) (a 34) (a 5) 0 t1 c25 (by decide +kernel)
  have t13 : a 34 ∈ [1] := remove (a 34) 0 [0,1] d34 b13
  have b14 : a 7 ≠ 0 := exclude [1] (edge r29) (a 7) (a 10) 0 t10 c29 (by decide +kernel)
  have t14 : a 7 ∈ [1] := remove (a 7) 0 [0,1] d7 b14
  have b15 : a 22 ≠ 0 := exclude [1] (fun u v => edge r30 v u) (a 22) (a 7) 0 t14 c30 (by decide +kernel)
  have t15 : a 22 ∈ [2] := remove (a 22) 0 [0,2] d22 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_238
