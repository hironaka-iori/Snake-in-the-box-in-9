import PartitionData205_201
namespace PartitionCover205_201
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk24 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,2])
    (d1 : a 1 ∈ [1])
    (d9 : a 9 ∈ [0,2])
    (d17 : a 17 ∈ [0,6])
    (d2 : a 2 ∈ [0,8])
    (d6 : a 6 ∈ [0,5])
    (d10 : a 10 ∈ [0,1])
    (d18 : a 18 ∈ [0,8])
    (d7 : a 7 ∈ [0,4])
    (d19 : a 19 ∈ [0,1])
    (d4 : a 4 ∈ [0,1])
    (d12 : a 12 ∈ [0,8])
    (d20 : a 20 ∈ [0,12])
    (d14 : a 14 ∈ [0,13])
    (d22 : a 22 ∈ [0,11])
    (d15 : a 15 ∈ [0,8])
    (d8 : a 8 ∈ [0,8])
    (c5 : edge r5 (a 1) (a 3)=true)
    (c7 : edge r7 (a 1) (a 9)=true)
    (c8 : edge r8 (a 1) (a 17)=true)
    (c9 : edge r9 (a 2) (a 3)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    (c12 : edge r12 (a 2) (a 18)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c15 : edge r15 (a 3) (a 19)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    : a 3 ∈ [2] ∧ a 9 ∈ [2] ∧ a 17 ∈ [6] ∧ a 2 ∈ [8] ∧ a 6 ∈ [5] ∧ a 10 ∈ [1] ∧ a 18 ∈ [8] ∧ a 7 ∈ [4] ∧ a 19 ∈ [1] ∧ a 4 ∈ [1] ∧ a 12 ∈ [8] ∧ a 20 ∈ [12] ∧ a 14 ∈ [13] ∧ a 22 ∈ [11] ∧ a 15 ∈ [8] ∧ a 8 ∈ [8] := by
  have b0 : a 3 ≠ 0 := exclude [1] (fun u v => edge r5 v u) (a 3) (a 1) 0 d1 c5 (by decide +kernel)
  have t0 : a 3 ∈ [2] := remove (a 3) 0 [0,2] d3 b0
  have b1 : a 9 ≠ 0 := exclude [1] (fun u v => edge r7 v u) (a 9) (a 1) 0 d1 c7 (by decide +kernel)
  have t1 : a 9 ∈ [2] := remove (a 9) 0 [0,2] d9 b1
  have b2 : a 17 ≠ 0 := exclude [1] (fun u v => edge r8 v u) (a 17) (a 1) 0 d1 c8 (by decide +kernel)
  have t2 : a 17 ∈ [6] := remove (a 17) 0 [0,6] d17 b2
  have b3 : a 2 ≠ 0 := exclude [2] (edge r9) (a 2) (a 3) 0 t0 c9 (by decide +kernel)
  have t3 : a 2 ∈ [8] := remove (a 2) 0 [0,8] d2 b3
  have b4 : a 6 ≠ 0 := exclude [8] (fun u v => edge r10 v u) (a 6) (a 2) 0 t3 c10 (by decide +kernel)
  have t4 : a 6 ∈ [5] := remove (a 6) 0 [0,5] d6 b4
  have b5 : a 10 ≠ 0 := exclude [8] (fun u v => edge r11 v u) (a 10) (a 2) 0 t3 c11 (by decide +kernel)
  have t5 : a 10 ∈ [1] := remove (a 10) 0 [0,1] d10 b5
  have b6 : a 18 ≠ 0 := exclude [8] (fun u v => edge r12 v u) (a 18) (a 2) 0 t3 c12 (by decide +kernel)
  have t6 : a 18 ∈ [8] := remove (a 18) 0 [0,8] d18 b6
  have b7 : a 7 ≠ 0 := exclude [2] (fun u v => edge r13 v u) (a 7) (a 3) 0 t0 c13 (by decide +kernel)
  have t7 : a 7 ∈ [4] := remove (a 7) 0 [0,4] d7 b7
  have b8 : a 19 ≠ 0 := exclude [2] (fun u v => edge r15 v u) (a 19) (a 3) 0 t0 c15 (by decide +kernel)
  have t8 : a 19 ∈ [1] := remove (a 19) 0 [0,1] d19 b8
  have b9 : a 4 ≠ 0 := exclude [5] (edge r17) (a 4) (a 6) 0 t4 c17 (by decide +kernel)
  have t9 : a 4 ∈ [1] := remove (a 4) 0 [0,1] d4 b9
  have b10 : a 12 ≠ 0 := exclude [1] (fun u v => edge r18 v u) (a 12) (a 4) 0 t9 c18 (by decide +kernel)
  have t10 : a 12 ∈ [8] := remove (a 12) 0 [0,8] d12 b10
  have b11 : a 20 ≠ 0 := exclude [1] (fun u v => edge r19 v u) (a 20) (a 4) 0 t9 c19 (by decide +kernel)
  have t11 : a 20 ∈ [12] := remove (a 20) 0 [0,12] d20 b11
  have b12 : a 14 ≠ 0 := exclude [5] (fun u v => edge r24 v u) (a 14) (a 6) 0 t4 c24 (by decide +kernel)
  have t12 : a 14 ∈ [13] := remove (a 14) 0 [0,13] d14 b12
  have b13 : a 22 ≠ 0 := exclude [5] (fun u v => edge r25 v u) (a 22) (a 6) 0 t4 c25 (by decide +kernel)
  have t13 : a 22 ∈ [11] := remove (a 22) 0 [0,11] d22 b13
  have b14 : a 15 ≠ 0 := exclude [4] (fun u v => edge r26 v u) (a 15) (a 7) 0 t7 c26 (by decide +kernel)
  have t14 : a 15 ∈ [8] := remove (a 15) 0 [0,8] d15 b14
  have b15 : a 8 ≠ 0 := exclude [2] (edge r28) (a 8) (a 9) 0 t1 c28 (by decide +kernel)
  have t15 : a 8 ∈ [8] := remove (a 8) 0 [0,8] d8 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk25 (a : Nat → Nat)
    (d24 : a 24 ∈ [0,6])
    (d8 : a 8 ∈ [8])
    (d13 : a 13 ∈ [0,4])
    (d9 : a 9 ∈ [2])
    (d25 : a 25 ∈ [0,3])
    (d26 : a 26 ∈ [0,20])
    (d10 : a 10 ∈ [1])
    (d11 : a 11 ∈ [0,16])
    (d15 : a 15 ∈ [8])
    (d27 : a 27 ∈ [0,11])
    (d28 : a 28 ∈ [0,4])
    (d12 : a 12 ∈ [8])
    (d29 : a 29 ∈ [0,8])
    (d30 : a 30 ∈ [0,23])
    (d14 : a 14 ∈ [13])
    (d31 : a 31 ∈ [0,11])
    (d16 : a 16 ∈ [0,12])
    (d17 : a 17 ∈ [6])
    (d21 : a 21 ∈ [0,6])
    (d23 : a 23 ∈ [0,1])
    (d5 : a 5 ∈ [0,2])
    (d4 : a 4 ∈ [1])
    (c16 : edge r16 (a 4) (a 5)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    (c33 : edge r33 (a 9) (a 13)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c53 : edge r53 (a 17) (a 21)=true)
    (c63 : edge r63 (a 21) (a 23)=true)
    : a 24 ∈ [6] ∧ a 13 ∈ [4] ∧ a 25 ∈ [3] ∧ a 26 ∈ [20] ∧ a 11 ∈ [16] ∧ a 27 ∈ [11] ∧ a 28 ∈ [4] ∧ a 29 ∈ [8] ∧ a 30 ∈ [23] ∧ a 31 ∈ [11] ∧ a 16 ∈ [12] ∧ a 21 ∈ [6] ∧ a 23 ∈ [1] ∧ a 5 ∈ [2] := by
  have b0 : a 24 ≠ 0 := exclude [8] (fun u v => edge r31 v u) (a 24) (a 8) 0 d8 c31 (by decide +kernel)
  have t0 : a 24 ∈ [6] := remove (a 24) 0 [0,6] d24 b0
  have b1 : a 13 ≠ 0 := exclude [2] (fun u v => edge r33 v u) (a 13) (a 9) 0 d9 c33 (by decide +kernel)
  have t1 : a 13 ∈ [4] := remove (a 13) 0 [0,4] d13 b1
  have b2 : a 25 ≠ 0 := exclude [2] (fun u v => edge r34 v u) (a 25) (a 9) 0 d9 c34 (by decide +kernel)
  have t2 : a 25 ∈ [3] := remove (a 25) 0 [0,3] d25 b2
  have b3 : a 26 ≠ 0 := exclude [1] (fun u v => edge r37 v u) (a 26) (a 10) 0 d10 c37 (by decide +kernel)
  have t3 : a 26 ∈ [20] := remove (a 26) 0 [0,20] d26 b3
  have b4 : a 11 ≠ 0 := exclude [8] (edge r38) (a 11) (a 15) 0 d15 c38 (by decide +kernel)
  have t4 : a 11 ∈ [16] := remove (a 11) 0 [0,16] d11 b4
  have b5 : a 27 ≠ 0 := exclude [16] (fun u v => edge r39 v u) (a 27) (a 11) 0 t4 c39 (by decide +kernel)
  have t5 : a 27 ∈ [11] := remove (a 27) 0 [0,11] d27 b5
  have b6 : a 28 ≠ 0 := exclude [8] (fun u v => edge r42 v u) (a 28) (a 12) 0 d12 c42 (by decide +kernel)
  have t6 : a 28 ∈ [4] := remove (a 28) 0 [0,4] d28 b6
  have b7 : a 29 ≠ 0 := exclude [4] (fun u v => edge r44 v u) (a 29) (a 13) 0 t1 c44 (by decide +kernel)
  have t7 : a 29 ∈ [8] := remove (a 29) 0 [0,8] d29 b7
  have b8 : a 30 ≠ 0 := exclude [13] (fun u v => edge r46 v u) (a 30) (a 14) 0 d14 c46 (by decide +kernel)
  have t8 : a 30 ∈ [23] := remove (a 30) 0 [0,23] d30 b8
  have b9 : a 31 ≠ 0 := exclude [8] (fun u v => edge r47 v u) (a 31) (a 15) 0 d15 c47 (by decide +kernel)
  have t9 : a 31 ∈ [11] := remove (a 31) 0 [0,11] d31 b9
  have b10 : a 16 ≠ 0 := exclude [6] (edge r48) (a 16) (a 17) 0 d17 c48 (by decide +kernel)
  have t10 : a 16 ∈ [12] := remove (a 16) 0 [0,12] d16 b10
  have b11 : a 21 ≠ 0 := exclude [6] (fun u v => edge r53 v u) (a 21) (a 17) 0 d17 c53 (by decide +kernel)
  have t11 : a 21 ∈ [6] := remove (a 21) 0 [0,6] d21 b11
  have b12 : a 23 ≠ 0 := exclude [6] (fun u v => edge r63 v u) (a 23) (a 21) 0 t11 c63 (by decide +kernel)
  have t12 : a 23 ∈ [1] := remove (a 23) 0 [0,1] d23 b12
  have b13 : a 5 ≠ 0 := exclude [1] (fun u v => edge r16 v u) (a 5) (a 4) 0 d4 c16 (by decide +kernel)
  have t13 : a 5 ∈ [2] := remove (a 5) 0 [0,2] d5 b13
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (t13)))))))))))))
#print axioms chunk24
#print axioms chunk25
end PartitionCover205_201
