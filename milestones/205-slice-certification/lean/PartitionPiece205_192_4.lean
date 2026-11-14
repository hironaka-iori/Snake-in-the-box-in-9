import PartitionData205_192
namespace PartitionCover205_192
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk16 (a : Nat → Nat)
    (d29 : a 29 ∈ [0,8])
    (d13 : a 13 ∈ [0])
    (d30 : a 30 ∈ [0,6])
    (d14 : a 14 ∈ [0])
    (d16 : a 16 ∈ [0,1])
    (d18 : a 18 ∈ [0])
    (d17 : a 17 ∈ [0,1])
    (d21 : a 21 ∈ [0])
    (d25 : a 25 ∈ [0,8])
    (d26 : a 26 ∈ [0,6])
    (d31 : a 31 ∈ [0,6])
    (d27 : a 27 ∈ [0,3])
    (c44 : edge r44 (a 13) (a 29)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c49 : edge r49 (a 16) (a 18)=true)
    (c53 : edge r53 (a 17) (a 21)=true)
    (c71 : edge r71 (a 25) (a 27)=true)
    (c72 : edge r72 (a 25) (a 29)=true)
    (c74 : edge r74 (a 26) (a 30)=true)
    (c79 : edge r79 (a 30) (a 31)=true)
    : a 29 ∈ [0] ∧ a 30 ∈ [0] ∧ a 16 ∈ [0] ∧ a 17 ∈ [0] ∧ a 25 ∈ [0] ∧ a 26 ∈ [0] ∧ a 31 ∈ [0] ∧ a 27 ∈ [0] := by
  have b0 : a 29 ≠ 8 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 8 d13 c44 (by decide +kernel)
  have t0 : a 29 ∈ [0] := remove (a 29) 8 [0,8] d29 b0
  have b1 : a 30 ≠ 6 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 6 d14 c46 (by decide +kernel)
  have t1 : a 30 ∈ [0] := remove (a 30) 6 [0,6] d30 b1
  have b2 : a 16 ≠ 1 := exclude [0] (edge r49) (a 16) (a 18) 1 d18 c49 (by decide +kernel)
  have t2 : a 16 ∈ [0] := remove (a 16) 1 [0,1] d16 b2
  have b3 : a 17 ≠ 1 := exclude [0] (edge r53) (a 17) (a 21) 1 d21 c53 (by decide +kernel)
  have t3 : a 17 ∈ [0] := remove (a 17) 1 [0,1] d17 b3
  have b4 : a 25 ≠ 8 := exclude [0] (edge r72) (a 25) (a 29) 8 t0 c72 (by decide +kernel)
  have t4 : a 25 ∈ [0] := remove (a 25) 8 [0,8] d25 b4
  have b5 : a 26 ≠ 6 := exclude [0] (edge r74) (a 26) (a 30) 6 t1 c74 (by decide +kernel)
  have t5 : a 26 ∈ [0] := remove (a 26) 6 [0,6] d26 b5
  have b6 : a 31 ≠ 6 := exclude [0] (fun u v => edge r79 v u) (a 31) (a 30) 6 t1 c79 (by decide +kernel)
  have t6 : a 31 ∈ [0] := remove (a 31) 6 [0,6] d31 b6
  have b7 : a 27 ≠ 3 := exclude [0] (fun u v => edge r71 v u) (a 27) (a 25) 3 t4 c71 (by decide +kernel)
  have t7 : a 27 ∈ [0] := remove (a 27) 3 [0,3] d27 b7
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (t7)))))))

theorem chunk17 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,2])
    (d1 : a 1 ∈ [1])
    (d2 : a 2 ∈ [0,2])
    (d6 : a 6 ∈ [0,6])
    (d10 : a 10 ∈ [0,4])
    (d18 : a 18 ∈ [0,1])
    (d7 : a 7 ∈ [0,3])
    (d5 : a 5 ∈ [0,1])
    (d13 : a 13 ∈ [0,4])
    (d21 : a 21 ∈ [0,1])
    (d14 : a 14 ∈ [0,4])
    (d15 : a 15 ∈ [0,6])
    (d23 : a 23 ∈ [0,1])
    (d8 : a 8 ∈ [0,2])
    (d12 : a 12 ∈ [0,1])
    (d9 : a 9 ∈ [0,4])
    (d28 : a 28 ∈ [0,1])
    (c5 : edge r5 (a 1) (a 3)=true)
    (c9 : edge r9 (a 2) (a 3)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    (c12 : edge r12 (a 2) (a 18)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c20 : edge r20 (a 5) (a 7)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c30 : edge r30 (a 8) (a 12)=true)
    (c33 : edge r33 (a 9) (a 13)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    : a 3 ∈ [2] ∧ a 2 ∈ [2] ∧ a 6 ∈ [6] ∧ a 10 ∈ [4] ∧ a 18 ∈ [1] ∧ a 7 ∈ [3] ∧ a 5 ∈ [1] ∧ a 13 ∈ [4] ∧ a 21 ∈ [1] ∧ a 14 ∈ [4] ∧ a 15 ∈ [6] ∧ a 23 ∈ [1] ∧ a 8 ∈ [2] ∧ a 12 ∈ [1] ∧ a 9 ∈ [4] ∧ a 28 ∈ [1] := by
  have b0 : a 3 ≠ 0 := exclude [1] (fun u v => edge r5 v u) (a 3) (a 1) 0 d1 c5 (by decide +kernel)
  have t0 : a 3 ∈ [2] := remove (a 3) 0 [0,2] d3 b0
  have b1 : a 2 ≠ 0 := exclude [2] (edge r9) (a 2) (a 3) 0 t0 c9 (by decide +kernel)
  have t1 : a 2 ∈ [2] := remove (a 2) 0 [0,2] d2 b1
  have b2 : a 6 ≠ 0 := exclude [2] (fun u v => edge r10 v u) (a 6) (a 2) 0 t1 c10 (by decide +kernel)
  have t2 : a 6 ∈ [6] := remove (a 6) 0 [0,6] d6 b2
  have b3 : a 10 ≠ 0 := exclude [2] (fun u v => edge r11 v u) (a 10) (a 2) 0 t1 c11 (by decide +kernel)
  have t3 : a 10 ∈ [4] := remove (a 10) 0 [0,4] d10 b3
  have b4 : a 18 ≠ 0 := exclude [2] (fun u v => edge r12 v u) (a 18) (a 2) 0 t1 c12 (by decide +kernel)
  have t4 : a 18 ∈ [1] := remove (a 18) 0 [0,1] d18 b4
  have b5 : a 7 ≠ 0 := exclude [2] (fun u v => edge r13 v u) (a 7) (a 3) 0 t0 c13 (by decide +kernel)
  have t5 : a 7 ∈ [3] := remove (a 7) 0 [0,3] d7 b5
  have b6 : a 5 ≠ 0 := exclude [3] (edge r20) (a 5) (a 7) 0 t5 c20 (by decide +kernel)
  have t6 : a 5 ∈ [1] := remove (a 5) 0 [0,1] d5 b6
  have b7 : a 13 ≠ 0 := exclude [1] (fun u v => edge r21 v u) (a 13) (a 5) 0 t6 c21 (by decide +kernel)
  have t7 : a 13 ∈ [4] := remove (a 13) 0 [0,4] d13 b7
  have b8 : a 21 ≠ 0 := exclude [1] (fun u v => edge r22 v u) (a 21) (a 5) 0 t6 c22 (by decide +kernel)
  have t8 : a 21 ∈ [1] := remove (a 21) 0 [0,1] d21 b8
  have b9 : a 14 ≠ 0 := exclude [6] (fun u v => edge r24 v u) (a 14) (a 6) 0 t2 c24 (by decide +kernel)
  have t9 : a 14 ∈ [4] := remove (a 14) 0 [0,4] d14 b9
  have b10 : a 15 ≠ 0 := exclude [3] (fun u v => edge r26 v u) (a 15) (a 7) 0 t5 c26 (by decide +kernel)
  have t10 : a 15 ∈ [6] := remove (a 15) 0 [0,6] d15 b10
  have b11 : a 23 ≠ 0 := exclude [3] (fun u v => edge r27 v u) (a 23) (a 7) 0 t5 c27 (by decide +kernel)
  have t11 : a 23 ∈ [1] := remove (a 23) 0 [0,1] d23 b11
  have b12 : a 8 ≠ 0 := exclude [4] (edge r29) (a 8) (a 10) 0 t3 c29 (by decide +kernel)
  have t12 : a 8 ∈ [2] := remove (a 8) 0 [0,2] d8 b12
  have b13 : a 12 ≠ 0 := exclude [2] (fun u v => edge r30 v u) (a 12) (a 8) 0 t12 c30 (by decide +kernel)
  have t13 : a 12 ∈ [1] := remove (a 12) 0 [0,1] d12 b13
  have b14 : a 9 ≠ 0 := exclude [4] (edge r33) (a 9) (a 13) 0 t7 c33 (by decide +kernel)
  have t14 : a 9 ∈ [4] := remove (a 9) 0 [0,4] d9 b14
  have b15 : a 28 ≠ 0 := exclude [1] (fun u v => edge r42 v u) (a 28) (a 12) 0 t13 c42 (by decide +kernel)
  have t15 : a 28 ∈ [1] := remove (a 28) 0 [0,1] d28 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk18 (a : Nat → Nat)
    (d29 : a 29 ∈ [0,8])
    (d13 : a 13 ∈ [4])
    (d30 : a 30 ∈ [0,6])
    (d14 : a 14 ∈ [4])
    (d16 : a 16 ∈ [0,1])
    (d18 : a 18 ∈ [1])
    (d17 : a 17 ∈ [0,1])
    (d21 : a 21 ∈ [1])
    (d25 : a 25 ∈ [0,8])
    (d26 : a 26 ∈ [0,6])
    (d31 : a 31 ∈ [0,6])
    (d27 : a 27 ∈ [0,3])
    (c44 : edge r44 (a 13) (a 29)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c49 : edge r49 (a 16) (a 18)=true)
    (c53 : edge r53 (a 17) (a 21)=true)
    (c71 : edge r71 (a 25) (a 27)=true)
    (c72 : edge r72 (a 25) (a 29)=true)
    (c74 : edge r74 (a 26) (a 30)=true)
    (c79 : edge r79 (a 30) (a 31)=true)
    : a 29 ∈ [8] ∧ a 30 ∈ [6] ∧ a 16 ∈ [1] ∧ a 17 ∈ [1] ∧ a 25 ∈ [8] ∧ a 26 ∈ [6] ∧ a 31 ∈ [6] ∧ a 27 ∈ [3] := by
  have b0 : a 29 ≠ 0 := exclude [4] (fun u v => edge r44 v u) (a 29) (a 13) 0 d13 c44 (by decide +kernel)
  have t0 : a 29 ∈ [8] := remove (a 29) 0 [0,8] d29 b0
  have b1 : a 30 ≠ 0 := exclude [4] (fun u v => edge r46 v u) (a 30) (a 14) 0 d14 c46 (by decide +kernel)
  have t1 : a 30 ∈ [6] := remove (a 30) 0 [0,6] d30 b1
  have b2 : a 16 ≠ 0 := exclude [1] (edge r49) (a 16) (a 18) 0 d18 c49 (by decide +kernel)
  have t2 : a 16 ∈ [1] := remove (a 16) 0 [0,1] d16 b2
  have b3 : a 17 ≠ 0 := exclude [1] (edge r53) (a 17) (a 21) 0 d21 c53 (by decide +kernel)
  have t3 : a 17 ∈ [1] := remove (a 17) 0 [0,1] d17 b3
  have b4 : a 25 ≠ 0 := exclude [8] (edge r72) (a 25) (a 29) 0 t0 c72 (by decide +kernel)
  have t4 : a 25 ∈ [8] := remove (a 25) 0 [0,8] d25 b4
  have b5 : a 26 ≠ 0 := exclude [6] (edge r74) (a 26) (a 30) 0 t1 c74 (by decide +kernel)
  have t5 : a 26 ∈ [6] := remove (a 26) 0 [0,6] d26 b5
  have b6 : a 31 ≠ 0 := exclude [6] (fun u v => edge r79 v u) (a 31) (a 30) 0 t1 c79 (by decide +kernel)
  have t6 : a 31 ∈ [6] := remove (a 31) 0 [0,6] d31 b6
  have b7 : a 27 ≠ 0 := exclude [8] (fun u v => edge r71 v u) (a 27) (a 25) 0 t4 c71 (by decide +kernel)
  have t7 : a 27 ∈ [3] := remove (a 27) 0 [0,3] d27 b7
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (t7)))))))
#print axioms chunk16
#print axioms chunk17
#print axioms chunk18
end PartitionCover205_192
