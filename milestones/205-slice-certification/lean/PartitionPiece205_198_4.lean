import PartitionData205_198
namespace PartitionCover205_198
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk16 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,1])
    (d2 : a 2 ∈ [1])
    (d10 : a 10 ∈ [0,2])
    (d7 : a 7 ∈ [0,1])
    (d11 : a 11 ∈ [0,1])
    (d5 : a 5 ∈ [0,2])
    (d13 : a 13 ∈ [0,4])
    (d21 : a 21 ∈ [0,6])
    (d15 : a 15 ∈ [0,1])
    (d8 : a 8 ∈ [0,1])
    (d12 : a 12 ∈ [0,1])
    (d24 : a 24 ∈ [0,6])
    (d9 : a 9 ∈ [0,1])
    (d26 : a 26 ∈ [0,4])
    (d27 : a 27 ∈ [0,1])
    (d16 : a 16 ∈ [0,3])
    (d17 : a 17 ∈ [0,6])
    (c9 : edge r9 (a 2) (a 3)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    (c20 : edge r20 (a 5) (a 7)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c30 : edge r30 (a 8) (a 12)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    (c51 : edge r51 (a 16) (a 24)=true)
    (c53 : edge r53 (a 17) (a 21)=true)
    : a 3 ∈ [1] ∧ a 10 ∈ [2] ∧ a 7 ∈ [1] ∧ a 11 ∈ [1] ∧ a 5 ∈ [2] ∧ a 13 ∈ [4] ∧ a 21 ∈ [6] ∧ a 15 ∈ [1] ∧ a 8 ∈ [1] ∧ a 12 ∈ [1] ∧ a 24 ∈ [6] ∧ a 9 ∈ [1] ∧ a 26 ∈ [4] ∧ a 27 ∈ [1] ∧ a 16 ∈ [3] ∧ a 17 ∈ [6] := by
  have b0 : a 3 ≠ 0 := exclude [1] (fun u v => edge r9 v u) (a 3) (a 2) 0 d2 c9 (by decide +kernel)
  have t0 : a 3 ∈ [1] := remove (a 3) 0 [0,1] d3 b0
  have b1 : a 10 ≠ 0 := exclude [1] (fun u v => edge r11 v u) (a 10) (a 2) 0 d2 c11 (by decide +kernel)
  have t1 : a 10 ∈ [2] := remove (a 10) 0 [0,2] d10 b1
  have b2 : a 7 ≠ 0 := exclude [1] (fun u v => edge r13 v u) (a 7) (a 3) 0 t0 c13 (by decide +kernel)
  have t2 : a 7 ∈ [1] := remove (a 7) 0 [0,1] d7 b2
  have b3 : a 11 ≠ 0 := exclude [1] (fun u v => edge r14 v u) (a 11) (a 3) 0 t0 c14 (by decide +kernel)
  have t3 : a 11 ∈ [1] := remove (a 11) 0 [0,1] d11 b3
  have b4 : a 5 ≠ 0 := exclude [1] (edge r20) (a 5) (a 7) 0 t2 c20 (by decide +kernel)
  have t4 : a 5 ∈ [2] := remove (a 5) 0 [0,2] d5 b4
  have b5 : a 13 ≠ 0 := exclude [2] (fun u v => edge r21 v u) (a 13) (a 5) 0 t4 c21 (by decide +kernel)
  have t5 : a 13 ∈ [4] := remove (a 13) 0 [0,4] d13 b5
  have b6 : a 21 ≠ 0 := exclude [2] (fun u v => edge r22 v u) (a 21) (a 5) 0 t4 c22 (by decide +kernel)
  have t6 : a 21 ∈ [6] := remove (a 21) 0 [0,6] d21 b6
  have b7 : a 15 ≠ 0 := exclude [1] (fun u v => edge r26 v u) (a 15) (a 7) 0 t2 c26 (by decide +kernel)
  have t7 : a 15 ∈ [1] := remove (a 15) 0 [0,1] d15 b7
  have b8 : a 8 ≠ 0 := exclude [2] (edge r29) (a 8) (a 10) 0 t1 c29 (by decide +kernel)
  have t8 : a 8 ∈ [1] := remove (a 8) 0 [0,1] d8 b8
  have b9 : a 12 ≠ 0 := exclude [1] (fun u v => edge r30 v u) (a 12) (a 8) 0 t8 c30 (by decide +kernel)
  have t9 : a 12 ∈ [1] := remove (a 12) 0 [0,1] d12 b9
  have b10 : a 24 ≠ 0 := exclude [1] (fun u v => edge r31 v u) (a 24) (a 8) 0 t8 c31 (by decide +kernel)
  have t10 : a 24 ∈ [6] := remove (a 24) 0 [0,6] d24 b10
  have b11 : a 9 ≠ 0 := exclude [1] (edge r32) (a 9) (a 11) 0 t3 c32 (by decide +kernel)
  have t11 : a 9 ∈ [1] := remove (a 9) 0 [0,1] d9 b11
  have b12 : a 26 ≠ 0 := exclude [2] (fun u v => edge r37 v u) (a 26) (a 10) 0 t1 c37 (by decide +kernel)
  have t12 : a 26 ∈ [4] := remove (a 26) 0 [0,4] d26 b12
  have b13 : a 27 ≠ 0 := exclude [1] (fun u v => edge r39 v u) (a 27) (a 11) 0 t3 c39 (by decide +kernel)
  have t13 : a 27 ∈ [1] := remove (a 27) 0 [0,1] d27 b13
  have b14 : a 16 ≠ 0 := exclude [6] (edge r51) (a 16) (a 24) 0 t10 c51 (by decide +kernel)
  have t14 : a 16 ∈ [3] := remove (a 16) 0 [0,3] d16 b14
  have b15 : a 17 ≠ 0 := exclude [6] (edge r53) (a 17) (a 21) 0 t6 c53 (by decide +kernel)
  have t15 : a 17 ∈ [6] := remove (a 17) 0 [0,6] d17 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk17 (a : Nat → Nat)
    (d19 : a 19 ∈ [0,1])
    (d27 : a 27 ∈ [1])
    (d29 : a 29 ∈ [0,6])
    (d21 : a 21 ∈ [6])
    (d25 : a 25 ∈ [0,1])
    (d24 : a 24 ∈ [6])
    (d30 : a 30 ∈ [0,4])
    (d26 : a 26 ∈ [4])
    (d31 : a 31 ∈ [0,1])
    (d4 : a 4 ∈ [0,2])
    (d5 : a 5 ∈ [2])
    (d23 : a 23 ∈ [0,1])
    (d22 : a 22 ∈ [0,3])
    (c16 : edge r16 (a 4) (a 5)=true)
    (c58 : edge r58 (a 19) (a 23)=true)
    (c59 : edge r59 (a 19) (a 27)=true)
    (c64 : edge r64 (a 21) (a 29)=true)
    (c65 : edge r65 (a 22) (a 23)=true)
    (c68 : edge r68 (a 24) (a 25)=true)
    (c74 : edge r74 (a 26) (a 30)=true)
    (c75 : edge r75 (a 27) (a 31)=true)
    : a 19 ∈ [1] ∧ a 29 ∈ [6] ∧ a 25 ∈ [1] ∧ a 30 ∈ [4] ∧ a 31 ∈ [1] ∧ a 4 ∈ [2] ∧ a 23 ∈ [1] ∧ a 22 ∈ [3] := by
  have b0 : a 19 ≠ 0 := exclude [1] (edge r59) (a 19) (a 27) 0 d27 c59 (by decide +kernel)
  have t0 : a 19 ∈ [1] := remove (a 19) 0 [0,1] d19 b0
  have b1 : a 29 ≠ 0 := exclude [6] (fun u v => edge r64 v u) (a 29) (a 21) 0 d21 c64 (by decide +kernel)
  have t1 : a 29 ∈ [6] := remove (a 29) 0 [0,6] d29 b1
  have b2 : a 25 ≠ 0 := exclude [6] (fun u v => edge r68 v u) (a 25) (a 24) 0 d24 c68 (by decide +kernel)
  have t2 : a 25 ∈ [1] := remove (a 25) 0 [0,1] d25 b2
  have b3 : a 30 ≠ 0 := exclude [4] (fun u v => edge r74 v u) (a 30) (a 26) 0 d26 c74 (by decide +kernel)
  have t3 : a 30 ∈ [4] := remove (a 30) 0 [0,4] d30 b3
  have b4 : a 31 ≠ 0 := exclude [1] (fun u v => edge r75 v u) (a 31) (a 27) 0 d27 c75 (by decide +kernel)
  have t4 : a 31 ∈ [1] := remove (a 31) 0 [0,1] d31 b4
  have b5 : a 4 ≠ 0 := exclude [2] (edge r16) (a 4) (a 5) 0 d5 c16 (by decide +kernel)
  have t5 : a 4 ∈ [2] := remove (a 4) 0 [0,2] d4 b5
  have b6 : a 23 ≠ 0 := exclude [1] (fun u v => edge r58 v u) (a 23) (a 19) 0 t0 c58 (by decide +kernel)
  have t6 : a 23 ∈ [1] := remove (a 23) 0 [0,1] d23 b6
  have b7 : a 22 ≠ 0 := exclude [1] (edge r65) (a 22) (a 23) 0 t6 c65 (by decide +kernel)
  have t7 : a 22 ∈ [3] := remove (a 22) 0 [0,3] d22 b7
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (t7)))))))
#print axioms chunk16
#print axioms chunk17
end PartitionCover205_198
