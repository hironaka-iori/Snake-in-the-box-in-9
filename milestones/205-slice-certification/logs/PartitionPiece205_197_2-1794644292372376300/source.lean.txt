import PartitionData205_197
namespace PartitionCover205_197
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,1])
    (d2 : a 2 ∈ [0])
    (d10 : a 10 ∈ [0,1])
    (d7 : a 7 ∈ [0,1])
    (d11 : a 11 ∈ [0,3])
    (d5 : a 5 ∈ [0,1])
    (d13 : a 13 ∈ [0,2])
    (d21 : a 21 ∈ [0,4])
    (d9 : a 9 ∈ [0,1])
    (d25 : a 25 ∈ [0,2])
    (d12 : a 12 ∈ [0,1])
    (d28 : a 28 ∈ [0,1])
    (d15 : a 15 ∈ [0,1])
    (d29 : a 29 ∈ [0,4])
    (d17 : a 17 ∈ [0,4])
    (d30 : a 30 ∈ [0,2])
    (d4 : a 4 ∈ [0,2])
    (c9 : edge r9 (a 2) (a 3)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c20 : edge r20 (a 5) (a 7)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    (c40 : edge r40 (a 12) (a 13)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    (c43 : edge r43 (a 13) (a 15)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    (c53 : edge r53 (a 17) (a 21)=true)
    (c77 : edge r77 (a 28) (a 30)=true)
    : a 3 ∈ [0] ∧ a 10 ∈ [0] ∧ a 7 ∈ [0] ∧ a 11 ∈ [0] ∧ a 5 ∈ [0] ∧ a 13 ∈ [0] ∧ a 21 ∈ [0] ∧ a 9 ∈ [0] ∧ a 25 ∈ [0] ∧ a 12 ∈ [0] ∧ a 28 ∈ [0] ∧ a 15 ∈ [0] ∧ a 29 ∈ [0] ∧ a 17 ∈ [0] ∧ a 30 ∈ [0] ∧ a 4 ∈ [0] := by
  have b0 : a 3 ≠ 1 := exclude [0] (fun u v => edge r9 v u) (a 3) (a 2) 1 d2 c9 (by decide +kernel)
  have t0 : a 3 ∈ [0] := remove (a 3) 1 [0,1] d3 b0
  have b1 : a 10 ≠ 1 := exclude [0] (fun u v => edge r11 v u) (a 10) (a 2) 1 d2 c11 (by decide +kernel)
  have t1 : a 10 ∈ [0] := remove (a 10) 1 [0,1] d10 b1
  have b2 : a 7 ≠ 1 := exclude [0] (fun u v => edge r13 v u) (a 7) (a 3) 1 t0 c13 (by decide +kernel)
  have t2 : a 7 ∈ [0] := remove (a 7) 1 [0,1] d7 b2
  have b3 : a 11 ≠ 3 := exclude [0] (fun u v => edge r14 v u) (a 11) (a 3) 3 t0 c14 (by decide +kernel)
  have t3 : a 11 ∈ [0] := remove (a 11) 3 [0,3] d11 b3
  have b4 : a 5 ≠ 1 := exclude [0] (edge r20) (a 5) (a 7) 1 t2 c20 (by decide +kernel)
  have t4 : a 5 ∈ [0] := remove (a 5) 1 [0,1] d5 b4
  have b5 : a 13 ≠ 2 := exclude [0] (fun u v => edge r21 v u) (a 13) (a 5) 2 t4 c21 (by decide +kernel)
  have t5 : a 13 ∈ [0] := remove (a 13) 2 [0,2] d13 b5
  have b6 : a 21 ≠ 4 := exclude [0] (fun u v => edge r22 v u) (a 21) (a 5) 4 t4 c22 (by decide +kernel)
  have t6 : a 21 ∈ [0] := remove (a 21) 4 [0,4] d21 b6
  have b7 : a 9 ≠ 1 := exclude [0] (edge r32) (a 9) (a 11) 1 t3 c32 (by decide +kernel)
  have t7 : a 9 ∈ [0] := remove (a 9) 1 [0,1] d9 b7
  have b8 : a 25 ≠ 2 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 2 t7 c34 (by decide +kernel)
  have t8 : a 25 ∈ [0] := remove (a 25) 2 [0,2] d25 b8
  have b9 : a 12 ≠ 1 := exclude [0] (edge r40) (a 12) (a 13) 1 t5 c40 (by decide +kernel)
  have t9 : a 12 ∈ [0] := remove (a 12) 1 [0,1] d12 b9
  have b10 : a 28 ≠ 1 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 1 t9 c42 (by decide +kernel)
  have t10 : a 28 ∈ [0] := remove (a 28) 1 [0,1] d28 b10
  have b11 : a 15 ≠ 1 := exclude [0] (fun u v => edge r43 v u) (a 15) (a 13) 1 t5 c43 (by decide +kernel)
  have t11 : a 15 ∈ [0] := remove (a 15) 1 [0,1] d15 b11
  have b12 : a 29 ≠ 4 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 4 t5 c44 (by decide +kernel)
  have t12 : a 29 ∈ [0] := remove (a 29) 4 [0,4] d29 b12
  have b13 : a 17 ≠ 4 := exclude [0] (edge r53) (a 17) (a 21) 4 t6 c53 (by decide +kernel)
  have t13 : a 17 ∈ [0] := remove (a 17) 4 [0,4] d17 b13
  have b14 : a 30 ≠ 2 := exclude [0] (fun u v => edge r77 v u) (a 30) (a 28) 2 t10 c77 (by decide +kernel)
  have t14 : a 30 ∈ [0] := remove (a 30) 2 [0,2] d30 b14
  have b15 : a 4 ≠ 2 := exclude [0] (edge r16) (a 4) (a 5) 2 t4 c16 (by decide +kernel)
  have t15 : a 4 ∈ [0] := remove (a 4) 2 [0,2] d4 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk9 (a : Nat → Nat)
    (d8 : a 8 ∈ [0,1])
    (d9 : a 9 ∈ [0])
    (d16 : a 16 ∈ [0,4])
    (d17 : a 17 ∈ [0])
    (d24 : a 24 ∈ [0,8])
    (d22 : a 22 ∈ [0,2])
    (d30 : a 30 ∈ [0])
    (d26 : a 26 ∈ [0,2])
    (d23 : a 23 ∈ [0,4])
    (d19 : a 19 ∈ [0,4])
    (d27 : a 27 ∈ [0,4])
    (c28 : edge r28 (a 8) (a 9)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c51 : edge r51 (a 16) (a 24)=true)
    (c58 : edge r58 (a 19) (a 23)=true)
    (c59 : edge r59 (a 19) (a 27)=true)
    (c65 : edge r65 (a 22) (a 23)=true)
    (c66 : edge r66 (a 22) (a 30)=true)
    (c74 : edge r74 (a 26) (a 30)=true)
    : a 8 ∈ [0] ∧ a 16 ∈ [0] ∧ a 24 ∈ [0] ∧ a 22 ∈ [0] ∧ a 26 ∈ [0] ∧ a 23 ∈ [0] ∧ a 19 ∈ [0] ∧ a 27 ∈ [0] := by
  have b0 : a 8 ≠ 1 := exclude [0] (edge r28) (a 8) (a 9) 1 d9 c28 (by decide +kernel)
  have t0 : a 8 ∈ [0] := remove (a 8) 1 [0,1] d8 b0
  have b1 : a 16 ≠ 4 := exclude [0] (edge r48) (a 16) (a 17) 4 d17 c48 (by decide +kernel)
  have t1 : a 16 ∈ [0] := remove (a 16) 4 [0,4] d16 b1
  have b2 : a 24 ≠ 8 := exclude [0] (fun u v => edge r51 v u) (a 24) (a 16) 8 t1 c51 (by decide +kernel)
  have t2 : a 24 ∈ [0] := remove (a 24) 8 [0,8] d24 b2
  have b3 : a 22 ≠ 2 := exclude [0] (edge r66) (a 22) (a 30) 2 d30 c66 (by decide +kernel)
  have t3 : a 22 ∈ [0] := remove (a 22) 2 [0,2] d22 b3
  have b4 : a 26 ≠ 2 := exclude [0] (edge r74) (a 26) (a 30) 2 d30 c74 (by decide +kernel)
  have t4 : a 26 ∈ [0] := remove (a 26) 2 [0,2] d26 b4
  have b5 : a 23 ≠ 4 := exclude [0] (fun u v => edge r65 v u) (a 23) (a 22) 4 t3 c65 (by decide +kernel)
  have t5 : a 23 ∈ [0] := remove (a 23) 4 [0,4] d23 b5
  have b6 : a 19 ≠ 4 := exclude [0] (edge r58) (a 19) (a 23) 4 t5 c58 (by decide +kernel)
  have t6 : a 19 ∈ [0] := remove (a 19) 4 [0,4] d19 b6
  have b7 : a 27 ≠ 4 := exclude [0] (fun u v => edge r59 v u) (a 27) (a 19) 4 t6 c59 (by decide +kernel)
  have t7 : a 27 ∈ [0] := remove (a 27) 4 [0,4] d27 b7
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (t7)))))))

theorem chunk10 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,1])
    (d2 : a 2 ∈ [1])
    (d10 : a 10 ∈ [0,1])
    (d7 : a 7 ∈ [0,1])
    (d11 : a 11 ∈ [0,3])
    (d5 : a 5 ∈ [0,1])
    (d13 : a 13 ∈ [0,2])
    (d21 : a 21 ∈ [0,4])
    (d9 : a 9 ∈ [0,1])
    (d25 : a 25 ∈ [0,2])
    (d12 : a 12 ∈ [0,1])
    (d28 : a 28 ∈ [0,1])
    (d15 : a 15 ∈ [0,1])
    (d29 : a 29 ∈ [0,4])
    (d17 : a 17 ∈ [0,4])
    (d30 : a 30 ∈ [0,2])
    (d4 : a 4 ∈ [0,2])
    (c9 : edge r9 (a 2) (a 3)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c20 : edge r20 (a 5) (a 7)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    (c40 : edge r40 (a 12) (a 13)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    (c43 : edge r43 (a 13) (a 15)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    (c53 : edge r53 (a 17) (a 21)=true)
    (c77 : edge r77 (a 28) (a 30)=true)
    : a 3 ∈ [1] ∧ a 10 ∈ [1] ∧ a 7 ∈ [1] ∧ a 11 ∈ [3] ∧ a 5 ∈ [1] ∧ a 13 ∈ [2] ∧ a 21 ∈ [4] ∧ a 9 ∈ [1] ∧ a 25 ∈ [2] ∧ a 12 ∈ [1] ∧ a 28 ∈ [1] ∧ a 15 ∈ [1] ∧ a 29 ∈ [4] ∧ a 17 ∈ [4] ∧ a 30 ∈ [2] ∧ a 4 ∈ [2] := by
  have b0 : a 3 ≠ 0 := exclude [1] (fun u v => edge r9 v u) (a 3) (a 2) 0 d2 c9 (by decide +kernel)
  have t0 : a 3 ∈ [1] := remove (a 3) 0 [0,1] d3 b0
  have b1 : a 10 ≠ 0 := exclude [1] (fun u v => edge r11 v u) (a 10) (a 2) 0 d2 c11 (by decide +kernel)
  have t1 : a 10 ∈ [1] := remove (a 10) 0 [0,1] d10 b1
  have b2 : a 7 ≠ 0 := exclude [1] (fun u v => edge r13 v u) (a 7) (a 3) 0 t0 c13 (by decide +kernel)
  have t2 : a 7 ∈ [1] := remove (a 7) 0 [0,1] d7 b2
  have b3 : a 11 ≠ 0 := exclude [1] (fun u v => edge r14 v u) (a 11) (a 3) 0 t0 c14 (by decide +kernel)
  have t3 : a 11 ∈ [3] := remove (a 11) 0 [0,3] d11 b3
  have b4 : a 5 ≠ 0 := exclude [1] (edge r20) (a 5) (a 7) 0 t2 c20 (by decide +kernel)
  have t4 : a 5 ∈ [1] := remove (a 5) 0 [0,1] d5 b4
  have b5 : a 13 ≠ 0 := exclude [1] (fun u v => edge r21 v u) (a 13) (a 5) 0 t4 c21 (by decide +kernel)
  have t5 : a 13 ∈ [2] := remove (a 13) 0 [0,2] d13 b5
  have b6 : a 21 ≠ 0 := exclude [1] (fun u v => edge r22 v u) (a 21) (a 5) 0 t4 c22 (by decide +kernel)
  have t6 : a 21 ∈ [4] := remove (a 21) 0 [0,4] d21 b6
  have b7 : a 9 ≠ 0 := exclude [3] (edge r32) (a 9) (a 11) 0 t3 c32 (by decide +kernel)
  have t7 : a 9 ∈ [1] := remove (a 9) 0 [0,1] d9 b7
  have b8 : a 25 ≠ 0 := exclude [1] (fun u v => edge r34 v u) (a 25) (a 9) 0 t7 c34 (by decide +kernel)
  have t8 : a 25 ∈ [2] := remove (a 25) 0 [0,2] d25 b8
  have b9 : a 12 ≠ 0 := exclude [2] (edge r40) (a 12) (a 13) 0 t5 c40 (by decide +kernel)
  have t9 : a 12 ∈ [1] := remove (a 12) 0 [0,1] d12 b9
  have b10 : a 28 ≠ 0 := exclude [1] (fun u v => edge r42 v u) (a 28) (a 12) 0 t9 c42 (by decide +kernel)
  have t10 : a 28 ∈ [1] := remove (a 28) 0 [0,1] d28 b10
  have b11 : a 15 ≠ 0 := exclude [2] (fun u v => edge r43 v u) (a 15) (a 13) 0 t5 c43 (by decide +kernel)
  have t11 : a 15 ∈ [1] := remove (a 15) 0 [0,1] d15 b11
  have b12 : a 29 ≠ 0 := exclude [2] (fun u v => edge r44 v u) (a 29) (a 13) 0 t5 c44 (by decide +kernel)
  have t12 : a 29 ∈ [4] := remove (a 29) 0 [0,4] d29 b12
  have b13 : a 17 ≠ 0 := exclude [4] (edge r53) (a 17) (a 21) 0 t6 c53 (by decide +kernel)
  have t13 : a 17 ∈ [4] := remove (a 17) 0 [0,4] d17 b13
  have b14 : a 30 ≠ 0 := exclude [1] (fun u v => edge r77 v u) (a 30) (a 28) 0 t10 c77 (by decide +kernel)
  have t14 : a 30 ∈ [2] := remove (a 30) 0 [0,2] d30 b14
  have b15 : a 4 ≠ 0 := exclude [1] (edge r16) (a 4) (a 5) 0 t4 c16 (by decide +kernel)
  have t15 : a 4 ∈ [2] := remove (a 4) 0 [0,2] d4 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk11 (a : Nat → Nat)
    (d8 : a 8 ∈ [0,1])
    (d9 : a 9 ∈ [1])
    (d16 : a 16 ∈ [0,4])
    (d17 : a 17 ∈ [4])
    (d24 : a 24 ∈ [0,8])
    (d22 : a 22 ∈ [0,2])
    (d30 : a 30 ∈ [2])
    (d26 : a 26 ∈ [0,2])
    (d23 : a 23 ∈ [0,4])
    (d19 : a 19 ∈ [0,4])
    (d27 : a 27 ∈ [0,4])
    (c28 : edge r28 (a 8) (a 9)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c51 : edge r51 (a 16) (a 24)=true)
    (c58 : edge r58 (a 19) (a 23)=true)
    (c59 : edge r59 (a 19) (a 27)=true)
    (c65 : edge r65 (a 22) (a 23)=true)
    (c66 : edge r66 (a 22) (a 30)=true)
    (c74 : edge r74 (a 26) (a 30)=true)
    : a 8 ∈ [1] ∧ a 16 ∈ [4] ∧ a 24 ∈ [8] ∧ a 22 ∈ [2] ∧ a 26 ∈ [2] ∧ a 23 ∈ [4] ∧ a 19 ∈ [4] ∧ a 27 ∈ [4] := by
  have b0 : a 8 ≠ 0 := exclude [1] (edge r28) (a 8) (a 9) 0 d9 c28 (by decide +kernel)
  have t0 : a 8 ∈ [1] := remove (a 8) 0 [0,1] d8 b0
  have b1 : a 16 ≠ 0 := exclude [4] (edge r48) (a 16) (a 17) 0 d17 c48 (by decide +kernel)
  have t1 : a 16 ∈ [4] := remove (a 16) 0 [0,4] d16 b1
  have b2 : a 24 ≠ 0 := exclude [4] (fun u v => edge r51 v u) (a 24) (a 16) 0 t1 c51 (by decide +kernel)
  have t2 : a 24 ∈ [8] := remove (a 24) 0 [0,8] d24 b2
  have b3 : a 22 ≠ 0 := exclude [2] (edge r66) (a 22) (a 30) 0 d30 c66 (by decide +kernel)
  have t3 : a 22 ∈ [2] := remove (a 22) 0 [0,2] d22 b3
  have b4 : a 26 ≠ 0 := exclude [2] (edge r74) (a 26) (a 30) 0 d30 c74 (by decide +kernel)
  have t4 : a 26 ∈ [2] := remove (a 26) 0 [0,2] d26 b4
  have b5 : a 23 ≠ 0 := exclude [2] (fun u v => edge r65 v u) (a 23) (a 22) 0 t3 c65 (by decide +kernel)
  have t5 : a 23 ∈ [4] := remove (a 23) 0 [0,4] d23 b5
  have b6 : a 19 ≠ 0 := exclude [4] (edge r58) (a 19) (a 23) 0 t5 c58 (by decide +kernel)
  have t6 : a 19 ∈ [4] := remove (a 19) 0 [0,4] d19 b6
  have b7 : a 27 ≠ 0 := exclude [4] (fun u v => edge r59 v u) (a 27) (a 19) 0 t6 c59 (by decide +kernel)
  have t7 : a 27 ∈ [4] := remove (a 27) 0 [0,4] d27 b7
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (t7)))))))
#print axioms chunk8
#print axioms chunk9
#print axioms chunk10
#print axioms chunk11
end PartitionCover205_197
