import PartitionData205_225
namespace PartitionCover205_225
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d36 : a 36 ∈ [0,1])
    (d37 : a 37 ∈ [0])
    (d30 : a 30 ∈ [0,1])
    (d29 : a 29 ∈ [0,1])
    (d31 : a 31 ∈ [0,2])
    (c91 : edge r91 (a 29) (a 30)=true)
    (c92 : edge r92 (a 29) (a 31)=true)
    (c96 : edge r96 (a 30) (a 36)=true)
    (c112 : edge r112 (a 36) (a 37)=true)
    : a 36 ∈ [0] ∧ a 30 ∈ [0] ∧ a 29 ∈ [0] ∧ a 31 ∈ [0] := by
  have b0 : a 36 ≠ 1 := exclude [0] (edge r112) (a 36) (a 37) 1 d37 c112 (by decide +kernel)
  have t0 : a 36 ∈ [0] := remove (a 36) 1 [0,1] d36 b0
  have b1 : a 30 ≠ 1 := exclude [0] (edge r96) (a 30) (a 36) 1 t0 c96 (by decide +kernel)
  have t1 : a 30 ∈ [0] := remove (a 30) 1 [0,1] d30 b1
  have b2 : a 29 ≠ 1 := exclude [0] (edge r91) (a 29) (a 30) 1 t1 c91 (by decide +kernel)
  have t2 : a 29 ∈ [0] := remove (a 29) 1 [0,1] d29 b2
  have b3 : a 31 ≠ 2 := exclude [0] (fun u v => edge r92 v u) (a 31) (a 29) 2 t2 c92 (by decide +kernel)
  have t3 : a 31 ∈ [0] := remove (a 31) 2 [0,2] d31 b3
  exact And.intro t0 (And.intro t1 (And.intro t2 (t3)))

theorem chunk5 (a : Nat → Nat)
    (d4 : a 4 ∈ [0,1])
    (d3 : a 3 ∈ [1])
    (d5 : a 5 ∈ [0,2])
    (d10 : a 10 ∈ [0,1])
    (d6 : a 6 ∈ [0,1])
    (d11 : a 11 ∈ [0,1])
    (d12 : a 12 ∈ [0,1])
    (d20 : a 20 ∈ [0,2])
    (d21 : a 21 ∈ [0,1])
    (d7 : a 7 ∈ [0,1])
    (d22 : a 22 ∈ [0,1])
    (d8 : a 8 ∈ [0,1])
    (d26 : a 26 ∈ [0,1])
    (d38 : a 38 ∈ [0,1])
    (d27 : a 27 ∈ [0,1])
    (d40 : a 40 ∈ [0,1])
    (d14 : a 14 ∈ [0,1])
    (c12 : edge r12 (a 3) (a 4)=true)
    (c13 : edge r13 (a 3) (a 5)=true)
    (c14 : edge r14 (a 3) (a 10)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c18 : edge r18 (a 4) (a 11)=true)
    (c22 : edge r22 (a 5) (a 12)=true)
    (c23 : edge r23 (a 5) (a 20)=true)
    (c26 : edge r26 (a 6) (a 21)=true)
    (c29 : edge r29 (a 7) (a 10)=true)
    (c30 : edge r30 (a 7) (a 22)=true)
    (c32 : edge r32 (a 8) (a 12)=true)
    (c39 : edge r39 (a 10) (a 26)=true)
    (c40 : edge r40 (a 10) (a 38)=true)
    (c44 : edge r44 (a 12) (a 27)=true)
    (c45 : edge r45 (a 12) (a 40)=true)
    (c51 : edge r51 (a 14) (a 22)=true)
    : a 4 ∈ [1] ∧ a 5 ∈ [2] ∧ a 10 ∈ [1] ∧ a 6 ∈ [1] ∧ a 11 ∈ [1] ∧ a 12 ∈ [1] ∧ a 20 ∈ [2] ∧ a 21 ∈ [1] ∧ a 7 ∈ [1] ∧ a 22 ∈ [1] ∧ a 8 ∈ [1] ∧ a 26 ∈ [1] ∧ a 38 ∈ [1] ∧ a 27 ∈ [1] ∧ a 40 ∈ [1] ∧ a 14 ∈ [1] := by
  have b0 : a 4 ≠ 0 := exclude [1] (fun u v => edge r12 v u) (a 4) (a 3) 0 d3 c12 (by decide +kernel)
  have t0 : a 4 ∈ [1] := remove (a 4) 0 [0,1] d4 b0
  have b1 : a 5 ≠ 0 := exclude [1] (fun u v => edge r13 v u) (a 5) (a 3) 0 d3 c13 (by decide +kernel)
  have t1 : a 5 ∈ [2] := remove (a 5) 0 [0,2] d5 b1
  have b2 : a 10 ≠ 0 := exclude [1] (fun u v => edge r14 v u) (a 10) (a 3) 0 d3 c14 (by decide +kernel)
  have t2 : a 10 ∈ [1] := remove (a 10) 0 [0,1] d10 b2
  have b3 : a 6 ≠ 0 := exclude [1] (fun u v => edge r17 v u) (a 6) (a 4) 0 t0 c17 (by decide +kernel)
  have t3 : a 6 ∈ [1] := remove (a 6) 0 [0,1] d6 b3
  have b4 : a 11 ≠ 0 := exclude [1] (fun u v => edge r18 v u) (a 11) (a 4) 0 t0 c18 (by decide +kernel)
  have t4 : a 11 ∈ [1] := remove (a 11) 0 [0,1] d11 b4
  have b5 : a 12 ≠ 0 := exclude [2] (fun u v => edge r22 v u) (a 12) (a 5) 0 t1 c22 (by decide +kernel)
  have t5 : a 12 ∈ [1] := remove (a 12) 0 [0,1] d12 b5
  have b6 : a 20 ≠ 0 := exclude [2] (fun u v => edge r23 v u) (a 20) (a 5) 0 t1 c23 (by decide +kernel)
  have t6 : a 20 ∈ [2] := remove (a 20) 0 [0,2] d20 b6
  have b7 : a 21 ≠ 0 := exclude [1] (fun u v => edge r26 v u) (a 21) (a 6) 0 t3 c26 (by decide +kernel)
  have t7 : a 21 ∈ [1] := remove (a 21) 0 [0,1] d21 b7
  have b8 : a 7 ≠ 0 := exclude [1] (edge r29) (a 7) (a 10) 0 t2 c29 (by decide +kernel)
  have t8 : a 7 ∈ [1] := remove (a 7) 0 [0,1] d7 b8
  have b9 : a 22 ≠ 0 := exclude [1] (fun u v => edge r30 v u) (a 22) (a 7) 0 t8 c30 (by decide +kernel)
  have t9 : a 22 ∈ [1] := remove (a 22) 0 [0,1] d22 b9
  have b10 : a 8 ≠ 0 := exclude [1] (edge r32) (a 8) (a 12) 0 t5 c32 (by decide +kernel)
  have t10 : a 8 ∈ [1] := remove (a 8) 0 [0,1] d8 b10
  have b11 : a 26 ≠ 0 := exclude [1] (fun u v => edge r39 v u) (a 26) (a 10) 0 t2 c39 (by decide +kernel)
  have t11 : a 26 ∈ [1] := remove (a 26) 0 [0,1] d26 b11
  have b12 : a 38 ≠ 0 := exclude [1] (fun u v => edge r40 v u) (a 38) (a 10) 0 t2 c40 (by decide +kernel)
  have t12 : a 38 ∈ [1] := remove (a 38) 0 [0,1] d38 b12
  have b13 : a 27 ≠ 0 := exclude [1] (fun u v => edge r44 v u) (a 27) (a 12) 0 t5 c44 (by decide +kernel)
  have t13 : a 27 ∈ [1] := remove (a 27) 0 [0,1] d27 b13
  have b14 : a 40 ≠ 0 := exclude [1] (fun u v => edge r45 v u) (a 40) (a 12) 0 t5 c45 (by decide +kernel)
  have t14 : a 40 ∈ [1] := remove (a 40) 0 [0,1] d40 b14
  have b15 : a 14 ≠ 0 := exclude [1] (edge r51) (a 14) (a 22) 0 t9 c51 (by decide +kernel)
  have t15 : a 14 ∈ [1] := remove (a 14) 0 [0,1] d14 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk6 (a : Nat → Nat)
    (d16 : a 16 ∈ [0,1])
    (d20 : a 20 ∈ [2])
    (d17 : a 17 ∈ [0,1])
    (d21 : a 21 ∈ [1])
    (d25 : a 25 ∈ [0,1])
    (d45 : a 45 ∈ [0,1])
    (d48 : a 48 ∈ [0,1])
    (d28 : a 28 ∈ [0,1])
    (d49 : a 49 ∈ [0,2])
    (d23 : a 23 ∈ [0,1])
    (d22 : a 22 ∈ [1])
    (d50 : a 50 ∈ [0,1])
    (d53 : a 53 ∈ [0,1])
    (d54 : a 54 ∈ [0,1])
    (d26 : a 26 ∈ [1])
    (d37 : a 37 ∈ [0,1])
    (d46 : a 46 ∈ [0,1])
    (d47 : a 47 ∈ [0,1])
    (d55 : a 55 ∈ [0,1])
    (d15 : a 15 ∈ [0,1])
    (d14 : a 14 ∈ [1])
    (c48 : edge r48 (a 14) (a 15)=true)
    (c58 : edge r58 (a 16) (a 20)=true)
    (c61 : edge r61 (a 17) (a 21)=true)
    (c62 : edge r62 (a 17) (a 25)=true)
    (c63 : edge r63 (a 17) (a 45)=true)
    (c72 : edge r72 (a 20) (a 48)=true)
    (c73 : edge r73 (a 21) (a 28)=true)
    (c74 : edge r74 (a 21) (a 49)=true)
    (c75 : edge r75 (a 22) (a 23)=true)
    (c78 : edge r78 (a 22) (a 50)=true)
    (c85 : edge r85 (a 25) (a 53)=true)
    (c87 : edge r87 (a 26) (a 54)=true)
    (c116 : edge r116 (a 37) (a 53)=true)
    (c138 : edge r138 (a 46) (a 48)=true)
    (c140 : edge r140 (a 47) (a 49)=true)
    (c141 : edge r141 (a 47) (a 55)=true)
    : a 16 ∈ [1] ∧ a 17 ∈ [1] ∧ a 25 ∈ [1] ∧ a 45 ∈ [1] ∧ a 48 ∈ [1] ∧ a 28 ∈ [1] ∧ a 49 ∈ [2] ∧ a 23 ∈ [1] ∧ a 50 ∈ [1] ∧ a 53 ∈ [1] ∧ a 54 ∈ [1] ∧ a 37 ∈ [1] ∧ a 46 ∈ [1] ∧ a 47 ∈ [1] ∧ a 55 ∈ [1] ∧ a 15 ∈ [1] := by
  have b0 : a 16 ≠ 0 := exclude [2] (edge r58) (a 16) (a 20) 0 d20 c58 (by decide +kernel)
  have t0 : a 16 ∈ [1] := remove (a 16) 0 [0,1] d16 b0
  have b1 : a 17 ≠ 0 := exclude [1] (edge r61) (a 17) (a 21) 0 d21 c61 (by decide +kernel)
  have t1 : a 17 ∈ [1] := remove (a 17) 0 [0,1] d17 b1
  have b2 : a 25 ≠ 0 := exclude [1] (fun u v => edge r62 v u) (a 25) (a 17) 0 t1 c62 (by decide +kernel)
  have t2 : a 25 ∈ [1] := remove (a 25) 0 [0,1] d25 b2
  have b3 : a 45 ≠ 0 := exclude [1] (fun u v => edge r63 v u) (a 45) (a 17) 0 t1 c63 (by decide +kernel)
  have t3 : a 45 ∈ [1] := remove (a 45) 0 [0,1] d45 b3
  have b4 : a 48 ≠ 0 := exclude [2] (fun u v => edge r72 v u) (a 48) (a 20) 0 d20 c72 (by decide +kernel)
  have t4 : a 48 ∈ [1] := remove (a 48) 0 [0,1] d48 b4
  have b5 : a 28 ≠ 0 := exclude [1] (fun u v => edge r73 v u) (a 28) (a 21) 0 d21 c73 (by decide +kernel)
  have t5 : a 28 ∈ [1] := remove (a 28) 0 [0,1] d28 b5
  have b6 : a 49 ≠ 0 := exclude [1] (fun u v => edge r74 v u) (a 49) (a 21) 0 d21 c74 (by decide +kernel)
  have t6 : a 49 ∈ [2] := remove (a 49) 0 [0,2] d49 b6
  have b7 : a 23 ≠ 0 := exclude [1] (fun u v => edge r75 v u) (a 23) (a 22) 0 d22 c75 (by decide +kernel)
  have t7 : a 23 ∈ [1] := remove (a 23) 0 [0,1] d23 b7
  have b8 : a 50 ≠ 0 := exclude [1] (fun u v => edge r78 v u) (a 50) (a 22) 0 d22 c78 (by decide +kernel)
  have t8 : a 50 ∈ [1] := remove (a 50) 0 [0,1] d50 b8
  have b9 : a 53 ≠ 0 := exclude [1] (fun u v => edge r85 v u) (a 53) (a 25) 0 t2 c85 (by decide +kernel)
  have t9 : a 53 ∈ [1] := remove (a 53) 0 [0,1] d53 b9
  have b10 : a 54 ≠ 0 := exclude [1] (fun u v => edge r87 v u) (a 54) (a 26) 0 d26 c87 (by decide +kernel)
  have t10 : a 54 ∈ [1] := remove (a 54) 0 [0,1] d54 b10
  have b11 : a 37 ≠ 0 := exclude [1] (edge r116) (a 37) (a 53) 0 t9 c116 (by decide +kernel)
  have t11 : a 37 ∈ [1] := remove (a 37) 0 [0,1] d37 b11
  have b12 : a 46 ≠ 0 := exclude [1] (edge r138) (a 46) (a 48) 0 t4 c138 (by decide +kernel)
  have t12 : a 46 ∈ [1] := remove (a 46) 0 [0,1] d46 b12
  have b13 : a 47 ≠ 0 := exclude [2] (edge r140) (a 47) (a 49) 0 t6 c140 (by decide +kernel)
  have t13 : a 47 ∈ [1] := remove (a 47) 0 [0,1] d47 b13
  have b14 : a 55 ≠ 0 := exclude [1] (fun u v => edge r141 v u) (a 55) (a 47) 0 t13 c141 (by decide +kernel)
  have t14 : a 55 ∈ [1] := remove (a 55) 0 [0,1] d55 b14
  have b15 : a 15 ≠ 0 := exclude [1] (fun u v => edge r48 v u) (a 15) (a 14) 0 d14 c48 (by decide +kernel)
  have t15 : a 15 ∈ [1] := remove (a 15) 0 [0,1] d15 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk7 (a : Nat → Nat)
    (d36 : a 36 ∈ [0,1])
    (d37 : a 37 ∈ [1])
    (d30 : a 30 ∈ [0,1])
    (d29 : a 29 ∈ [0,1])
    (d31 : a 31 ∈ [0,2])
    (c91 : edge r91 (a 29) (a 30)=true)
    (c92 : edge r92 (a 29) (a 31)=true)
    (c96 : edge r96 (a 30) (a 36)=true)
    (c112 : edge r112 (a 36) (a 37)=true)
    : a 36 ∈ [1] ∧ a 30 ∈ [1] ∧ a 29 ∈ [1] ∧ a 31 ∈ [2] := by
  have b0 : a 36 ≠ 0 := exclude [1] (edge r112) (a 36) (a 37) 0 d37 c112 (by decide +kernel)
  have t0 : a 36 ∈ [1] := remove (a 36) 0 [0,1] d36 b0
  have b1 : a 30 ≠ 0 := exclude [1] (edge r96) (a 30) (a 36) 0 t0 c96 (by decide +kernel)
  have t1 : a 30 ∈ [1] := remove (a 30) 0 [0,1] d30 b1
  have b2 : a 29 ≠ 0 := exclude [1] (edge r91) (a 29) (a 30) 0 t1 c91 (by decide +kernel)
  have t2 : a 29 ∈ [1] := remove (a 29) 0 [0,1] d29 b2
  have b3 : a 31 ≠ 0 := exclude [1] (fun u v => edge r92 v u) (a 31) (a 29) 0 t2 c92 (by decide +kernel)
  have t3 : a 31 ∈ [2] := remove (a 31) 0 [0,2] d31 b3
  exact And.intro t0 (And.intro t1 (And.intro t2 (t3)))
#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_225
