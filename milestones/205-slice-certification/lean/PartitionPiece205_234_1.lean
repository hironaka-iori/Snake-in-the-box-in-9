import PartitionData205_234
namespace PartitionCover205_234
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,1])
    (d1 : a 1 ∈ [0])
    (d5 : a 5 ∈ [0,1])
    (d15 : a 15 ∈ [0,1])
    (d30 : a 30 ∈ [0,1])
    (d2 : a 2 ∈ [0,2])
    (d16 : a 16 ∈ [0,2])
    (d31 : a 31 ∈ [0,1])
    (d7 : a 7 ∈ [0,2])
    (d9 : a 9 ∈ [0,2])
    (d4 : a 4 ∈ [0,1])
    (d10 : a 10 ∈ [0,1])
    (d33 : a 33 ∈ [0,2])
    (d19 : a 19 ∈ [0,1])
    (d21 : a 21 ∈ [0,2])
    (d36 : a 36 ∈ [0,2])
    (d8 : a 8 ∈ [0,2])
    (c6 : edge r6 (a 1) (a 3)=true)
    (c7 : edge r7 (a 1) (a 5)=true)
    (c8 : edge r8 (a 1) (a 15)=true)
    (c9 : edge r9 (a 1) (a 30)=true)
    (c10 : edge r10 (a 2) (a 3)=true)
    (c12 : edge r12 (a 2) (a 16)=true)
    (c13 : edge r13 (a 2) (a 31)=true)
    (c14 : edge r14 (a 3) (a 7)=true)
    (c15 : edge r15 (a 3) (a 9)=true)
    (c18 : edge r18 (a 4) (a 5)=true)
    (c20 : edge r20 (a 4) (a 10)=true)
    (c22 : edge r22 (a 4) (a 33)=true)
    (c25 : edge r25 (a 5) (a 19)=true)
    (c32 : edge r32 (a 7) (a 21)=true)
    (c33 : edge r33 (a 7) (a 36)=true)
    (c34 : edge r34 (a 8) (a 10)=true)
    : a 3 ∈ [0] ∧ a 5 ∈ [0] ∧ a 15 ∈ [0] ∧ a 30 ∈ [0] ∧ a 2 ∈ [0] ∧ a 16 ∈ [0] ∧ a 31 ∈ [0] ∧ a 7 ∈ [0] ∧ a 9 ∈ [0] ∧ a 4 ∈ [0] ∧ a 10 ∈ [0] ∧ a 33 ∈ [0] ∧ a 19 ∈ [0] ∧ a 21 ∈ [0] ∧ a 36 ∈ [0] ∧ a 8 ∈ [0] := by
  have b0 : a 3 ≠ 1 := exclude [0] (fun u v => edge r6 v u) (a 3) (a 1) 1 d1 c6 (by decide +kernel)
  have t0 : a 3 ∈ [0] := remove (a 3) 1 [0,1] d3 b0
  have b1 : a 5 ≠ 1 := exclude [0] (fun u v => edge r7 v u) (a 5) (a 1) 1 d1 c7 (by decide +kernel)
  have t1 : a 5 ∈ [0] := remove (a 5) 1 [0,1] d5 b1
  have b2 : a 15 ≠ 1 := exclude [0] (fun u v => edge r8 v u) (a 15) (a 1) 1 d1 c8 (by decide +kernel)
  have t2 : a 15 ∈ [0] := remove (a 15) 1 [0,1] d15 b2
  have b3 : a 30 ≠ 1 := exclude [0] (fun u v => edge r9 v u) (a 30) (a 1) 1 d1 c9 (by decide +kernel)
  have t3 : a 30 ∈ [0] := remove (a 30) 1 [0,1] d30 b3
  have b4 : a 2 ≠ 2 := exclude [0] (edge r10) (a 2) (a 3) 2 t0 c10 (by decide +kernel)
  have t4 : a 2 ∈ [0] := remove (a 2) 2 [0,2] d2 b4
  have b5 : a 16 ≠ 2 := exclude [0] (fun u v => edge r12 v u) (a 16) (a 2) 2 t4 c12 (by decide +kernel)
  have t5 : a 16 ∈ [0] := remove (a 16) 2 [0,2] d16 b5
  have b6 : a 31 ≠ 1 := exclude [0] (fun u v => edge r13 v u) (a 31) (a 2) 1 t4 c13 (by decide +kernel)
  have t6 : a 31 ∈ [0] := remove (a 31) 1 [0,1] d31 b6
  have b7 : a 7 ≠ 2 := exclude [0] (fun u v => edge r14 v u) (a 7) (a 3) 2 t0 c14 (by decide +kernel)
  have t7 : a 7 ∈ [0] := remove (a 7) 2 [0,2] d7 b7
  have b8 : a 9 ≠ 2 := exclude [0] (fun u v => edge r15 v u) (a 9) (a 3) 2 t0 c15 (by decide +kernel)
  have t8 : a 9 ∈ [0] := remove (a 9) 2 [0,2] d9 b8
  have b9 : a 4 ≠ 1 := exclude [0] (edge r18) (a 4) (a 5) 1 t1 c18 (by decide +kernel)
  have t9 : a 4 ∈ [0] := remove (a 4) 1 [0,1] d4 b9
  have b10 : a 10 ≠ 1 := exclude [0] (fun u v => edge r20 v u) (a 10) (a 4) 1 t9 c20 (by decide +kernel)
  have t10 : a 10 ∈ [0] := remove (a 10) 1 [0,1] d10 b10
  have b11 : a 33 ≠ 2 := exclude [0] (fun u v => edge r22 v u) (a 33) (a 4) 2 t9 c22 (by decide +kernel)
  have t11 : a 33 ∈ [0] := remove (a 33) 2 [0,2] d33 b11
  have b12 : a 19 ≠ 1 := exclude [0] (fun u v => edge r25 v u) (a 19) (a 5) 1 t1 c25 (by decide +kernel)
  have t12 : a 19 ∈ [0] := remove (a 19) 1 [0,1] d19 b12
  have b13 : a 21 ≠ 2 := exclude [0] (fun u v => edge r32 v u) (a 21) (a 7) 2 t7 c32 (by decide +kernel)
  have t13 : a 21 ∈ [0] := remove (a 21) 2 [0,2] d21 b13
  have b14 : a 36 ≠ 2 := exclude [0] (fun u v => edge r33 v u) (a 36) (a 7) 2 t7 c33 (by decide +kernel)
  have t14 : a 36 ∈ [0] := remove (a 36) 2 [0,2] d36 b14
  have b15 : a 8 ≠ 2 := exclude [0] (edge r34) (a 8) (a 10) 2 t10 c34 (by decide +kernel)
  have t15 : a 8 ∈ [0] := remove (a 8) 2 [0,2] d8 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk5 (a : Nat → Nat)
    (d22 : a 22 ∈ [0,1])
    (d8 : a 8 ∈ [0])
    (d25 : a 25 ∈ [0,1])
    (d9 : a 9 ∈ [0])
    (d12 : a 12 ∈ [0,1])
    (d10 : a 10 ∈ [0])
    (d28 : a 28 ∈ [0,1])
    (d41 : a 41 ∈ [0,1])
    (d14 : a 14 ∈ [0,2])
    (d15 : a 15 ∈ [0])
    (d43 : a 43 ∈ [0,2])
    (d23 : a 23 ∈ [0,1])
    (d20 : a 20 ∈ [0,1])
    (d16 : a 16 ∈ [0])
    (d24 : a 24 ∈ [0,2])
    (d45 : a 45 ∈ [0,1])
    (d27 : a 27 ∈ [0,1])
    (d19 : a 19 ∈ [0])
    (d47 : a 47 ∈ [0,1])
    (d49 : a 49 ∈ [0,1])
    (d21 : a 21 ∈ [0])
    (d50 : a 50 ∈ [0,1])
    (d52 : a 52 ∈ [0,1])
    (c35 : edge r35 (a 8) (a 22)=true)
    (c37 : edge r37 (a 9) (a 25)=true)
    (c40 : edge r40 (a 10) (a 12)=true)
    (c46 : edge r46 (a 12) (a 28)=true)
    (c47 : edge r47 (a 12) (a 41)=true)
    (c49 : edge r49 (a 14) (a 15)=true)
    (c53 : edge r53 (a 14) (a 43)=true)
    (c56 : edge r56 (a 15) (a 23)=true)
    (c59 : edge r59 (a 16) (a 20)=true)
    (c60 : edge r60 (a 16) (a 24)=true)
    (c61 : edge r61 (a 16) (a 45)=true)
    (c69 : edge r69 (a 19) (a 27)=true)
    (c70 : edge r70 (a 19) (a 47)=true)
    (c74 : edge r74 (a 21) (a 49)=true)
    (c78 : edge r78 (a 22) (a 50)=true)
    (c84 : edge r84 (a 25) (a 52)=true)
    : a 22 ∈ [0] ∧ a 25 ∈ [0] ∧ a 12 ∈ [0] ∧ a 28 ∈ [0] ∧ a 41 ∈ [0] ∧ a 14 ∈ [0] ∧ a 43 ∈ [0] ∧ a 23 ∈ [0] ∧ a 20 ∈ [0] ∧ a 24 ∈ [0] ∧ a 45 ∈ [0] ∧ a 27 ∈ [0] ∧ a 47 ∈ [0] ∧ a 49 ∈ [0] ∧ a 50 ∈ [0] ∧ a 52 ∈ [0] := by
  have b0 : a 22 ≠ 1 := exclude [0] (fun u v => edge r35 v u) (a 22) (a 8) 1 d8 c35 (by decide +kernel)
  have t0 : a 22 ∈ [0] := remove (a 22) 1 [0,1] d22 b0
  have b1 : a 25 ≠ 1 := exclude [0] (fun u v => edge r37 v u) (a 25) (a 9) 1 d9 c37 (by decide +kernel)
  have t1 : a 25 ∈ [0] := remove (a 25) 1 [0,1] d25 b1
  have b2 : a 12 ≠ 1 := exclude [0] (fun u v => edge r40 v u) (a 12) (a 10) 1 d10 c40 (by decide +kernel)
  have t2 : a 12 ∈ [0] := remove (a 12) 1 [0,1] d12 b2
  have b3 : a 28 ≠ 1 := exclude [0] (fun u v => edge r46 v u) (a 28) (a 12) 1 t2 c46 (by decide +kernel)
  have t3 : a 28 ∈ [0] := remove (a 28) 1 [0,1] d28 b3
  have b4 : a 41 ≠ 1 := exclude [0] (fun u v => edge r47 v u) (a 41) (a 12) 1 t2 c47 (by decide +kernel)
  have t4 : a 41 ∈ [0] := remove (a 41) 1 [0,1] d41 b4
  have b5 : a 14 ≠ 2 := exclude [0] (edge r49) (a 14) (a 15) 2 d15 c49 (by decide +kernel)
  have t5 : a 14 ∈ [0] := remove (a 14) 2 [0,2] d14 b5
  have b6 : a 43 ≠ 2 := exclude [0] (fun u v => edge r53 v u) (a 43) (a 14) 2 t5 c53 (by decide +kernel)
  have t6 : a 43 ∈ [0] := remove (a 43) 2 [0,2] d43 b6
  have b7 : a 23 ≠ 1 := exclude [0] (fun u v => edge r56 v u) (a 23) (a 15) 1 d15 c56 (by decide +kernel)
  have t7 : a 23 ∈ [0] := remove (a 23) 1 [0,1] d23 b7
  have b8 : a 20 ≠ 1 := exclude [0] (fun u v => edge r59 v u) (a 20) (a 16) 1 d16 c59 (by decide +kernel)
  have t8 : a 20 ∈ [0] := remove (a 20) 1 [0,1] d20 b8
  have b9 : a 24 ≠ 2 := exclude [0] (fun u v => edge r60 v u) (a 24) (a 16) 2 d16 c60 (by decide +kernel)
  have t9 : a 24 ∈ [0] := remove (a 24) 2 [0,2] d24 b9
  have b10 : a 45 ≠ 1 := exclude [0] (fun u v => edge r61 v u) (a 45) (a 16) 1 d16 c61 (by decide +kernel)
  have t10 : a 45 ∈ [0] := remove (a 45) 1 [0,1] d45 b10
  have b11 : a 27 ≠ 1 := exclude [0] (fun u v => edge r69 v u) (a 27) (a 19) 1 d19 c69 (by decide +kernel)
  have t11 : a 27 ∈ [0] := remove (a 27) 1 [0,1] d27 b11
  have b12 : a 47 ≠ 1 := exclude [0] (fun u v => edge r70 v u) (a 47) (a 19) 1 d19 c70 (by decide +kernel)
  have t12 : a 47 ∈ [0] := remove (a 47) 1 [0,1] d47 b12
  have b13 : a 49 ≠ 1 := exclude [0] (fun u v => edge r74 v u) (a 49) (a 21) 1 d21 c74 (by decide +kernel)
  have t13 : a 49 ∈ [0] := remove (a 49) 1 [0,1] d49 b13
  have b14 : a 50 ≠ 1 := exclude [0] (fun u v => edge r78 v u) (a 50) (a 22) 1 t0 c78 (by decide +kernel)
  have t14 : a 50 ∈ [0] := remove (a 50) 1 [0,1] d50 b14
  have b15 : a 52 ≠ 1 := exclude [0] (fun u v => edge r84 v u) (a 52) (a 25) 1 t1 c84 (by decide +kernel)
  have t15 : a 52 ∈ [0] := remove (a 52) 1 [0,1] d52 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk6 (a : Nat → Nat)
    (d54 : a 54 ∈ [0,1])
    (d27 : a 27 ∈ [0])
    (d29 : a 29 ∈ [0,2])
    (d30 : a 30 ∈ [0])
    (d37 : a 37 ∈ [0,1])
    (d35 : a 35 ∈ [0,1])
    (d31 : a 31 ∈ [0])
    (d38 : a 38 ∈ [0,1])
    (d40 : a 40 ∈ [0,2])
    (d46 : a 46 ∈ [0,1])
    (d45 : a 45 ∈ [0])
    (d56 : a 56 ∈ [0,1])
    (d49 : a 49 ∈ [0])
    (c88 : edge r88 (a 27) (a 54)=true)
    (c90 : edge r90 (a 29) (a 30)=true)
    (c96 : edge r96 (a 30) (a 37)=true)
    (c99 : edge r99 (a 31) (a 35)=true)
    (c100 : edge r100 (a 31) (a 38)=true)
    (c116 : edge r116 (a 37) (a 40)=true)
    (c133 : edge r133 (a 45) (a 46)=true)
    (c141 : edge r141 (a 49) (a 56)=true)
    : a 54 ∈ [0] ∧ a 29 ∈ [0] ∧ a 37 ∈ [0] ∧ a 35 ∈ [0] ∧ a 38 ∈ [0] ∧ a 40 ∈ [0] ∧ a 46 ∈ [0] ∧ a 56 ∈ [0] := by
  have b0 : a 54 ≠ 1 := exclude [0] (fun u v => edge r88 v u) (a 54) (a 27) 1 d27 c88 (by decide +kernel)
  have t0 : a 54 ∈ [0] := remove (a 54) 1 [0,1] d54 b0
  have b1 : a 29 ≠ 2 := exclude [0] (edge r90) (a 29) (a 30) 2 d30 c90 (by decide +kernel)
  have t1 : a 29 ∈ [0] := remove (a 29) 2 [0,2] d29 b1
  have b2 : a 37 ≠ 1 := exclude [0] (fun u v => edge r96 v u) (a 37) (a 30) 1 d30 c96 (by decide +kernel)
  have t2 : a 37 ∈ [0] := remove (a 37) 1 [0,1] d37 b2
  have b3 : a 35 ≠ 1 := exclude [0] (fun u v => edge r99 v u) (a 35) (a 31) 1 d31 c99 (by decide +kernel)
  have t3 : a 35 ∈ [0] := remove (a 35) 1 [0,1] d35 b3
  have b4 : a 38 ≠ 1 := exclude [0] (fun u v => edge r100 v u) (a 38) (a 31) 1 d31 c100 (by decide +kernel)
  have t4 : a 38 ∈ [0] := remove (a 38) 1 [0,1] d38 b4
  have b5 : a 40 ≠ 2 := exclude [0] (fun u v => edge r116 v u) (a 40) (a 37) 2 t2 c116 (by decide +kernel)
  have t5 : a 40 ∈ [0] := remove (a 40) 2 [0,2] d40 b5
  have b6 : a 46 ≠ 1 := exclude [0] (fun u v => edge r133 v u) (a 46) (a 45) 1 d45 c133 (by decide +kernel)
  have t6 : a 46 ∈ [0] := remove (a 46) 1 [0,1] d46 b6
  have b7 : a 56 ≠ 1 := exclude [0] (fun u v => edge r141 v u) (a 56) (a 49) 1 d49 c141 (by decide +kernel)
  have t7 : a 56 ∈ [0] := remove (a 56) 1 [0,1] d56 b7
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (t7)))))))

theorem chunk7 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,1])
    (d1 : a 1 ∈ [1])
    (d5 : a 5 ∈ [0,1])
    (d15 : a 15 ∈ [0,1])
    (d30 : a 30 ∈ [0,1])
    (d2 : a 2 ∈ [0,2])
    (d16 : a 16 ∈ [0,2])
    (d31 : a 31 ∈ [0,1])
    (d7 : a 7 ∈ [0,2])
    (d9 : a 9 ∈ [0,2])
    (d4 : a 4 ∈ [0,1])
    (d10 : a 10 ∈ [0,1])
    (d33 : a 33 ∈ [0,2])
    (d19 : a 19 ∈ [0,1])
    (d21 : a 21 ∈ [0,2])
    (d36 : a 36 ∈ [0,2])
    (d8 : a 8 ∈ [0,2])
    (c6 : edge r6 (a 1) (a 3)=true)
    (c7 : edge r7 (a 1) (a 5)=true)
    (c8 : edge r8 (a 1) (a 15)=true)
    (c9 : edge r9 (a 1) (a 30)=true)
    (c10 : edge r10 (a 2) (a 3)=true)
    (c12 : edge r12 (a 2) (a 16)=true)
    (c13 : edge r13 (a 2) (a 31)=true)
    (c14 : edge r14 (a 3) (a 7)=true)
    (c15 : edge r15 (a 3) (a 9)=true)
    (c18 : edge r18 (a 4) (a 5)=true)
    (c20 : edge r20 (a 4) (a 10)=true)
    (c22 : edge r22 (a 4) (a 33)=true)
    (c25 : edge r25 (a 5) (a 19)=true)
    (c32 : edge r32 (a 7) (a 21)=true)
    (c33 : edge r33 (a 7) (a 36)=true)
    (c34 : edge r34 (a 8) (a 10)=true)
    : a 3 ∈ [1] ∧ a 5 ∈ [1] ∧ a 15 ∈ [1] ∧ a 30 ∈ [1] ∧ a 2 ∈ [2] ∧ a 16 ∈ [2] ∧ a 31 ∈ [1] ∧ a 7 ∈ [2] ∧ a 9 ∈ [2] ∧ a 4 ∈ [1] ∧ a 10 ∈ [1] ∧ a 33 ∈ [2] ∧ a 19 ∈ [1] ∧ a 21 ∈ [2] ∧ a 36 ∈ [2] ∧ a 8 ∈ [2] := by
  have b0 : a 3 ≠ 0 := exclude [1] (fun u v => edge r6 v u) (a 3) (a 1) 0 d1 c6 (by decide +kernel)
  have t0 : a 3 ∈ [1] := remove (a 3) 0 [0,1] d3 b0
  have b1 : a 5 ≠ 0 := exclude [1] (fun u v => edge r7 v u) (a 5) (a 1) 0 d1 c7 (by decide +kernel)
  have t1 : a 5 ∈ [1] := remove (a 5) 0 [0,1] d5 b1
  have b2 : a 15 ≠ 0 := exclude [1] (fun u v => edge r8 v u) (a 15) (a 1) 0 d1 c8 (by decide +kernel)
  have t2 : a 15 ∈ [1] := remove (a 15) 0 [0,1] d15 b2
  have b3 : a 30 ≠ 0 := exclude [1] (fun u v => edge r9 v u) (a 30) (a 1) 0 d1 c9 (by decide +kernel)
  have t3 : a 30 ∈ [1] := remove (a 30) 0 [0,1] d30 b3
  have b4 : a 2 ≠ 0 := exclude [1] (edge r10) (a 2) (a 3) 0 t0 c10 (by decide +kernel)
  have t4 : a 2 ∈ [2] := remove (a 2) 0 [0,2] d2 b4
  have b5 : a 16 ≠ 0 := exclude [2] (fun u v => edge r12 v u) (a 16) (a 2) 0 t4 c12 (by decide +kernel)
  have t5 : a 16 ∈ [2] := remove (a 16) 0 [0,2] d16 b5
  have b6 : a 31 ≠ 0 := exclude [2] (fun u v => edge r13 v u) (a 31) (a 2) 0 t4 c13 (by decide +kernel)
  have t6 : a 31 ∈ [1] := remove (a 31) 0 [0,1] d31 b6
  have b7 : a 7 ≠ 0 := exclude [1] (fun u v => edge r14 v u) (a 7) (a 3) 0 t0 c14 (by decide +kernel)
  have t7 : a 7 ∈ [2] := remove (a 7) 0 [0,2] d7 b7
  have b8 : a 9 ≠ 0 := exclude [1] (fun u v => edge r15 v u) (a 9) (a 3) 0 t0 c15 (by decide +kernel)
  have t8 : a 9 ∈ [2] := remove (a 9) 0 [0,2] d9 b8
  have b9 : a 4 ≠ 0 := exclude [1] (edge r18) (a 4) (a 5) 0 t1 c18 (by decide +kernel)
  have t9 : a 4 ∈ [1] := remove (a 4) 0 [0,1] d4 b9
  have b10 : a 10 ≠ 0 := exclude [1] (fun u v => edge r20 v u) (a 10) (a 4) 0 t9 c20 (by decide +kernel)
  have t10 : a 10 ∈ [1] := remove (a 10) 0 [0,1] d10 b10
  have b11 : a 33 ≠ 0 := exclude [1] (fun u v => edge r22 v u) (a 33) (a 4) 0 t9 c22 (by decide +kernel)
  have t11 : a 33 ∈ [2] := remove (a 33) 0 [0,2] d33 b11
  have b12 : a 19 ≠ 0 := exclude [1] (fun u v => edge r25 v u) (a 19) (a 5) 0 t1 c25 (by decide +kernel)
  have t12 : a 19 ∈ [1] := remove (a 19) 0 [0,1] d19 b12
  have b13 : a 21 ≠ 0 := exclude [2] (fun u v => edge r32 v u) (a 21) (a 7) 0 t7 c32 (by decide +kernel)
  have t13 : a 21 ∈ [2] := remove (a 21) 0 [0,2] d21 b13
  have b14 : a 36 ≠ 0 := exclude [2] (fun u v => edge r33 v u) (a 36) (a 7) 0 t7 c33 (by decide +kernel)
  have t14 : a 36 ∈ [2] := remove (a 36) 0 [0,2] d36 b14
  have b15 : a 8 ≠ 0 := exclude [1] (edge r34) (a 8) (a 10) 0 t10 c34 (by decide +kernel)
  have t15 : a 8 ∈ [2] := remove (a 8) 0 [0,2] d8 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_234
