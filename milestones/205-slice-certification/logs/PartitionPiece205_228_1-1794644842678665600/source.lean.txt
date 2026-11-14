import PartitionData205_228
namespace PartitionCover205_228
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d14 : a 14 ∈ [0,1])
    (d15 : a 15 ∈ [0])
    (d29 : a 29 ∈ [0,1])
    (d30 : a 30 ∈ [0])
    (d49 : a 49 ∈ [0,1])
    (d45 : a 45 ∈ [0])
    (d47 : a 47 ∈ [0,1])
    (d46 : a 46 ∈ [0])
    (c48 : edge r48 (a 14) (a 15)=true)
    (c89 : edge r89 (a 29) (a 30)=true)
    (c129 : edge r129 (a 45) (a 49)=true)
    (c131 : edge r131 (a 46) (a 47)=true)
    : a 14 ∈ [0] ∧ a 29 ∈ [0] ∧ a 49 ∈ [0] ∧ a 47 ∈ [0] := by
  have b0 : a 14 ≠ 1 := exclude [0] (edge r48) (a 14) (a 15) 1 d15 c48 (by decide +kernel)
  have t0 : a 14 ∈ [0] := remove (a 14) 1 [0,1] d14 b0
  have b1 : a 29 ≠ 1 := exclude [0] (edge r89) (a 29) (a 30) 1 d30 c89 (by decide +kernel)
  have t1 : a 29 ∈ [0] := remove (a 29) 1 [0,1] d29 b1
  have b2 : a 49 ≠ 1 := exclude [0] (fun u v => edge r129 v u) (a 49) (a 45) 1 d45 c129 (by decide +kernel)
  have t2 : a 49 ∈ [0] := remove (a 49) 1 [0,1] d49 b2
  have b3 : a 47 ≠ 1 := exclude [0] (fun u v => edge r131 v u) (a 47) (a 46) 1 d46 c131 (by decide +kernel)
  have t3 : a 47 ∈ [0] := remove (a 47) 1 [0,1] d47 b3
  exact And.intro t0 (And.intro t1 (And.intro t2 (t3)))

theorem chunk5 (a : Nat → Nat)
    (d7 : a 7 ∈ [0,1])
    (d3 : a 3 ∈ [1])
    (d5 : a 5 ∈ [0,1])
    (d11 : a 11 ∈ [0,1])
    (d6 : a 6 ∈ [0,1])
    (d12 : a 12 ∈ [0,1])
    (d20 : a 20 ∈ [0,1])
    (d34 : a 34 ∈ [0,1])
    (d13 : a 13 ∈ [0,1])
    (d8 : a 8 ∈ [0,1])
    (d23 : a 23 ∈ [0,2])
    (d37 : a 37 ∈ [0,1])
    (d10 : a 10 ∈ [0,1])
    (d26 : a 26 ∈ [0,1])
    (d27 : a 27 ∈ [0,1])
    (d28 : a 28 ∈ [0,2])
    (d41 : a 41 ∈ [0,1])
    (c15 : edge r15 (a 3) (a 7)=true)
    (c22 : edge r22 (a 5) (a 7)=true)
    (c23 : edge r23 (a 5) (a 11)=true)
    (c26 : edge r26 (a 6) (a 7)=true)
    (c27 : edge r27 (a 6) (a 12)=true)
    (c28 : edge r28 (a 6) (a 20)=true)
    (c29 : edge r29 (a 6) (a 34)=true)
    (c30 : edge r30 (a 7) (a 13)=true)
    (c33 : edge r33 (a 8) (a 11)=true)
    (c34 : edge r34 (a 8) (a 23)=true)
    (c35 : edge r35 (a 8) (a 37)=true)
    (c39 : edge r39 (a 10) (a 11)=true)
    (c41 : edge r41 (a 10) (a 26)=true)
    (c45 : edge r45 (a 12) (a 27)=true)
    (c46 : edge r46 (a 13) (a 28)=true)
    (c47 : edge r47 (a 13) (a 41)=true)
    : a 7 ∈ [1] ∧ a 5 ∈ [1] ∧ a 11 ∈ [1] ∧ a 6 ∈ [1] ∧ a 12 ∈ [1] ∧ a 20 ∈ [1] ∧ a 34 ∈ [1] ∧ a 13 ∈ [1] ∧ a 8 ∈ [1] ∧ a 23 ∈ [2] ∧ a 37 ∈ [1] ∧ a 10 ∈ [1] ∧ a 26 ∈ [1] ∧ a 27 ∈ [1] ∧ a 28 ∈ [2] ∧ a 41 ∈ [1] := by
  have b0 : a 7 ≠ 0 := exclude [1] (fun u v => edge r15 v u) (a 7) (a 3) 0 d3 c15 (by decide +kernel)
  have t0 : a 7 ∈ [1] := remove (a 7) 0 [0,1] d7 b0
  have b1 : a 5 ≠ 0 := exclude [1] (edge r22) (a 5) (a 7) 0 t0 c22 (by decide +kernel)
  have t1 : a 5 ∈ [1] := remove (a 5) 0 [0,1] d5 b1
  have b2 : a 11 ≠ 0 := exclude [1] (fun u v => edge r23 v u) (a 11) (a 5) 0 t1 c23 (by decide +kernel)
  have t2 : a 11 ∈ [1] := remove (a 11) 0 [0,1] d11 b2
  have b3 : a 6 ≠ 0 := exclude [1] (edge r26) (a 6) (a 7) 0 t0 c26 (by decide +kernel)
  have t3 : a 6 ∈ [1] := remove (a 6) 0 [0,1] d6 b3
  have b4 : a 12 ≠ 0 := exclude [1] (fun u v => edge r27 v u) (a 12) (a 6) 0 t3 c27 (by decide +kernel)
  have t4 : a 12 ∈ [1] := remove (a 12) 0 [0,1] d12 b4
  have b5 : a 20 ≠ 0 := exclude [1] (fun u v => edge r28 v u) (a 20) (a 6) 0 t3 c28 (by decide +kernel)
  have t5 : a 20 ∈ [1] := remove (a 20) 0 [0,1] d20 b5
  have b6 : a 34 ≠ 0 := exclude [1] (fun u v => edge r29 v u) (a 34) (a 6) 0 t3 c29 (by decide +kernel)
  have t6 : a 34 ∈ [1] := remove (a 34) 0 [0,1] d34 b6
  have b7 : a 13 ≠ 0 := exclude [1] (fun u v => edge r30 v u) (a 13) (a 7) 0 t0 c30 (by decide +kernel)
  have t7 : a 13 ∈ [1] := remove (a 13) 0 [0,1] d13 b7
  have b8 : a 8 ≠ 0 := exclude [1] (edge r33) (a 8) (a 11) 0 t2 c33 (by decide +kernel)
  have t8 : a 8 ∈ [1] := remove (a 8) 0 [0,1] d8 b8
  have b9 : a 23 ≠ 0 := exclude [1] (fun u v => edge r34 v u) (a 23) (a 8) 0 t8 c34 (by decide +kernel)
  have t9 : a 23 ∈ [2] := remove (a 23) 0 [0,2] d23 b9
  have b10 : a 37 ≠ 0 := exclude [1] (fun u v => edge r35 v u) (a 37) (a 8) 0 t8 c35 (by decide +kernel)
  have t10 : a 37 ∈ [1] := remove (a 37) 0 [0,1] d37 b10
  have b11 : a 10 ≠ 0 := exclude [1] (edge r39) (a 10) (a 11) 0 t2 c39 (by decide +kernel)
  have t11 : a 10 ∈ [1] := remove (a 10) 0 [0,1] d10 b11
  have b12 : a 26 ≠ 0 := exclude [1] (fun u v => edge r41 v u) (a 26) (a 10) 0 t11 c41 (by decide +kernel)
  have t12 : a 26 ∈ [1] := remove (a 26) 0 [0,1] d26 b12
  have b13 : a 27 ≠ 0 := exclude [1] (fun u v => edge r45 v u) (a 27) (a 12) 0 t4 c45 (by decide +kernel)
  have t13 : a 27 ∈ [1] := remove (a 27) 0 [0,1] d27 b13
  have b14 : a 28 ≠ 0 := exclude [1] (fun u v => edge r46 v u) (a 28) (a 13) 0 t7 c46 (by decide +kernel)
  have t14 : a 28 ∈ [2] := remove (a 28) 0 [0,2] d28 b14
  have b15 : a 41 ≠ 0 := exclude [1] (fun u v => edge r47 v u) (a 41) (a 13) 0 t7 c47 (by decide +kernel)
  have t15 : a 41 ∈ [1] := remove (a 41) 0 [0,1] d41 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk6 (a : Nat → Nat)
    (d15 : a 15 ∈ [0,1])
    (d23 : a 23 ∈ [2])
    (d16 : a 16 ∈ [0,1])
    (d20 : a 20 ∈ [1])
    (d24 : a 24 ∈ [0,1])
    (d22 : a 22 ∈ [0,1])
    (d50 : a 50 ∈ [0,1])
    (d25 : a 25 ∈ [0,2])
    (d52 : a 52 ∈ [0,1])
    (d53 : a 53 ∈ [0,1])
    (d26 : a 26 ∈ [1])
    (d55 : a 55 ∈ [0,1])
    (d27 : a 27 ∈ [1])
    (d30 : a 30 ∈ [0,1])
    (d37 : a 37 ∈ [1])
    (d31 : a 31 ∈ [0,1])
    (d34 : a 34 ∈ [1])
    (d39 : a 39 ∈ [0,1])
    (d45 : a 45 ∈ [0,1])
    (d46 : a 46 ∈ [0,1])
    (d54 : a 54 ∈ [0,2])
    (d4 : a 4 ∈ [0,1])
    (d5 : a 5 ∈ [1])
    (c17 : edge r17 (a 4) (a 5)=true)
    (c55 : edge r55 (a 15) (a 23)=true)
    (c58 : edge r58 (a 16) (a 20)=true)
    (c59 : edge r59 (a 16) (a 24)=true)
    (c75 : edge r75 (a 22) (a 23)=true)
    (c78 : edge r78 (a 22) (a 50)=true)
    (c79 : edge r79 (a 23) (a 25)=true)
    (c84 : edge r84 (a 25) (a 52)=true)
    (c86 : edge r86 (a 26) (a 53)=true)
    (c88 : edge r88 (a 27) (a 55)=true)
    (c95 : edge r95 (a 30) (a 37)=true)
    (c97 : edge r97 (a 31) (a 34)=true)
    (c114 : edge r114 (a 37) (a 39)=true)
    (c130 : edge r130 (a 45) (a 52)=true)
    (c133 : edge r133 (a 46) (a 53)=true)
    (c142 : edge r142 (a 53) (a 54)=true)
    : a 15 ∈ [1] ∧ a 16 ∈ [1] ∧ a 24 ∈ [1] ∧ a 22 ∈ [1] ∧ a 50 ∈ [1] ∧ a 25 ∈ [2] ∧ a 52 ∈ [1] ∧ a 53 ∈ [1] ∧ a 55 ∈ [1] ∧ a 30 ∈ [1] ∧ a 31 ∈ [1] ∧ a 39 ∈ [1] ∧ a 45 ∈ [1] ∧ a 46 ∈ [1] ∧ a 54 ∈ [2] ∧ a 4 ∈ [1] := by
  have b0 : a 15 ≠ 0 := exclude [2] (edge r55) (a 15) (a 23) 0 d23 c55 (by decide +kernel)
  have t0 : a 15 ∈ [1] := remove (a 15) 0 [0,1] d15 b0
  have b1 : a 16 ≠ 0 := exclude [1] (edge r58) (a 16) (a 20) 0 d20 c58 (by decide +kernel)
  have t1 : a 16 ∈ [1] := remove (a 16) 0 [0,1] d16 b1
  have b2 : a 24 ≠ 0 := exclude [1] (fun u v => edge r59 v u) (a 24) (a 16) 0 t1 c59 (by decide +kernel)
  have t2 : a 24 ∈ [1] := remove (a 24) 0 [0,1] d24 b2
  have b3 : a 22 ≠ 0 := exclude [2] (edge r75) (a 22) (a 23) 0 d23 c75 (by decide +kernel)
  have t3 : a 22 ∈ [1] := remove (a 22) 0 [0,1] d22 b3
  have b4 : a 50 ≠ 0 := exclude [1] (fun u v => edge r78 v u) (a 50) (a 22) 0 t3 c78 (by decide +kernel)
  have t4 : a 50 ∈ [1] := remove (a 50) 0 [0,1] d50 b4
  have b5 : a 25 ≠ 0 := exclude [2] (fun u v => edge r79 v u) (a 25) (a 23) 0 d23 c79 (by decide +kernel)
  have t5 : a 25 ∈ [2] := remove (a 25) 0 [0,2] d25 b5
  have b6 : a 52 ≠ 0 := exclude [2] (fun u v => edge r84 v u) (a 52) (a 25) 0 t5 c84 (by decide +kernel)
  have t6 : a 52 ∈ [1] := remove (a 52) 0 [0,1] d52 b6
  have b7 : a 53 ≠ 0 := exclude [1] (fun u v => edge r86 v u) (a 53) (a 26) 0 d26 c86 (by decide +kernel)
  have t7 : a 53 ∈ [1] := remove (a 53) 0 [0,1] d53 b7
  have b8 : a 55 ≠ 0 := exclude [1] (fun u v => edge r88 v u) (a 55) (a 27) 0 d27 c88 (by decide +kernel)
  have t8 : a 55 ∈ [1] := remove (a 55) 0 [0,1] d55 b8
  have b9 : a 30 ≠ 0 := exclude [1] (edge r95) (a 30) (a 37) 0 d37 c95 (by decide +kernel)
  have t9 : a 30 ∈ [1] := remove (a 30) 0 [0,1] d30 b9
  have b10 : a 31 ≠ 0 := exclude [1] (edge r97) (a 31) (a 34) 0 d34 c97 (by decide +kernel)
  have t10 : a 31 ∈ [1] := remove (a 31) 0 [0,1] d31 b10
  have b11 : a 39 ≠ 0 := exclude [1] (fun u v => edge r114 v u) (a 39) (a 37) 0 d37 c114 (by decide +kernel)
  have t11 : a 39 ∈ [1] := remove (a 39) 0 [0,1] d39 b11
  have b12 : a 45 ≠ 0 := exclude [1] (edge r130) (a 45) (a 52) 0 t6 c130 (by decide +kernel)
  have t12 : a 45 ∈ [1] := remove (a 45) 0 [0,1] d45 b12
  have b13 : a 46 ≠ 0 := exclude [1] (edge r133) (a 46) (a 53) 0 t7 c133 (by decide +kernel)
  have t13 : a 46 ∈ [1] := remove (a 46) 0 [0,1] d46 b13
  have b14 : a 54 ≠ 0 := exclude [1] (fun u v => edge r142 v u) (a 54) (a 53) 0 t7 c142 (by decide +kernel)
  have t14 : a 54 ∈ [2] := remove (a 54) 0 [0,2] d54 b14
  have b15 : a 4 ≠ 0 := exclude [1] (edge r17) (a 4) (a 5) 0 d5 c17 (by decide +kernel)
  have t15 : a 4 ∈ [1] := remove (a 4) 0 [0,1] d4 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk7 (a : Nat → Nat)
    (d14 : a 14 ∈ [0,1])
    (d15 : a 15 ∈ [1])
    (d29 : a 29 ∈ [0,1])
    (d30 : a 30 ∈ [1])
    (d49 : a 49 ∈ [0,1])
    (d45 : a 45 ∈ [1])
    (d47 : a 47 ∈ [0,1])
    (d46 : a 46 ∈ [1])
    (c48 : edge r48 (a 14) (a 15)=true)
    (c89 : edge r89 (a 29) (a 30)=true)
    (c129 : edge r129 (a 45) (a 49)=true)
    (c131 : edge r131 (a 46) (a 47)=true)
    : a 14 ∈ [1] ∧ a 29 ∈ [1] ∧ a 49 ∈ [1] ∧ a 47 ∈ [1] := by
  have b0 : a 14 ≠ 0 := exclude [1] (edge r48) (a 14) (a 15) 0 d15 c48 (by decide +kernel)
  have t0 : a 14 ∈ [1] := remove (a 14) 0 [0,1] d14 b0
  have b1 : a 29 ≠ 0 := exclude [1] (edge r89) (a 29) (a 30) 0 d30 c89 (by decide +kernel)
  have t1 : a 29 ∈ [1] := remove (a 29) 0 [0,1] d29 b1
  have b2 : a 49 ≠ 0 := exclude [1] (fun u v => edge r129 v u) (a 49) (a 45) 0 d45 c129 (by decide +kernel)
  have t2 : a 49 ∈ [1] := remove (a 49) 0 [0,1] d49 b2
  have b3 : a 47 ≠ 0 := exclude [1] (fun u v => edge r131 v u) (a 47) (a 46) 0 d46 c131 (by decide +kernel)
  have t3 : a 47 ∈ [1] := remove (a 47) 0 [0,1] d47 b3
  exact And.intro t0 (And.intro t1 (And.intro t2 (t3)))
#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_228
