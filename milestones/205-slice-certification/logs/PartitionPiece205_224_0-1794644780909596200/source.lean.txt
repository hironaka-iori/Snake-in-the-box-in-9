import PartitionData205_224
namespace PartitionCover205_224
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d9 : a 9 ∈ [0,1])
    (d2 : a 2 ∈ [0])
    (d21 : a 21 ∈ [0,1,2,3])
    (d7 : a 7 ∈ [0,1])
    (d36 : a 36 ∈ [0,1])
    (d12 : a 12 ∈ [0,1,2,3])
    (d8 : a 8 ∈ [0])
    (d23 : a 23 ∈ [0,1,2,3])
    (d24 : a 24 ∈ [0,1,2,3])
    (d39 : a 39 ∈ [0,1])
    (d42 : a 42 ∈ [0,1])
    (d19 : a 19 ∈ [0,1])
    (d20 : a 20 ∈ [0,1,2,3])
    (d51 : a 51 ∈ [0,1,2,3])
    (c12 : edge r12 (a 2) (a 9)=true)
    (c32 : edge r32 (a 7) (a 21)=true)
    (c33 : edge r33 (a 7) (a 36)=true)
    (c35 : edge r35 (a 8) (a 12)=true)
    (c36 : edge r36 (a 8) (a 23)=true)
    (c40 : edge r40 (a 9) (a 24)=true)
    (c41 : edge r41 (a 9) (a 39)=true)
    (c48 : edge r48 (a 12) (a 42)=true)
    (c71 : edge r71 (a 19) (a 21)=true)
    (c73 : edge r73 (a 20) (a 21)=true)
    (c75 : edge r75 (a 20) (a 51)=true)
    : a 9 ∈ [0] ∧ a 21 ∈ [0,1] ∧ a 36 ∈ [0] ∧ a 12 ∈ [0,2] ∧ a 23 ∈ [0,2] ∧ a 24 ∈ [0,2] ∧ a 39 ∈ [0] ∧ a 42 ∈ [0] ∧ a 19 ∈ [0] ∧ a 20 ∈ [0,2] ∧ a 51 ∈ [0,2,3] := by
  have b0 : a 9 ≠ 1 := exclude [0] (fun u v => edge r12 v u) (a 9) (a 2) 1 d2 c12 (by decide +kernel)
  have t0 : a 9 ∈ [0] := remove (a 9) 1 [0,1] d9 b0
  have b1 : a 21 ≠ 2 := exclude [0,1] (fun u v => edge r32 v u) (a 21) (a 7) 2 d7 c32 (by decide +kernel)
  have t1 : a 21 ∈ [0,1,3] := remove (a 21) 2 [0,1,2,3] d21 b1
  have b2 : a 21 ≠ 3 := exclude [0,1] (fun u v => edge r32 v u) (a 21) (a 7) 3 d7 c32 (by decide +kernel)
  have t2 : a 21 ∈ [0,1] := remove (a 21) 3 [0,1,3] t1 b2
  have b3 : a 36 ≠ 1 := exclude [0,1] (fun u v => edge r33 v u) (a 36) (a 7) 1 d7 c33 (by decide +kernel)
  have t3 : a 36 ∈ [0] := remove (a 36) 1 [0,1] d36 b3
  have b4 : a 12 ≠ 1 := exclude [0] (fun u v => edge r35 v u) (a 12) (a 8) 1 d8 c35 (by decide +kernel)
  have t4 : a 12 ∈ [0,2,3] := remove (a 12) 1 [0,1,2,3] d12 b4
  have b5 : a 12 ≠ 3 := exclude [0] (fun u v => edge r35 v u) (a 12) (a 8) 3 d8 c35 (by decide +kernel)
  have t5 : a 12 ∈ [0,2] := remove (a 12) 3 [0,2,3] t4 b5
  have b6 : a 23 ≠ 1 := exclude [0] (fun u v => edge r36 v u) (a 23) (a 8) 1 d8 c36 (by decide +kernel)
  have t6 : a 23 ∈ [0,2,3] := remove (a 23) 1 [0,1,2,3] d23 b6
  have b7 : a 23 ≠ 3 := exclude [0] (fun u v => edge r36 v u) (a 23) (a 8) 3 d8 c36 (by decide +kernel)
  have t7 : a 23 ∈ [0,2] := remove (a 23) 3 [0,2,3] t6 b7
  have b8 : a 24 ≠ 1 := exclude [0] (fun u v => edge r40 v u) (a 24) (a 9) 1 t0 c40 (by decide +kernel)
  have t8 : a 24 ∈ [0,2,3] := remove (a 24) 1 [0,1,2,3] d24 b8
  have b9 : a 24 ≠ 3 := exclude [0] (fun u v => edge r40 v u) (a 24) (a 9) 3 t0 c40 (by decide +kernel)
  have t9 : a 24 ∈ [0,2] := remove (a 24) 3 [0,2,3] t8 b9
  have b10 : a 39 ≠ 1 := exclude [0] (fun u v => edge r41 v u) (a 39) (a 9) 1 t0 c41 (by decide +kernel)
  have t10 : a 39 ∈ [0] := remove (a 39) 1 [0,1] d39 b10
  have b11 : a 42 ≠ 1 := exclude [0,2] (fun u v => edge r48 v u) (a 42) (a 12) 1 t5 c48 (by decide +kernel)
  have t11 : a 42 ∈ [0] := remove (a 42) 1 [0,1] d42 b11
  have b12 : a 19 ≠ 1 := exclude [0,1] (edge r71) (a 19) (a 21) 1 t2 c71 (by decide +kernel)
  have t12 : a 19 ∈ [0] := remove (a 19) 1 [0,1] d19 b12
  have b13 : a 20 ≠ 1 := exclude [0,1] (edge r73) (a 20) (a 21) 1 t2 c73 (by decide +kernel)
  have t13 : a 20 ∈ [0,2,3] := remove (a 20) 1 [0,1,2,3] d20 b13
  have b14 : a 20 ≠ 3 := exclude [0,1] (edge r73) (a 20) (a 21) 3 t2 c73 (by decide +kernel)
  have t14 : a 20 ∈ [0,2] := remove (a 20) 3 [0,2,3] t13 b14
  have b15 : a 51 ≠ 1 := exclude [0,2] (fun u v => edge r75 v u) (a 51) (a 20) 1 t14 c75 (by decide +kernel)
  have t15 : a 51 ∈ [0,2,3] := remove (a 51) 1 [0,1,2,3] d51 b15
  exact And.intro t0 (And.intro t2 (And.intro t3 (And.intro t5 (And.intro t7 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t14 (t15))))))))))

theorem chunk1 (a : Nat → Nat)
    (d51 : a 51 ∈ [0,2,3])
    (d20 : a 20 ∈ [0,2])
    (d28 : a 28 ∈ [0,1,2,3])
    (d21 : a 21 ∈ [0,1])
    (d52 : a 52 ∈ [0,1,2,3])
    (d22 : a 22 ∈ [0,1,2,3])
    (d23 : a 23 ∈ [0,2])
    (d26 : a 26 ∈ [0,1])
    (d53 : a 53 ∈ [0,1])
    (d54 : a 54 ∈ [0,1,2,3])
    (d24 : a 24 ∈ [0,2])
    (d56 : a 56 ∈ [0,1,2,3])
    (d59 : a 59 ∈ [0,1])
    (d35 : a 35 ∈ [0,1,2,3])
    (d31 : a 31 ∈ [0,1])
    (c75 : edge r75 (a 20) (a 51)=true)
    (c76 : edge r76 (a 21) (a 28)=true)
    (c77 : edge r77 (a 21) (a 52)=true)
    (c78 : edge r78 (a 22) (a 23)=true)
    (c80 : edge r80 (a 22) (a 26)=true)
    (c82 : edge r82 (a 23) (a 53)=true)
    (c85 : edge r85 (a 24) (a 54)=true)
    (c89 : edge r89 (a 26) (a 56)=true)
    (c92 : edge r92 (a 28) (a 59)=true)
    (c103 : edge r103 (a 31) (a 35)=true)
    : a 51 ∈ [0,2] ∧ a 28 ∈ [0,1] ∧ a 52 ∈ [0,2] ∧ a 22 ∈ [0,2] ∧ a 26 ∈ [0] ∧ a 53 ∈ [0] ∧ a 54 ∈ [0,1] ∧ a 56 ∈ [0,1] ∧ a 59 ∈ [0] ∧ a 35 ∈ [0,1] := by
  have b0 : a 51 ≠ 3 := exclude [0,2] (fun u v => edge r75 v u) (a 51) (a 20) 3 d20 c75 (by decide +kernel)
  have t0 : a 51 ∈ [0,2] := remove (a 51) 3 [0,2,3] d51 b0
  have b1 : a 28 ≠ 2 := exclude [0,1] (fun u v => edge r76 v u) (a 28) (a 21) 2 d21 c76 (by decide +kernel)
  have t1 : a 28 ∈ [0,1,3] := remove (a 28) 2 [0,1,2,3] d28 b1
  have b2 : a 28 ≠ 3 := exclude [0,1] (fun u v => edge r76 v u) (a 28) (a 21) 3 d21 c76 (by decide +kernel)
  have t2 : a 28 ∈ [0,1] := remove (a 28) 3 [0,1,3] t1 b2
  have b3 : a 52 ≠ 1 := exclude [0,1] (fun u v => edge r77 v u) (a 52) (a 21) 1 d21 c77 (by decide +kernel)
  have t3 : a 52 ∈ [0,2,3] := remove (a 52) 1 [0,1,2,3] d52 b3
  have b4 : a 52 ≠ 3 := exclude [0,1] (fun u v => edge r77 v u) (a 52) (a 21) 3 d21 c77 (by decide +kernel)
  have t4 : a 52 ∈ [0,2] := remove (a 52) 3 [0,2,3] t3 b4
  have b5 : a 22 ≠ 1 := exclude [0,2] (edge r78) (a 22) (a 23) 1 d23 c78 (by decide +kernel)
  have t5 : a 22 ∈ [0,2,3] := remove (a 22) 1 [0,1,2,3] d22 b5
  have b6 : a 22 ≠ 3 := exclude [0,2] (edge r78) (a 22) (a 23) 3 d23 c78 (by decide +kernel)
  have t6 : a 22 ∈ [0,2] := remove (a 22) 3 [0,2,3] t5 b6
  have b7 : a 26 ≠ 1 := exclude [0,2] (fun u v => edge r80 v u) (a 26) (a 22) 1 t6 c80 (by decide +kernel)
  have t7 : a 26 ∈ [0] := remove (a 26) 1 [0,1] d26 b7
  have b8 : a 53 ≠ 1 := exclude [0,2] (fun u v => edge r82 v u) (a 53) (a 23) 1 d23 c82 (by decide +kernel)
  have t8 : a 53 ∈ [0] := remove (a 53) 1 [0,1] d53 b8
  have b9 : a 54 ≠ 2 := exclude [0,2] (fun u v => edge r85 v u) (a 54) (a 24) 2 d24 c85 (by decide +kernel)
  have t9 : a 54 ∈ [0,1,3] := remove (a 54) 2 [0,1,2,3] d54 b9
  have b10 : a 54 ≠ 3 := exclude [0,2] (fun u v => edge r85 v u) (a 54) (a 24) 3 d24 c85 (by decide +kernel)
  have t10 : a 54 ∈ [0,1] := remove (a 54) 3 [0,1,3] t9 b10
  have b11 : a 56 ≠ 2 := exclude [0] (fun u v => edge r89 v u) (a 56) (a 26) 2 t7 c89 (by decide +kernel)
  have t11 : a 56 ∈ [0,1,3] := remove (a 56) 2 [0,1,2,3] d56 b11
  have b12 : a 56 ≠ 3 := exclude [0] (fun u v => edge r89 v u) (a 56) (a 26) 3 t7 c89 (by decide +kernel)
  have t12 : a 56 ∈ [0,1] := remove (a 56) 3 [0,1,3] t11 b12
  have b13 : a 59 ≠ 1 := exclude [0,1] (fun u v => edge r92 v u) (a 59) (a 28) 1 t2 c92 (by decide +kernel)
  have t13 : a 59 ∈ [0] := remove (a 59) 1 [0,1] d59 b13
  have b14 : a 35 ≠ 2 := exclude [0,1] (fun u v => edge r103 v u) (a 35) (a 31) 2 d31 c103 (by decide +kernel)
  have t14 : a 35 ∈ [0,1,3] := remove (a 35) 2 [0,1,2,3] d35 b14
  have b15 : a 35 ≠ 3 := exclude [0,1] (fun u v => edge r103 v u) (a 35) (a 31) 3 d31 c103 (by decide +kernel)
  have t15 : a 35 ∈ [0,1] := remove (a 35) 3 [0,1,3] t14 b15
  exact And.intro t0 (And.intro t2 (And.intro t4 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t10 (And.intro t12 (And.intro t13 (t15)))))))))

theorem chunk2 (a : Nat → Nat)
    (d47 : a 47 ∈ [0,1,2,3])
    (d31 : a 31 ∈ [0,1])
    (d33 : a 33 ∈ [0,1])
    (d35 : a 35 ∈ [0,1])
    (d41 : a 41 ∈ [0,1,2,3])
    (d34 : a 34 ∈ [0,1])
    (d36 : a 36 ∈ [0])
    (d44 : a 44 ∈ [0,1,2,3])
    (d37 : a 37 ∈ [0,1,2,3])
    (d39 : a 39 ∈ [0])
    (d57 : a 57 ∈ [0,1,2,3])
    (d42 : a 42 ∈ [0])
    (d45 : a 45 ∈ [0,1])
    (d46 : a 46 ∈ [0,1])
    (d53 : a 53 ∈ [0])
    (d48 : a 48 ∈ [0,1,2,3])
    (c105 : edge r105 (a 31) (a 47)=true)
    (c110 : edge r110 (a 33) (a 35)=true)
    (c111 : edge r111 (a 33) (a 41)=true)
    (c113 : edge r113 (a 34) (a 36)=true)
    (c119 : edge r119 (a 36) (a 44)=true)
    (c122 : edge r122 (a 37) (a 39)=true)
    (c136 : edge r136 (a 42) (a 57)=true)
    (c141 : edge r141 (a 45) (a 47)=true)
    (c145 : edge r145 (a 46) (a 53)=true)
    (c146 : edge r146 (a 47) (a 48)=true)
    : a 47 ∈ [0,1] ∧ a 33 ∈ [0] ∧ a 41 ∈ [0,2] ∧ a 34 ∈ [0] ∧ a 44 ∈ [0,2] ∧ a 37 ∈ [0,2] ∧ a 57 ∈ [0,1] ∧ a 45 ∈ [0] ∧ a 46 ∈ [0] ∧ a 48 ∈ [0,2] := by
  have b0 : a 47 ≠ 2 := exclude [0,1] (fun u v => edge r105 v u) (a 47) (a 31) 2 d31 c105 (by decide +kernel)
  have t0 : a 47 ∈ [0,1,3] := remove (a 47) 2 [0,1,2,3] d47 b0
  have b1 : a 47 ≠ 3 := exclude [0,1] (fun u v => edge r105 v u) (a 47) (a 31) 3 d31 c105 (by decide +kernel)
  have t1 : a 47 ∈ [0,1] := remove (a 47) 3 [0,1,3] t0 b1
  have b2 : a 33 ≠ 1 := exclude [0,1] (edge r110) (a 33) (a 35) 1 d35 c110 (by decide +kernel)
  have t2 : a 33 ∈ [0] := remove (a 33) 1 [0,1] d33 b2
  have b3 : a 41 ≠ 1 := exclude [0] (fun u v => edge r111 v u) (a 41) (a 33) 1 t2 c111 (by decide +kernel)
  have t3 : a 41 ∈ [0,2,3] := remove (a 41) 1 [0,1,2,3] d41 b3
  have b4 : a 41 ≠ 3 := exclude [0] (fun u v => edge r111 v u) (a 41) (a 33) 3 t2 c111 (by decide +kernel)
  have t4 : a 41 ∈ [0,2] := remove (a 41) 3 [0,2,3] t3 b4
  have b5 : a 34 ≠ 1 := exclude [0] (edge r113) (a 34) (a 36) 1 d36 c113 (by decide +kernel)
  have t5 : a 34 ∈ [0] := remove (a 34) 1 [0,1] d34 b5
  have b6 : a 44 ≠ 1 := exclude [0] (fun u v => edge r119 v u) (a 44) (a 36) 1 d36 c119 (by decide +kernel)
  have t6 : a 44 ∈ [0,2,3] := remove (a 44) 1 [0,1,2,3] d44 b6
  have b7 : a 44 ≠ 3 := exclude [0] (fun u v => edge r119 v u) (a 44) (a 36) 3 d36 c119 (by decide +kernel)
  have t7 : a 44 ∈ [0,2] := remove (a 44) 3 [0,2,3] t6 b7
  have b8 : a 37 ≠ 1 := exclude [0] (edge r122) (a 37) (a 39) 1 d39 c122 (by decide +kernel)
  have t8 : a 37 ∈ [0,2,3] := remove (a 37) 1 [0,1,2,3] d37 b8
  have b9 : a 37 ≠ 3 := exclude [0] (edge r122) (a 37) (a 39) 3 d39 c122 (by decide +kernel)
  have t9 : a 37 ∈ [0,2] := remove (a 37) 3 [0,2,3] t8 b9
  have b10 : a 57 ≠ 2 := exclude [0] (fun u v => edge r136 v u) (a 57) (a 42) 2 d42 c136 (by decide +kernel)
  have t10 : a 57 ∈ [0,1,3] := remove (a 57) 2 [0,1,2,3] d57 b10
  have b11 : a 57 ≠ 3 := exclude [0] (fun u v => edge r136 v u) (a 57) (a 42) 3 d42 c136 (by decide +kernel)
  have t11 : a 57 ∈ [0,1] := remove (a 57) 3 [0,1,3] t10 b11
  have b12 : a 45 ≠ 1 := exclude [0,1] (edge r141) (a 45) (a 47) 1 t1 c141 (by decide +kernel)
  have t12 : a 45 ∈ [0] := remove (a 45) 1 [0,1] d45 b12
  have b13 : a 46 ≠ 1 := exclude [0] (edge r145) (a 46) (a 53) 1 d53 c145 (by decide +kernel)
  have t13 : a 46 ∈ [0] := remove (a 46) 1 [0,1] d46 b13
  have b14 : a 48 ≠ 1 := exclude [0,1] (fun u v => edge r146 v u) (a 48) (a 47) 1 t1 c146 (by decide +kernel)
  have t14 : a 48 ∈ [0,2,3] := remove (a 48) 1 [0,1,2,3] d48 b14
  have b15 : a 48 ≠ 3 := exclude [0,1] (fun u v => edge r146 v u) (a 48) (a 47) 3 t1 c146 (by decide +kernel)
  have t15 : a 48 ∈ [0,2] := remove (a 48) 3 [0,2,3] t14 b15
  exact And.intro t1 (And.intro t2 (And.intro t4 (And.intro t5 (And.intro t7 (And.intro t9 (And.intro t11 (And.intro t12 (And.intro t13 (t15)))))))))

theorem chunk3 (a : Nat → Nat)
    (d58 : a 58 ∈ [0,1])
    (d51 : a 51 ∈ [0,2])
    (d18 : a 18 ∈ [0,1])
    (d19 : a 19 ∈ [0])
    (c67 : edge r67 (a 18) (a 19)=true)
    (c157 : edge r157 (a 51) (a 58)=true)
    : a 58 ∈ [0] ∧ a 18 ∈ [0] := by
  have b0 : a 58 ≠ 1 := exclude [0,2] (fun u v => edge r157 v u) (a 58) (a 51) 1 d51 c157 (by decide +kernel)
  have t0 : a 58 ∈ [0] := remove (a 58) 1 [0,1] d58 b0
  have b1 : a 18 ≠ 1 := exclude [0] (edge r67) (a 18) (a 19) 1 d19 c67 (by decide +kernel)
  have t1 : a 18 ∈ [0] := remove (a 18) 1 [0,1] d18 b1
  exact And.intro t0 (t1)

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_224
