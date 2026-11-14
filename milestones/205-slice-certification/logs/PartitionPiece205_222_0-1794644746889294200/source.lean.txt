import PartitionData205_222
namespace PartitionCover205_222
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d5 : a 5 ∈ [0,1,2,3])
    (d1 : a 1 ∈ [0])
    (d16 : a 16 ∈ [0,1,2,3])
    (d30 : a 30 ∈ [0,1,2,3])
    (d32 : a 32 ∈ [0,1])
    (d3 : a 3 ∈ [0])
    (d34 : a 34 ∈ [0,1,2,3])
    (d20 : a 20 ∈ [0,1,2,3])
    (d7 : a 7 ∈ [0])
    (d21 : a 21 ∈ [0,1,2,3])
    (d8 : a 8 ∈ [0,1])
    (d36 : a 36 ∈ [0,1])
    (d24 : a 24 ∈ [0,1,2,3])
    (d10 : a 10 ∈ [0,1])
    (c7 : edge r7 (a 1) (a 5)=true)
    (c9 : edge r9 (a 1) (a 16)=true)
    (c10 : edge r10 (a 1) (a 30)=true)
    (c17 : edge r17 (a 3) (a 32)=true)
    (c25 : edge r25 (a 5) (a 34)=true)
    (c31 : edge r31 (a 7) (a 20)=true)
    (c34 : edge r34 (a 8) (a 21)=true)
    (c35 : edge r35 (a 8) (a 36)=true)
    (c41 : edge r41 (a 10) (a 24)=true)
    : a 5 ∈ [0,2] ∧ a 16 ∈ [0,2] ∧ a 30 ∈ [0,1] ∧ a 32 ∈ [0] ∧ a 34 ∈ [0,2] ∧ a 20 ∈ [0,2] ∧ a 21 ∈ [0,2] ∧ a 36 ∈ [0] ∧ a 24 ∈ [0,1] := by
  have b0 : a 5 ≠ 1 := exclude [0] (fun u v => edge r7 v u) (a 5) (a 1) 1 d1 c7 (by decide +kernel)
  have t0 : a 5 ∈ [0,2,3] := remove (a 5) 1 [0,1,2,3] d5 b0
  have b1 : a 5 ≠ 3 := exclude [0] (fun u v => edge r7 v u) (a 5) (a 1) 3 d1 c7 (by decide +kernel)
  have t1 : a 5 ∈ [0,2] := remove (a 5) 3 [0,2,3] t0 b1
  have b2 : a 16 ≠ 1 := exclude [0] (fun u v => edge r9 v u) (a 16) (a 1) 1 d1 c9 (by decide +kernel)
  have t2 : a 16 ∈ [0,2,3] := remove (a 16) 1 [0,1,2,3] d16 b2
  have b3 : a 16 ≠ 3 := exclude [0] (fun u v => edge r9 v u) (a 16) (a 1) 3 d1 c9 (by decide +kernel)
  have t3 : a 16 ∈ [0,2] := remove (a 16) 3 [0,2,3] t2 b3
  have b4 : a 30 ≠ 2 := exclude [0] (fun u v => edge r10 v u) (a 30) (a 1) 2 d1 c10 (by decide +kernel)
  have t4 : a 30 ∈ [0,1,3] := remove (a 30) 2 [0,1,2,3] d30 b4
  have b5 : a 30 ≠ 3 := exclude [0] (fun u v => edge r10 v u) (a 30) (a 1) 3 d1 c10 (by decide +kernel)
  have t5 : a 30 ∈ [0,1] := remove (a 30) 3 [0,1,3] t4 b5
  have b6 : a 32 ≠ 1 := exclude [0] (fun u v => edge r17 v u) (a 32) (a 3) 1 d3 c17 (by decide +kernel)
  have t6 : a 32 ∈ [0] := remove (a 32) 1 [0,1] d32 b6
  have b7 : a 34 ≠ 1 := exclude [0,2] (fun u v => edge r25 v u) (a 34) (a 5) 1 t1 c25 (by decide +kernel)
  have t7 : a 34 ∈ [0,2,3] := remove (a 34) 1 [0,1,2,3] d34 b7
  have b8 : a 34 ≠ 3 := exclude [0,2] (fun u v => edge r25 v u) (a 34) (a 5) 3 t1 c25 (by decide +kernel)
  have t8 : a 34 ∈ [0,2] := remove (a 34) 3 [0,2,3] t7 b8
  have b9 : a 20 ≠ 1 := exclude [0] (fun u v => edge r31 v u) (a 20) (a 7) 1 d7 c31 (by decide +kernel)
  have t9 : a 20 ∈ [0,2,3] := remove (a 20) 1 [0,1,2,3] d20 b9
  have b10 : a 20 ≠ 3 := exclude [0] (fun u v => edge r31 v u) (a 20) (a 7) 3 d7 c31 (by decide +kernel)
  have t10 : a 20 ∈ [0,2] := remove (a 20) 3 [0,2,3] t9 b10
  have b11 : a 21 ≠ 1 := exclude [0,1] (fun u v => edge r34 v u) (a 21) (a 8) 1 d8 c34 (by decide +kernel)
  have t11 : a 21 ∈ [0,2,3] := remove (a 21) 1 [0,1,2,3] d21 b11
  have b12 : a 21 ≠ 3 := exclude [0,1] (fun u v => edge r34 v u) (a 21) (a 8) 3 d8 c34 (by decide +kernel)
  have t12 : a 21 ∈ [0,2] := remove (a 21) 3 [0,2,3] t11 b12
  have b13 : a 36 ≠ 1 := exclude [0,1] (fun u v => edge r35 v u) (a 36) (a 8) 1 d8 c35 (by decide +kernel)
  have t13 : a 36 ∈ [0] := remove (a 36) 1 [0,1] d36 b13
  have b14 : a 24 ≠ 2 := exclude [0,1] (fun u v => edge r41 v u) (a 24) (a 10) 2 d10 c41 (by decide +kernel)
  have t14 : a 24 ∈ [0,1,3] := remove (a 24) 2 [0,1,2,3] d24 b14
  have b15 : a 24 ≠ 3 := exclude [0,1] (fun u v => edge r41 v u) (a 24) (a 10) 3 d10 c41 (by decide +kernel)
  have t15 : a 24 ∈ [0,1] := remove (a 24) 3 [0,1,3] t14 b15
  exact And.intro t1 (And.intro t3 (And.intro t5 (And.intro t6 (And.intro t8 (And.intro t10 (And.intro t12 (And.intro t13 (t15))))))))

theorem chunk1 (a : Nat → Nat)
    (d25 : a 25 ∈ [0,1,2,3])
    (d11 : a 11 ∈ [0,1])
    (d40 : a 40 ∈ [0,1,2,3])
    (d22 : a 22 ∈ [0,1])
    (d16 : a 16 ∈ [0,2])
    (d44 : a 44 ∈ [0,1,2,3])
    (d18 : a 18 ∈ [0,1,2,3])
    (d19 : a 19 ∈ [0,1])
    (d20 : a 20 ∈ [0,2])
    (d27 : a 27 ∈ [0,1,2,3])
    (d50 : a 50 ∈ [0,1,2,3])
    (d23 : a 23 ∈ [0,1,2,3])
    (d21 : a 21 ∈ [0,2])
    (c45 : edge r45 (a 11) (a 25)=true)
    (c46 : edge r46 (a 11) (a 40)=true)
    (c59 : edge r59 (a 16) (a 22)=true)
    (c60 : edge r60 (a 16) (a 44)=true)
    (c65 : edge r65 (a 18) (a 25)=true)
    (c67 : edge r67 (a 19) (a 20)=true)
    (c68 : edge r68 (a 19) (a 27)=true)
    (c71 : edge r71 (a 20) (a 50)=true)
    (c73 : edge r73 (a 21) (a 23)=true)
    : a 25 ∈ [0,1] ∧ a 40 ∈ [0,2] ∧ a 22 ∈ [0] ∧ a 44 ∈ [0,2] ∧ a 18 ∈ [0,1] ∧ a 19 ∈ [0] ∧ a 27 ∈ [0,2] ∧ a 50 ∈ [0,2] ∧ a 23 ∈ [0,2] := by
  have b0 : a 25 ≠ 2 := exclude [0,1] (fun u v => edge r45 v u) (a 25) (a 11) 2 d11 c45 (by decide +kernel)
  have t0 : a 25 ∈ [0,1,3] := remove (a 25) 2 [0,1,2,3] d25 b0
  have b1 : a 25 ≠ 3 := exclude [0,1] (fun u v => edge r45 v u) (a 25) (a 11) 3 d11 c45 (by decide +kernel)
  have t1 : a 25 ∈ [0,1] := remove (a 25) 3 [0,1,3] t0 b1
  have b2 : a 40 ≠ 1 := exclude [0,1] (fun u v => edge r46 v u) (a 40) (a 11) 1 d11 c46 (by decide +kernel)
  have t2 : a 40 ∈ [0,2,3] := remove (a 40) 1 [0,1,2,3] d40 b2
  have b3 : a 40 ≠ 3 := exclude [0,1] (fun u v => edge r46 v u) (a 40) (a 11) 3 d11 c46 (by decide +kernel)
  have t3 : a 40 ∈ [0,2] := remove (a 40) 3 [0,2,3] t2 b3
  have b4 : a 22 ≠ 1 := exclude [0,2] (fun u v => edge r59 v u) (a 22) (a 16) 1 d16 c59 (by decide +kernel)
  have t4 : a 22 ∈ [0] := remove (a 22) 1 [0,1] d22 b4
  have b5 : a 44 ≠ 1 := exclude [0,2] (fun u v => edge r60 v u) (a 44) (a 16) 1 d16 c60 (by decide +kernel)
  have t5 : a 44 ∈ [0,2,3] := remove (a 44) 1 [0,1,2,3] d44 b5
  have b6 : a 44 ≠ 3 := exclude [0,2] (fun u v => edge r60 v u) (a 44) (a 16) 3 d16 c60 (by decide +kernel)
  have t6 : a 44 ∈ [0,2] := remove (a 44) 3 [0,2,3] t5 b6
  have b7 : a 18 ≠ 2 := exclude [0,1] (edge r65) (a 18) (a 25) 2 t1 c65 (by decide +kernel)
  have t7 : a 18 ∈ [0,1,3] := remove (a 18) 2 [0,1,2,3] d18 b7
  have b8 : a 18 ≠ 3 := exclude [0,1] (edge r65) (a 18) (a 25) 3 t1 c65 (by decide +kernel)
  have t8 : a 18 ∈ [0,1] := remove (a 18) 3 [0,1,3] t7 b8
  have b9 : a 19 ≠ 1 := exclude [0,2] (edge r67) (a 19) (a 20) 1 d20 c67 (by decide +kernel)
  have t9 : a 19 ∈ [0] := remove (a 19) 1 [0,1] d19 b9
  have b10 : a 27 ≠ 1 := exclude [0] (fun u v => edge r68 v u) (a 27) (a 19) 1 t9 c68 (by decide +kernel)
  have t10 : a 27 ∈ [0,2,3] := remove (a 27) 1 [0,1,2,3] d27 b10
  have b11 : a 27 ≠ 3 := exclude [0] (fun u v => edge r68 v u) (a 27) (a 19) 3 t9 c68 (by decide +kernel)
  have t11 : a 27 ∈ [0,2] := remove (a 27) 3 [0,2,3] t10 b11
  have b12 : a 50 ≠ 1 := exclude [0,2] (fun u v => edge r71 v u) (a 50) (a 20) 1 d20 c71 (by decide +kernel)
  have t12 : a 50 ∈ [0,2,3] := remove (a 50) 1 [0,1,2,3] d50 b12
  have b13 : a 50 ≠ 3 := exclude [0,2] (fun u v => edge r71 v u) (a 50) (a 20) 3 d20 c71 (by decide +kernel)
  have t13 : a 50 ∈ [0,2] := remove (a 50) 3 [0,2,3] t12 b13
  have b14 : a 23 ≠ 1 := exclude [0,2] (fun u v => edge r73 v u) (a 23) (a 21) 1 d21 c73 (by decide +kernel)
  have t14 : a 23 ∈ [0,2,3] := remove (a 23) 1 [0,1,2,3] d23 b14
  have b15 : a 23 ≠ 3 := exclude [0,2] (fun u v => edge r73 v u) (a 23) (a 21) 3 d21 c73 (by decide +kernel)
  have t15 : a 23 ∈ [0,2] := remove (a 23) 3 [0,2,3] t14 b15
  exact And.intro t1 (And.intro t3 (And.intro t4 (And.intro t6 (And.intro t8 (And.intro t9 (And.intro t11 (And.intro t13 (t15))))))))

theorem chunk2 (a : Nat → Nat)
    (d52 : a 52 ∈ [0,1,2,3])
    (d22 : a 22 ∈ [0])
    (d53 : a 53 ∈ [0,1])
    (d23 : a 23 ∈ [0,2])
    (d55 : a 55 ∈ [0,1,2,3])
    (d25 : a 25 ∈ [0,1])
    (d57 : a 57 ∈ [0,1,2,3])
    (d27 : a 27 ∈ [0,2])
    (d37 : a 37 ∈ [0,1,2,3])
    (d30 : a 30 ∈ [0,1])
    (d46 : a 46 ∈ [0,1,2,3])
    (d32 : a 32 ∈ [0])
    (d33 : a 33 ∈ [0,1])
    (d34 : a 34 ∈ [0,2])
    (d35 : a 35 ∈ [0,1,2,3])
    (d48 : a 48 ∈ [0,1,2,3])
    (c78 : edge r78 (a 22) (a 52)=true)
    (c81 : edge r81 (a 23) (a 53)=true)
    (c86 : edge r86 (a 25) (a 55)=true)
    (c90 : edge r90 (a 27) (a 57)=true)
    (c99 : edge r99 (a 30) (a 37)=true)
    (c106 : edge r106 (a 32) (a 46)=true)
    (c107 : edge r107 (a 33) (a 34)=true)
    (c108 : edge r108 (a 33) (a 35)=true)
    (c112 : edge r112 (a 34) (a 48)=true)
    : a 52 ∈ [0,1] ∧ a 53 ∈ [0] ∧ a 55 ∈ [0,1] ∧ a 57 ∈ [0,1] ∧ a 37 ∈ [0,2] ∧ a 46 ∈ [0,2] ∧ a 33 ∈ [0] ∧ a 35 ∈ [0,1] ∧ a 48 ∈ [0,2] := by
  have b0 : a 52 ≠ 2 := exclude [0] (fun u v => edge r78 v u) (a 52) (a 22) 2 d22 c78 (by decide +kernel)
  have t0 : a 52 ∈ [0,1,3] := remove (a 52) 2 [0,1,2,3] d52 b0
  have b1 : a 52 ≠ 3 := exclude [0] (fun u v => edge r78 v u) (a 52) (a 22) 3 d22 c78 (by decide +kernel)
  have t1 : a 52 ∈ [0,1] := remove (a 52) 3 [0,1,3] t0 b1
  have b2 : a 53 ≠ 1 := exclude [0,2] (fun u v => edge r81 v u) (a 53) (a 23) 1 d23 c81 (by decide +kernel)
  have t2 : a 53 ∈ [0] := remove (a 53) 1 [0,1] d53 b2
  have b3 : a 55 ≠ 2 := exclude [0,1] (fun u v => edge r86 v u) (a 55) (a 25) 2 d25 c86 (by decide +kernel)
  have t3 : a 55 ∈ [0,1,3] := remove (a 55) 2 [0,1,2,3] d55 b3
  have b4 : a 55 ≠ 3 := exclude [0,1] (fun u v => edge r86 v u) (a 55) (a 25) 3 d25 c86 (by decide +kernel)
  have t4 : a 55 ∈ [0,1] := remove (a 55) 3 [0,1,3] t3 b4
  have b5 : a 57 ≠ 2 := exclude [0,2] (fun u v => edge r90 v u) (a 57) (a 27) 2 d27 c90 (by decide +kernel)
  have t5 : a 57 ∈ [0,1,3] := remove (a 57) 2 [0,1,2,3] d57 b5
  have b6 : a 57 ≠ 3 := exclude [0,2] (fun u v => edge r90 v u) (a 57) (a 27) 3 d27 c90 (by decide +kernel)
  have t6 : a 57 ∈ [0,1] := remove (a 57) 3 [0,1,3] t5 b6
  have b7 : a 37 ≠ 1 := exclude [0,1] (fun u v => edge r99 v u) (a 37) (a 30) 1 d30 c99 (by decide +kernel)
  have t7 : a 37 ∈ [0,2,3] := remove (a 37) 1 [0,1,2,3] d37 b7
  have b8 : a 37 ≠ 3 := exclude [0,1] (fun u v => edge r99 v u) (a 37) (a 30) 3 d30 c99 (by decide +kernel)
  have t8 : a 37 ∈ [0,2] := remove (a 37) 3 [0,2,3] t7 b8
  have b9 : a 46 ≠ 1 := exclude [0] (fun u v => edge r106 v u) (a 46) (a 32) 1 d32 c106 (by decide +kernel)
  have t9 : a 46 ∈ [0,2,3] := remove (a 46) 1 [0,1,2,3] d46 b9
  have b10 : a 46 ≠ 3 := exclude [0] (fun u v => edge r106 v u) (a 46) (a 32) 3 d32 c106 (by decide +kernel)
  have t10 : a 46 ∈ [0,2] := remove (a 46) 3 [0,2,3] t9 b10
  have b11 : a 33 ≠ 1 := exclude [0,2] (edge r107) (a 33) (a 34) 1 d34 c107 (by decide +kernel)
  have t11 : a 33 ∈ [0] := remove (a 33) 1 [0,1] d33 b11
  have b12 : a 35 ≠ 2 := exclude [0] (fun u v => edge r108 v u) (a 35) (a 33) 2 t11 c108 (by decide +kernel)
  have t12 : a 35 ∈ [0,1,3] := remove (a 35) 2 [0,1,2,3] d35 b12
  have b13 : a 35 ≠ 3 := exclude [0] (fun u v => edge r108 v u) (a 35) (a 33) 3 t11 c108 (by decide +kernel)
  have t13 : a 35 ∈ [0,1] := remove (a 35) 3 [0,1,3] t12 b13
  have b14 : a 48 ≠ 1 := exclude [0,2] (fun u v => edge r112 v u) (a 48) (a 34) 1 d34 c112 (by decide +kernel)
  have t14 : a 48 ∈ [0,2,3] := remove (a 48) 1 [0,1,2,3] d48 b14
  have b15 : a 48 ≠ 3 := exclude [0,2] (fun u v => edge r112 v u) (a 48) (a 34) 3 d34 c112 (by decide +kernel)
  have t15 : a 48 ∈ [0,2] := remove (a 48) 3 [0,2,3] t14 b15
  exact And.intro t1 (And.intro t2 (And.intro t4 (And.intro t6 (And.intro t8 (And.intro t10 (And.intro t11 (And.intro t13 (t15))))))))

theorem chunk3 (a : Nat → Nat)
    (d38 : a 38 ∈ [0,1,2,3])
    (d36 : a 36 ∈ [0])
    (d58 : a 58 ∈ [0,1])
    (d42 : a 42 ∈ [0,1])
    (d43 : a 43 ∈ [0,1])
    (d44 : a 44 ∈ [0,2])
    (d45 : a 45 ∈ [0,1,2,3])
    (d56 : a 56 ∈ [0,1])
    (d48 : a 48 ∈ [0,2])
    (c115 : edge r115 (a 36) (a 38)=true)
    (c129 : edge r129 (a 42) (a 58)=true)
    (c130 : edge r130 (a 43) (a 44)=true)
    (c131 : edge r131 (a 43) (a 45)=true)
    (c146 : edge r146 (a 48) (a 56)=true)
    : a 38 ∈ [0,2] ∧ a 58 ∈ [0] ∧ a 43 ∈ [0] ∧ a 45 ∈ [0,2] ∧ a 56 ∈ [0] := by
  have b0 : a 38 ≠ 1 := exclude [0] (fun u v => edge r115 v u) (a 38) (a 36) 1 d36 c115 (by decide +kernel)
  have t0 : a 38 ∈ [0,2,3] := remove (a 38) 1 [0,1,2,3] d38 b0
  have b1 : a 38 ≠ 3 := exclude [0] (fun u v => edge r115 v u) (a 38) (a 36) 3 d36 c115 (by decide +kernel)
  have t1 : a 38 ∈ [0,2] := remove (a 38) 3 [0,2,3] t0 b1
  have b2 : a 58 ≠ 1 := exclude [0,1] (fun u v => edge r129 v u) (a 58) (a 42) 1 d42 c129 (by decide +kernel)
  have t2 : a 58 ∈ [0] := remove (a 58) 1 [0,1] d58 b2
  have b3 : a 43 ≠ 1 := exclude [0,2] (edge r130) (a 43) (a 44) 1 d44 c130 (by decide +kernel)
  have t3 : a 43 ∈ [0] := remove (a 43) 1 [0,1] d43 b3
  have b4 : a 45 ≠ 1 := exclude [0] (fun u v => edge r131 v u) (a 45) (a 43) 1 t3 c131 (by decide +kernel)
  have t4 : a 45 ∈ [0,2,3] := remove (a 45) 1 [0,1,2,3] d45 b4
  have b5 : a 45 ≠ 3 := exclude [0] (fun u v => edge r131 v u) (a 45) (a 43) 3 t3 c131 (by decide +kernel)
  have t5 : a 45 ∈ [0,2] := remove (a 45) 3 [0,2,3] t4 b5
  have b6 : a 56 ≠ 1 := exclude [0,2] (fun u v => edge r146 v u) (a 56) (a 48) 1 d48 c146 (by decide +kernel)
  have t6 : a 56 ∈ [0] := remove (a 56) 1 [0,1] d56 b6
  exact And.intro t1 (And.intro t2 (And.intro t3 (And.intro t5 (t6))))

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_222
