import PartitionData205_222
namespace PartitionCover205_222
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d6 : a 6 ∈ [0,1])
    (d2 : a 2 ∈ [0])
    (d17 : a 17 ∈ [0,1])
    (d31 : a 31 ∈ [0,1])
    (d4 : a 4 ∈ [0,1])
    (d11 : a 11 ∈ [0,1])
    (d18 : a 18 ∈ [0,1])
    (d13 : a 13 ∈ [0,1])
    (d35 : a 35 ∈ [0,1])
    (d8 : a 8 ∈ [0,1])
    (d21 : a 21 ∈ [0,2])
    (d25 : a 25 ∈ [0,1])
    (d40 : a 40 ∈ [0,2])
    (d27 : a 27 ∈ [0,2])
    (d15 : a 15 ∈ [0,1])
    (d23 : a 23 ∈ [0,2])
    (d45 : a 45 ∈ [0,2])
    (c12 : edge r12 (a 2) (a 6)=true)
    (c13 : edge r13 (a 2) (a 17)=true)
    (c14 : edge r14 (a 2) (a 31)=true)
    (c19 : edge r19 (a 4) (a 6)=true)
    (c20 : edge r20 (a 4) (a 11)=true)
    (c21 : edge r21 (a 4) (a 18)=true)
    (c27 : edge r27 (a 6) (a 13)=true)
    (c29 : edge r29 (a 6) (a 35)=true)
    (c33 : edge r33 (a 8) (a 11)=true)
    (c34 : edge r34 (a 8) (a 21)=true)
    (c45 : edge r45 (a 11) (a 25)=true)
    (c46 : edge r46 (a 11) (a 40)=true)
    (c51 : edge r51 (a 13) (a 27)=true)
    (c55 : edge r55 (a 15) (a 17)=true)
    (c62 : edge r62 (a 17) (a 23)=true)
    (c63 : edge r63 (a 17) (a 45)=true)
    : a 6 ∈ [0] ∧ a 17 ∈ [0] ∧ a 31 ∈ [0] ∧ a 4 ∈ [0] ∧ a 11 ∈ [0] ∧ a 18 ∈ [0] ∧ a 13 ∈ [0] ∧ a 35 ∈ [0] ∧ a 8 ∈ [0] ∧ a 21 ∈ [0] ∧ a 25 ∈ [0] ∧ a 40 ∈ [0] ∧ a 27 ∈ [0] ∧ a 15 ∈ [0] ∧ a 23 ∈ [0] ∧ a 45 ∈ [0] := by
  have b0 : a 6 ≠ 1 := exclude [0] (fun u v => edge r12 v u) (a 6) (a 2) 1 d2 c12 (by decide +kernel)
  have t0 : a 6 ∈ [0] := remove (a 6) 1 [0,1] d6 b0
  have b1 : a 17 ≠ 1 := exclude [0] (fun u v => edge r13 v u) (a 17) (a 2) 1 d2 c13 (by decide +kernel)
  have t1 : a 17 ∈ [0] := remove (a 17) 1 [0,1] d17 b1
  have b2 : a 31 ≠ 1 := exclude [0] (fun u v => edge r14 v u) (a 31) (a 2) 1 d2 c14 (by decide +kernel)
  have t2 : a 31 ∈ [0] := remove (a 31) 1 [0,1] d31 b2
  have b3 : a 4 ≠ 1 := exclude [0] (edge r19) (a 4) (a 6) 1 t0 c19 (by decide +kernel)
  have t3 : a 4 ∈ [0] := remove (a 4) 1 [0,1] d4 b3
  have b4 : a 11 ≠ 1 := exclude [0] (fun u v => edge r20 v u) (a 11) (a 4) 1 t3 c20 (by decide +kernel)
  have t4 : a 11 ∈ [0] := remove (a 11) 1 [0,1] d11 b4
  have b5 : a 18 ≠ 1 := exclude [0] (fun u v => edge r21 v u) (a 18) (a 4) 1 t3 c21 (by decide +kernel)
  have t5 : a 18 ∈ [0] := remove (a 18) 1 [0,1] d18 b5
  have b6 : a 13 ≠ 1 := exclude [0] (fun u v => edge r27 v u) (a 13) (a 6) 1 t0 c27 (by decide +kernel)
  have t6 : a 13 ∈ [0] := remove (a 13) 1 [0,1] d13 b6
  have b7 : a 35 ≠ 1 := exclude [0] (fun u v => edge r29 v u) (a 35) (a 6) 1 t0 c29 (by decide +kernel)
  have t7 : a 35 ∈ [0] := remove (a 35) 1 [0,1] d35 b7
  have b8 : a 8 ≠ 1 := exclude [0] (edge r33) (a 8) (a 11) 1 t4 c33 (by decide +kernel)
  have t8 : a 8 ∈ [0] := remove (a 8) 1 [0,1] d8 b8
  have b9 : a 21 ≠ 2 := exclude [0] (fun u v => edge r34 v u) (a 21) (a 8) 2 t8 c34 (by decide +kernel)
  have t9 : a 21 ∈ [0] := remove (a 21) 2 [0,2] d21 b9
  have b10 : a 25 ≠ 1 := exclude [0] (fun u v => edge r45 v u) (a 25) (a 11) 1 t4 c45 (by decide +kernel)
  have t10 : a 25 ∈ [0] := remove (a 25) 1 [0,1] d25 b10
  have b11 : a 40 ≠ 2 := exclude [0] (fun u v => edge r46 v u) (a 40) (a 11) 2 t4 c46 (by decide +kernel)
  have t11 : a 40 ∈ [0] := remove (a 40) 2 [0,2] d40 b11
  have b12 : a 27 ≠ 2 := exclude [0] (fun u v => edge r51 v u) (a 27) (a 13) 2 t6 c51 (by decide +kernel)
  have t12 : a 27 ∈ [0] := remove (a 27) 2 [0,2] d27 b12
  have b13 : a 15 ≠ 1 := exclude [0] (edge r55) (a 15) (a 17) 1 t1 c55 (by decide +kernel)
  have t13 : a 15 ∈ [0] := remove (a 15) 1 [0,1] d15 b13
  have b14 : a 23 ≠ 2 := exclude [0] (fun u v => edge r62 v u) (a 23) (a 17) 2 t1 c62 (by decide +kernel)
  have t14 : a 23 ∈ [0] := remove (a 23) 2 [0,2] d23 b14
  have b15 : a 45 ≠ 2 := exclude [0] (fun u v => edge r63 v u) (a 45) (a 17) 2 t1 c63 (by decide +kernel)
  have t15 : a 45 ∈ [0] := remove (a 45) 2 [0,2] d45 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk5 (a : Nat → Nat)
    (d47 : a 47 ∈ [0,1])
    (d18 : a 18 ∈ [0])
    (d51 : a 51 ∈ [0,1])
    (d21 : a 21 ∈ [0])
    (d24 : a 24 ∈ [0,1])
    (d23 : a 23 ∈ [0])
    (d28 : a 28 ∈ [0,1])
    (d54 : a 54 ∈ [0,1])
    (d26 : a 26 ∈ [0,1])
    (d25 : a 25 ∈ [0])
    (d55 : a 55 ∈ [0,1])
    (d57 : a 57 ∈ [0,1])
    (d27 : a 27 ∈ [0])
    (d29 : a 29 ∈ [0,1])
    (d31 : a 31 ∈ [0])
    (d38 : a 38 ∈ [0,2])
    (d49 : a 49 ∈ [0,1])
    (d35 : a 35 ∈ [0])
    (d39 : a 39 ∈ [0,1])
    (d42 : a 42 ∈ [0,1])
    (d41 : a 41 ∈ [0,1])
    (d40 : a 40 ∈ [0])
    (d46 : a 46 ∈ [0,2])
    (d45 : a 45 ∈ [0])
    (d50 : a 50 ∈ [0,2])
    (c66 : edge r66 (a 18) (a 47)=true)
    (c75 : edge r75 (a 21) (a 51)=true)
    (c79 : edge r79 (a 23) (a 24)=true)
    (c82 : edge r82 (a 24) (a 28)=true)
    (c83 : edge r83 (a 24) (a 54)=true)
    (c84 : edge r84 (a 25) (a 26)=true)
    (c86 : edge r86 (a 25) (a 55)=true)
    (c90 : edge r90 (a 27) (a 57)=true)
    (c93 : edge r93 (a 29) (a 31)=true)
    (c103 : edge r103 (a 31) (a 38)=true)
    (c113 : edge r113 (a 35) (a 49)=true)
    (c121 : edge r121 (a 38) (a 39)=true)
    (c123 : edge r123 (a 39) (a 42)=true)
    (c125 : edge r125 (a 40) (a 41)=true)
    (c137 : edge r137 (a 45) (a 46)=true)
    (c140 : edge r140 (a 46) (a 50)=true)
    : a 47 ∈ [0] ∧ a 51 ∈ [0] ∧ a 24 ∈ [0] ∧ a 28 ∈ [0] ∧ a 54 ∈ [0] ∧ a 26 ∈ [0] ∧ a 55 ∈ [0] ∧ a 57 ∈ [0] ∧ a 29 ∈ [0] ∧ a 38 ∈ [0] ∧ a 49 ∈ [0] ∧ a 39 ∈ [0] ∧ a 42 ∈ [0] ∧ a 41 ∈ [0] ∧ a 46 ∈ [0] ∧ a 50 ∈ [0] := by
  have b0 : a 47 ≠ 1 := exclude [0] (fun u v => edge r66 v u) (a 47) (a 18) 1 d18 c66 (by decide +kernel)
  have t0 : a 47 ∈ [0] := remove (a 47) 1 [0,1] d47 b0
  have b1 : a 51 ≠ 1 := exclude [0] (fun u v => edge r75 v u) (a 51) (a 21) 1 d21 c75 (by decide +kernel)
  have t1 : a 51 ∈ [0] := remove (a 51) 1 [0,1] d51 b1
  have b2 : a 24 ≠ 1 := exclude [0] (fun u v => edge r79 v u) (a 24) (a 23) 1 d23 c79 (by decide +kernel)
  have t2 : a 24 ∈ [0] := remove (a 24) 1 [0,1] d24 b2
  have b3 : a 28 ≠ 1 := exclude [0] (fun u v => edge r82 v u) (a 28) (a 24) 1 t2 c82 (by decide +kernel)
  have t3 : a 28 ∈ [0] := remove (a 28) 1 [0,1] d28 b3
  have b4 : a 54 ≠ 1 := exclude [0] (fun u v => edge r83 v u) (a 54) (a 24) 1 t2 c83 (by decide +kernel)
  have t4 : a 54 ∈ [0] := remove (a 54) 1 [0,1] d54 b4
  have b5 : a 26 ≠ 1 := exclude [0] (fun u v => edge r84 v u) (a 26) (a 25) 1 d25 c84 (by decide +kernel)
  have t5 : a 26 ∈ [0] := remove (a 26) 1 [0,1] d26 b5
  have b6 : a 55 ≠ 1 := exclude [0] (fun u v => edge r86 v u) (a 55) (a 25) 1 d25 c86 (by decide +kernel)
  have t6 : a 55 ∈ [0] := remove (a 55) 1 [0,1] d55 b6
  have b7 : a 57 ≠ 1 := exclude [0] (fun u v => edge r90 v u) (a 57) (a 27) 1 d27 c90 (by decide +kernel)
  have t7 : a 57 ∈ [0] := remove (a 57) 1 [0,1] d57 b7
  have b8 : a 29 ≠ 1 := exclude [0] (edge r93) (a 29) (a 31) 1 d31 c93 (by decide +kernel)
  have t8 : a 29 ∈ [0] := remove (a 29) 1 [0,1] d29 b8
  have b9 : a 38 ≠ 2 := exclude [0] (fun u v => edge r103 v u) (a 38) (a 31) 2 d31 c103 (by decide +kernel)
  have t9 : a 38 ∈ [0] := remove (a 38) 2 [0,2] d38 b9
  have b10 : a 49 ≠ 1 := exclude [0] (fun u v => edge r113 v u) (a 49) (a 35) 1 d35 c113 (by decide +kernel)
  have t10 : a 49 ∈ [0] := remove (a 49) 1 [0,1] d49 b10
  have b11 : a 39 ≠ 1 := exclude [0] (fun u v => edge r121 v u) (a 39) (a 38) 1 t9 c121 (by decide +kernel)
  have t11 : a 39 ∈ [0] := remove (a 39) 1 [0,1] d39 b11
  have b12 : a 42 ≠ 1 := exclude [0] (fun u v => edge r123 v u) (a 42) (a 39) 1 t11 c123 (by decide +kernel)
  have t12 : a 42 ∈ [0] := remove (a 42) 1 [0,1] d42 b12
  have b13 : a 41 ≠ 1 := exclude [0] (fun u v => edge r125 v u) (a 41) (a 40) 1 d40 c125 (by decide +kernel)
  have t13 : a 41 ∈ [0] := remove (a 41) 1 [0,1] d41 b13
  have b14 : a 46 ≠ 2 := exclude [0] (fun u v => edge r137 v u) (a 46) (a 45) 2 d45 c137 (by decide +kernel)
  have t14 : a 46 ∈ [0] := remove (a 46) 2 [0,2] d46 b14
  have b15 : a 50 ≠ 2 := exclude [0] (fun u v => edge r140 v u) (a 50) (a 46) 2 t14 c140 (by decide +kernel)
  have t15 : a 50 ∈ [0] := remove (a 50) 2 [0,2] d50 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk6 (a : Nat → Nat)
    (d48 : a 48 ∈ [0,2])
    (d47 : a 47 ∈ [0])
    (d52 : a 52 ∈ [0,1])
    (d51 : a 51 ∈ [0])
    (d5 : a 5 ∈ [0,2])
    (d4 : a 4 ∈ [0])
    (d34 : a 34 ∈ [0,2])
    (d9 : a 9 ∈ [0,1])
    (d8 : a 8 ∈ [0])
    (d10 : a 10 ∈ [0,1])
    (d37 : a 37 ∈ [0,2])
    (d16 : a 16 ∈ [0,2])
    (d15 : a 15 ∈ [0])
    (d44 : a 44 ∈ [0,2])
    (d20 : a 20 ∈ [0,2])
    (d28 : a 28 ∈ [0])
    (d30 : a 30 ∈ [0,1])
    (d29 : a 29 ∈ [0])
    (c18 : edge r18 (a 4) (a 5)=true)
    (c25 : edge r25 (a 5) (a 34)=true)
    (c32 : edge r32 (a 8) (a 9)=true)
    (c36 : edge r36 (a 9) (a 10)=true)
    (c39 : edge r39 (a 9) (a 37)=true)
    (c54 : edge r54 (a 15) (a 16)=true)
    (c60 : edge r60 (a 16) (a 44)=true)
    (c70 : edge r70 (a 20) (a 28)=true)
    (c92 : edge r92 (a 29) (a 30)=true)
    (c142 : edge r142 (a 47) (a 48)=true)
    (c150 : edge r150 (a 51) (a 52)=true)
    : a 48 ∈ [0] ∧ a 52 ∈ [0] ∧ a 5 ∈ [0] ∧ a 34 ∈ [0] ∧ a 9 ∈ [0] ∧ a 10 ∈ [0] ∧ a 37 ∈ [0] ∧ a 16 ∈ [0] ∧ a 44 ∈ [0] ∧ a 20 ∈ [0] ∧ a 30 ∈ [0] := by
  have b0 : a 48 ≠ 2 := exclude [0] (fun u v => edge r142 v u) (a 48) (a 47) 2 d47 c142 (by decide +kernel)
  have t0 : a 48 ∈ [0] := remove (a 48) 2 [0,2] d48 b0
  have b1 : a 52 ≠ 1 := exclude [0] (fun u v => edge r150 v u) (a 52) (a 51) 1 d51 c150 (by decide +kernel)
  have t1 : a 52 ∈ [0] := remove (a 52) 1 [0,1] d52 b1
  have b2 : a 5 ≠ 2 := exclude [0] (fun u v => edge r18 v u) (a 5) (a 4) 2 d4 c18 (by decide +kernel)
  have t2 : a 5 ∈ [0] := remove (a 5) 2 [0,2] d5 b2
  have b3 : a 34 ≠ 2 := exclude [0] (fun u v => edge r25 v u) (a 34) (a 5) 2 t2 c25 (by decide +kernel)
  have t3 : a 34 ∈ [0] := remove (a 34) 2 [0,2] d34 b3
  have b4 : a 9 ≠ 1 := exclude [0] (fun u v => edge r32 v u) (a 9) (a 8) 1 d8 c32 (by decide +kernel)
  have t4 : a 9 ∈ [0] := remove (a 9) 1 [0,1] d9 b4
  have b5 : a 10 ≠ 1 := exclude [0] (fun u v => edge r36 v u) (a 10) (a 9) 1 t4 c36 (by decide +kernel)
  have t5 : a 10 ∈ [0] := remove (a 10) 1 [0,1] d10 b5
  have b6 : a 37 ≠ 2 := exclude [0] (fun u v => edge r39 v u) (a 37) (a 9) 2 t4 c39 (by decide +kernel)
  have t6 : a 37 ∈ [0] := remove (a 37) 2 [0,2] d37 b6
  have b7 : a 16 ≠ 2 := exclude [0] (fun u v => edge r54 v u) (a 16) (a 15) 2 d15 c54 (by decide +kernel)
  have t7 : a 16 ∈ [0] := remove (a 16) 2 [0,2] d16 b7
  have b8 : a 44 ≠ 2 := exclude [0] (fun u v => edge r60 v u) (a 44) (a 16) 2 t7 c60 (by decide +kernel)
  have t8 : a 44 ∈ [0] := remove (a 44) 2 [0,2] d44 b8
  have b9 : a 20 ≠ 2 := exclude [0] (edge r70) (a 20) (a 28) 2 d28 c70 (by decide +kernel)
  have t9 : a 20 ∈ [0] := remove (a 20) 2 [0,2] d20 b9
  have b10 : a 30 ≠ 1 := exclude [0] (fun u v => edge r92 v u) (a 30) (a 29) 1 d29 c92 (by decide +kernel)
  have t10 : a 30 ∈ [0] := remove (a 30) 1 [0,1] d30 b10
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (t10))))))))))

theorem chunk7 (a : Nat → Nat)
    (d6 : a 6 ∈ [0,1])
    (d2 : a 2 ∈ [1])
    (d17 : a 17 ∈ [0,1])
    (d31 : a 31 ∈ [0,1])
    (d4 : a 4 ∈ [0,1])
    (d11 : a 11 ∈ [0,1])
    (d18 : a 18 ∈ [0,1])
    (d13 : a 13 ∈ [0,1])
    (d35 : a 35 ∈ [0,1])
    (d8 : a 8 ∈ [0,1])
    (d21 : a 21 ∈ [0,2])
    (d25 : a 25 ∈ [0,1])
    (d40 : a 40 ∈ [0,2])
    (d27 : a 27 ∈ [0,2])
    (d15 : a 15 ∈ [0,1])
    (d23 : a 23 ∈ [0,2])
    (d45 : a 45 ∈ [0,2])
    (c12 : edge r12 (a 2) (a 6)=true)
    (c13 : edge r13 (a 2) (a 17)=true)
    (c14 : edge r14 (a 2) (a 31)=true)
    (c19 : edge r19 (a 4) (a 6)=true)
    (c20 : edge r20 (a 4) (a 11)=true)
    (c21 : edge r21 (a 4) (a 18)=true)
    (c27 : edge r27 (a 6) (a 13)=true)
    (c29 : edge r29 (a 6) (a 35)=true)
    (c33 : edge r33 (a 8) (a 11)=true)
    (c34 : edge r34 (a 8) (a 21)=true)
    (c45 : edge r45 (a 11) (a 25)=true)
    (c46 : edge r46 (a 11) (a 40)=true)
    (c51 : edge r51 (a 13) (a 27)=true)
    (c55 : edge r55 (a 15) (a 17)=true)
    (c62 : edge r62 (a 17) (a 23)=true)
    (c63 : edge r63 (a 17) (a 45)=true)
    : a 6 ∈ [1] ∧ a 17 ∈ [1] ∧ a 31 ∈ [1] ∧ a 4 ∈ [1] ∧ a 11 ∈ [1] ∧ a 18 ∈ [1] ∧ a 13 ∈ [1] ∧ a 35 ∈ [1] ∧ a 8 ∈ [1] ∧ a 21 ∈ [2] ∧ a 25 ∈ [1] ∧ a 40 ∈ [2] ∧ a 27 ∈ [2] ∧ a 15 ∈ [1] ∧ a 23 ∈ [2] ∧ a 45 ∈ [2] := by
  have b0 : a 6 ≠ 0 := exclude [1] (fun u v => edge r12 v u) (a 6) (a 2) 0 d2 c12 (by decide +kernel)
  have t0 : a 6 ∈ [1] := remove (a 6) 0 [0,1] d6 b0
  have b1 : a 17 ≠ 0 := exclude [1] (fun u v => edge r13 v u) (a 17) (a 2) 0 d2 c13 (by decide +kernel)
  have t1 : a 17 ∈ [1] := remove (a 17) 0 [0,1] d17 b1
  have b2 : a 31 ≠ 0 := exclude [1] (fun u v => edge r14 v u) (a 31) (a 2) 0 d2 c14 (by decide +kernel)
  have t2 : a 31 ∈ [1] := remove (a 31) 0 [0,1] d31 b2
  have b3 : a 4 ≠ 0 := exclude [1] (edge r19) (a 4) (a 6) 0 t0 c19 (by decide +kernel)
  have t3 : a 4 ∈ [1] := remove (a 4) 0 [0,1] d4 b3
  have b4 : a 11 ≠ 0 := exclude [1] (fun u v => edge r20 v u) (a 11) (a 4) 0 t3 c20 (by decide +kernel)
  have t4 : a 11 ∈ [1] := remove (a 11) 0 [0,1] d11 b4
  have b5 : a 18 ≠ 0 := exclude [1] (fun u v => edge r21 v u) (a 18) (a 4) 0 t3 c21 (by decide +kernel)
  have t5 : a 18 ∈ [1] := remove (a 18) 0 [0,1] d18 b5
  have b6 : a 13 ≠ 0 := exclude [1] (fun u v => edge r27 v u) (a 13) (a 6) 0 t0 c27 (by decide +kernel)
  have t6 : a 13 ∈ [1] := remove (a 13) 0 [0,1] d13 b6
  have b7 : a 35 ≠ 0 := exclude [1] (fun u v => edge r29 v u) (a 35) (a 6) 0 t0 c29 (by decide +kernel)
  have t7 : a 35 ∈ [1] := remove (a 35) 0 [0,1] d35 b7
  have b8 : a 8 ≠ 0 := exclude [1] (edge r33) (a 8) (a 11) 0 t4 c33 (by decide +kernel)
  have t8 : a 8 ∈ [1] := remove (a 8) 0 [0,1] d8 b8
  have b9 : a 21 ≠ 0 := exclude [1] (fun u v => edge r34 v u) (a 21) (a 8) 0 t8 c34 (by decide +kernel)
  have t9 : a 21 ∈ [2] := remove (a 21) 0 [0,2] d21 b9
  have b10 : a 25 ≠ 0 := exclude [1] (fun u v => edge r45 v u) (a 25) (a 11) 0 t4 c45 (by decide +kernel)
  have t10 : a 25 ∈ [1] := remove (a 25) 0 [0,1] d25 b10
  have b11 : a 40 ≠ 0 := exclude [1] (fun u v => edge r46 v u) (a 40) (a 11) 0 t4 c46 (by decide +kernel)
  have t11 : a 40 ∈ [2] := remove (a 40) 0 [0,2] d40 b11
  have b12 : a 27 ≠ 0 := exclude [1] (fun u v => edge r51 v u) (a 27) (a 13) 0 t6 c51 (by decide +kernel)
  have t12 : a 27 ∈ [2] := remove (a 27) 0 [0,2] d27 b12
  have b13 : a 15 ≠ 0 := exclude [1] (edge r55) (a 15) (a 17) 0 t1 c55 (by decide +kernel)
  have t13 : a 15 ∈ [1] := remove (a 15) 0 [0,1] d15 b13
  have b14 : a 23 ≠ 0 := exclude [1] (fun u v => edge r62 v u) (a 23) (a 17) 0 t1 c62 (by decide +kernel)
  have t14 : a 23 ∈ [2] := remove (a 23) 0 [0,2] d23 b14
  have b15 : a 45 ≠ 0 := exclude [1] (fun u v => edge r63 v u) (a 45) (a 17) 0 t1 c63 (by decide +kernel)
  have t15 : a 45 ∈ [2] := remove (a 45) 0 [0,2] d45 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_222
