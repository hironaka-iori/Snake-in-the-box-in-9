import PartitionData205_227
namespace PartitionCover205_227
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d10 : a 10 ∈ [0,1])
    (d2 : a 2 ∈ [1])
    (d17 : a 17 ∈ [0,1])
    (d31 : a 31 ∈ [0,1])
    (d8 : a 8 ∈ [0,1])
    (d12 : a 12 ∈ [0,1])
    (d11 : a 11 ∈ [0,2])
    (d13 : a 13 ∈ [0,1])
    (d25 : a 25 ∈ [0,1])
    (d38 : a 38 ∈ [0,1])
    (d14 : a 14 ∈ [0,1])
    (d26 : a 26 ∈ [0,1])
    (d40 : a 40 ∈ [0,2])
    (d28 : a 28 ∈ [0,2])
    (d42 : a 42 ∈ [0,2])
    (d15 : a 15 ∈ [0,2])
    (d18 : a 18 ∈ [0,2])
    (c13 : edge r13 (a 2) (a 10)=true)
    (c14 : edge r14 (a 2) (a 17)=true)
    (c15 : edge r15 (a 2) (a 31)=true)
    (c35 : edge r35 (a 8) (a 10)=true)
    (c36 : edge r36 (a 8) (a 12)=true)
    (c42 : edge r42 (a 10) (a 11)=true)
    (c43 : edge r43 (a 10) (a 13)=true)
    (c44 : edge r44 (a 10) (a 25)=true)
    (c45 : edge r45 (a 10) (a 38)=true)
    (c46 : edge r46 (a 11) (a 14)=true)
    (c49 : edge r49 (a 12) (a 26)=true)
    (c50 : edge r50 (a 12) (a 40)=true)
    (c52 : edge r52 (a 14) (a 28)=true)
    (c53 : edge r53 (a 14) (a 42)=true)
    (c55 : edge r55 (a 15) (a 17)=true)
    (c63 : edge r63 (a 17) (a 18)=true)
    : a 10 ∈ [1] ∧ a 17 ∈ [1] ∧ a 31 ∈ [1] ∧ a 8 ∈ [1] ∧ a 12 ∈ [1] ∧ a 11 ∈ [2] ∧ a 13 ∈ [1] ∧ a 25 ∈ [1] ∧ a 38 ∈ [1] ∧ a 14 ∈ [1] ∧ a 26 ∈ [1] ∧ a 40 ∈ [2] ∧ a 28 ∈ [2] ∧ a 42 ∈ [2] ∧ a 15 ∈ [2] ∧ a 18 ∈ [2] := by
  have b0 : a 10 ≠ 0 := exclude [1] (fun u v => edge r13 v u) (a 10) (a 2) 0 d2 c13 (by decide +kernel)
  have t0 : a 10 ∈ [1] := remove (a 10) 0 [0,1] d10 b0
  have b1 : a 17 ≠ 0 := exclude [1] (fun u v => edge r14 v u) (a 17) (a 2) 0 d2 c14 (by decide +kernel)
  have t1 : a 17 ∈ [1] := remove (a 17) 0 [0,1] d17 b1
  have b2 : a 31 ≠ 0 := exclude [1] (fun u v => edge r15 v u) (a 31) (a 2) 0 d2 c15 (by decide +kernel)
  have t2 : a 31 ∈ [1] := remove (a 31) 0 [0,1] d31 b2
  have b3 : a 8 ≠ 0 := exclude [1] (edge r35) (a 8) (a 10) 0 t0 c35 (by decide +kernel)
  have t3 : a 8 ∈ [1] := remove (a 8) 0 [0,1] d8 b3
  have b4 : a 12 ≠ 0 := exclude [1] (fun u v => edge r36 v u) (a 12) (a 8) 0 t3 c36 (by decide +kernel)
  have t4 : a 12 ∈ [1] := remove (a 12) 0 [0,1] d12 b4
  have b5 : a 11 ≠ 0 := exclude [1] (fun u v => edge r42 v u) (a 11) (a 10) 0 t0 c42 (by decide +kernel)
  have t5 : a 11 ∈ [2] := remove (a 11) 0 [0,2] d11 b5
  have b6 : a 13 ≠ 0 := exclude [1] (fun u v => edge r43 v u) (a 13) (a 10) 0 t0 c43 (by decide +kernel)
  have t6 : a 13 ∈ [1] := remove (a 13) 0 [0,1] d13 b6
  have b7 : a 25 ≠ 0 := exclude [1] (fun u v => edge r44 v u) (a 25) (a 10) 0 t0 c44 (by decide +kernel)
  have t7 : a 25 ∈ [1] := remove (a 25) 0 [0,1] d25 b7
  have b8 : a 38 ≠ 0 := exclude [1] (fun u v => edge r45 v u) (a 38) (a 10) 0 t0 c45 (by decide +kernel)
  have t8 : a 38 ∈ [1] := remove (a 38) 0 [0,1] d38 b8
  have b9 : a 14 ≠ 0 := exclude [2] (fun u v => edge r46 v u) (a 14) (a 11) 0 t5 c46 (by decide +kernel)
  have t9 : a 14 ∈ [1] := remove (a 14) 0 [0,1] d14 b9
  have b10 : a 26 ≠ 0 := exclude [1] (fun u v => edge r49 v u) (a 26) (a 12) 0 t4 c49 (by decide +kernel)
  have t10 : a 26 ∈ [1] := remove (a 26) 0 [0,1] d26 b10
  have b11 : a 40 ≠ 0 := exclude [1] (fun u v => edge r50 v u) (a 40) (a 12) 0 t4 c50 (by decide +kernel)
  have t11 : a 40 ∈ [2] := remove (a 40) 0 [0,2] d40 b11
  have b12 : a 28 ≠ 0 := exclude [1] (fun u v => edge r52 v u) (a 28) (a 14) 0 t9 c52 (by decide +kernel)
  have t12 : a 28 ∈ [2] := remove (a 28) 0 [0,2] d28 b12
  have b13 : a 42 ≠ 0 := exclude [1] (fun u v => edge r53 v u) (a 42) (a 14) 0 t9 c53 (by decide +kernel)
  have t13 : a 42 ∈ [2] := remove (a 42) 0 [0,2] d42 b13
  have b14 : a 15 ≠ 0 := exclude [1] (edge r55) (a 15) (a 17) 0 t1 c55 (by decide +kernel)
  have t14 : a 15 ∈ [2] := remove (a 15) 0 [0,2] d15 b14
  have b15 : a 18 ≠ 0 := exclude [1] (fun u v => edge r63 v u) (a 18) (a 17) 0 t1 c63 (by decide +kernel)
  have t15 : a 18 ∈ [2] := remove (a 18) 0 [0,2] d18 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk9 (a : Nat → Nat)
    (d21 : a 21 ∈ [0,1])
    (d17 : a 17 ∈ [1])
    (d45 : a 45 ∈ [0,2])
    (d46 : a 46 ∈ [0,1])
    (d18 : a 18 ∈ [2])
    (d49 : a 49 ∈ [0,1])
    (d27 : a 27 ∈ [0,1])
    (d26 : a 26 ∈ [1])
    (d55 : a 55 ∈ [0,2])
    (d29 : a 29 ∈ [0,1])
    (d31 : a 31 ∈ [1])
    (d35 : a 35 ∈ [0,1])
    (d41 : a 41 ∈ [0,1])
    (d40 : a 40 ∈ [2])
    (d44 : a 44 ∈ [0,1])
    (d48 : a 48 ∈ [0,1])
    (d51 : a 51 ∈ [0,2])
    (d50 : a 50 ∈ [0,1])
    (d53 : a 53 ∈ [0,2])
    (d47 : a 47 ∈ [0,2])
    (d56 : a 56 ∈ [0,1])
    (c64 : edge r64 (a 17) (a 21)=true)
    (c66 : edge r66 (a 17) (a 45)=true)
    (c68 : edge r68 (a 18) (a 46)=true)
    (c77 : edge r77 (a 21) (a 49)=true)
    (c86 : edge r86 (a 26) (a 27)=true)
    (c89 : edge r89 (a 27) (a 55)=true)
    (c91 : edge r91 (a 29) (a 31)=true)
    (c100 : edge r100 (a 31) (a 35)=true)
    (c122 : edge r122 (a 40) (a 41)=true)
    (c129 : edge r129 (a 44) (a 46)=true)
    (c130 : edge r130 (a 44) (a 48)=true)
    (c131 : edge r131 (a 44) (a 51)=true)
    (c135 : edge r135 (a 46) (a 50)=true)
    (c136 : edge r136 (a 46) (a 53)=true)
    (c137 : edge r137 (a 47) (a 48)=true)
    (c143 : edge r143 (a 49) (a 56)=true)
    : a 21 ∈ [1] ∧ a 45 ∈ [2] ∧ a 46 ∈ [1] ∧ a 49 ∈ [1] ∧ a 27 ∈ [1] ∧ a 55 ∈ [2] ∧ a 29 ∈ [1] ∧ a 35 ∈ [1] ∧ a 41 ∈ [1] ∧ a 44 ∈ [1] ∧ a 48 ∈ [1] ∧ a 51 ∈ [2] ∧ a 50 ∈ [1] ∧ a 53 ∈ [2] ∧ a 47 ∈ [2] ∧ a 56 ∈ [1] := by
  have b0 : a 21 ≠ 0 := exclude [1] (fun u v => edge r64 v u) (a 21) (a 17) 0 d17 c64 (by decide +kernel)
  have t0 : a 21 ∈ [1] := remove (a 21) 0 [0,1] d21 b0
  have b1 : a 45 ≠ 0 := exclude [1] (fun u v => edge r66 v u) (a 45) (a 17) 0 d17 c66 (by decide +kernel)
  have t1 : a 45 ∈ [2] := remove (a 45) 0 [0,2] d45 b1
  have b2 : a 46 ≠ 0 := exclude [2] (fun u v => edge r68 v u) (a 46) (a 18) 0 d18 c68 (by decide +kernel)
  have t2 : a 46 ∈ [1] := remove (a 46) 0 [0,1] d46 b2
  have b3 : a 49 ≠ 0 := exclude [1] (fun u v => edge r77 v u) (a 49) (a 21) 0 t0 c77 (by decide +kernel)
  have t3 : a 49 ∈ [1] := remove (a 49) 0 [0,1] d49 b3
  have b4 : a 27 ≠ 0 := exclude [1] (fun u v => edge r86 v u) (a 27) (a 26) 0 d26 c86 (by decide +kernel)
  have t4 : a 27 ∈ [1] := remove (a 27) 0 [0,1] d27 b4
  have b5 : a 55 ≠ 0 := exclude [1] (fun u v => edge r89 v u) (a 55) (a 27) 0 t4 c89 (by decide +kernel)
  have t5 : a 55 ∈ [2] := remove (a 55) 0 [0,2] d55 b5
  have b6 : a 29 ≠ 0 := exclude [1] (edge r91) (a 29) (a 31) 0 d31 c91 (by decide +kernel)
  have t6 : a 29 ∈ [1] := remove (a 29) 0 [0,1] d29 b6
  have b7 : a 35 ≠ 0 := exclude [1] (fun u v => edge r100 v u) (a 35) (a 31) 0 d31 c100 (by decide +kernel)
  have t7 : a 35 ∈ [1] := remove (a 35) 0 [0,1] d35 b7
  have b8 : a 41 ≠ 0 := exclude [2] (fun u v => edge r122 v u) (a 41) (a 40) 0 d40 c122 (by decide +kernel)
  have t8 : a 41 ∈ [1] := remove (a 41) 0 [0,1] d41 b8
  have b9 : a 44 ≠ 0 := exclude [1] (edge r129) (a 44) (a 46) 0 t2 c129 (by decide +kernel)
  have t9 : a 44 ∈ [1] := remove (a 44) 0 [0,1] d44 b9
  have b10 : a 48 ≠ 0 := exclude [1] (fun u v => edge r130 v u) (a 48) (a 44) 0 t9 c130 (by decide +kernel)
  have t10 : a 48 ∈ [1] := remove (a 48) 0 [0,1] d48 b10
  have b11 : a 51 ≠ 0 := exclude [1] (fun u v => edge r131 v u) (a 51) (a 44) 0 t9 c131 (by decide +kernel)
  have t11 : a 51 ∈ [2] := remove (a 51) 0 [0,2] d51 b11
  have b12 : a 50 ≠ 0 := exclude [1] (fun u v => edge r135 v u) (a 50) (a 46) 0 t2 c135 (by decide +kernel)
  have t12 : a 50 ∈ [1] := remove (a 50) 0 [0,1] d50 b12
  have b13 : a 53 ≠ 0 := exclude [1] (fun u v => edge r136 v u) (a 53) (a 46) 0 t2 c136 (by decide +kernel)
  have t13 : a 53 ∈ [2] := remove (a 53) 0 [0,2] d53 b13
  have b14 : a 47 ≠ 0 := exclude [1] (edge r137) (a 47) (a 48) 0 t10 c137 (by decide +kernel)
  have t14 : a 47 ∈ [2] := remove (a 47) 0 [0,2] d47 b14
  have b15 : a 56 ≠ 0 := exclude [1] (fun u v => edge r143 v u) (a 56) (a 49) 0 t3 c143 (by decide +kernel)
  have t15 : a 56 ∈ [1] := remove (a 56) 0 [0,1] d56 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk10 (a : Nat → Nat)
    (d4 : a 4 ∈ [0,2])
    (d12 : a 12 ∈ [1])
    (d7 : a 7 ∈ [0,1])
    (d14 : a 14 ∈ [1])
    (d9 : a 9 ∈ [0,1])
    (d8 : a 8 ∈ [1])
    (d24 : a 24 ∈ [0,2])
    (d37 : a 37 ∈ [0,1])
    (d16 : a 16 ∈ [0,1])
    (d15 : a 15 ∈ [2])
    (d20 : a 20 ∈ [0,2])
    (d30 : a 30 ∈ [0,1])
    (d29 : a 29 ∈ [1])
    (d34 : a 34 ∈ [0,2])
    (d5 : a 5 ∈ [0,1])
    (c20 : edge r20 (a 4) (a 5)=true)
    (c22 : edge r22 (a 4) (a 12)=true)
    (c32 : edge r32 (a 7) (a 14)=true)
    (c34 : edge r34 (a 8) (a 9)=true)
    (c40 : edge r40 (a 9) (a 24)=true)
    (c41 : edge r41 (a 9) (a 37)=true)
    (c54 : edge r54 (a 15) (a 16)=true)
    (c60 : edge r60 (a 16) (a 20)=true)
    (c90 : edge r90 (a 29) (a 30)=true)
    (c96 : edge r96 (a 30) (a 34)=true)
    : a 4 ∈ [2] ∧ a 7 ∈ [1] ∧ a 9 ∈ [1] ∧ a 24 ∈ [2] ∧ a 37 ∈ [1] ∧ a 16 ∈ [1] ∧ a 20 ∈ [2] ∧ a 30 ∈ [1] ∧ a 34 ∈ [2] ∧ a 5 ∈ [1] := by
  have b0 : a 4 ≠ 0 := exclude [1] (edge r22) (a 4) (a 12) 0 d12 c22 (by decide +kernel)
  have t0 : a 4 ∈ [2] := remove (a 4) 0 [0,2] d4 b0
  have b1 : a 7 ≠ 0 := exclude [1] (edge r32) (a 7) (a 14) 0 d14 c32 (by decide +kernel)
  have t1 : a 7 ∈ [1] := remove (a 7) 0 [0,1] d7 b1
  have b2 : a 9 ≠ 0 := exclude [1] (fun u v => edge r34 v u) (a 9) (a 8) 0 d8 c34 (by decide +kernel)
  have t2 : a 9 ∈ [1] := remove (a 9) 0 [0,1] d9 b2
  have b3 : a 24 ≠ 0 := exclude [1] (fun u v => edge r40 v u) (a 24) (a 9) 0 t2 c40 (by decide +kernel)
  have t3 : a 24 ∈ [2] := remove (a 24) 0 [0,2] d24 b3
  have b4 : a 37 ≠ 0 := exclude [1] (fun u v => edge r41 v u) (a 37) (a 9) 0 t2 c41 (by decide +kernel)
  have t4 : a 37 ∈ [1] := remove (a 37) 0 [0,1] d37 b4
  have b5 : a 16 ≠ 0 := exclude [2] (fun u v => edge r54 v u) (a 16) (a 15) 0 d15 c54 (by decide +kernel)
  have t5 : a 16 ∈ [1] := remove (a 16) 0 [0,1] d16 b5
  have b6 : a 20 ≠ 0 := exclude [1] (fun u v => edge r60 v u) (a 20) (a 16) 0 t5 c60 (by decide +kernel)
  have t6 : a 20 ∈ [2] := remove (a 20) 0 [0,2] d20 b6
  have b7 : a 30 ≠ 0 := exclude [1] (fun u v => edge r90 v u) (a 30) (a 29) 0 d29 c90 (by decide +kernel)
  have t7 : a 30 ∈ [1] := remove (a 30) 0 [0,1] d30 b7
  have b8 : a 34 ≠ 0 := exclude [1] (fun u v => edge r96 v u) (a 34) (a 30) 0 t7 c96 (by decide +kernel)
  have t8 : a 34 ∈ [2] := remove (a 34) 0 [0,2] d34 b8
  have b9 : a 5 ≠ 0 := exclude [2] (fun u v => edge r20 v u) (a 5) (a 4) 0 t0 c20 (by decide +kernel)
  have t9 : a 5 ∈ [1] := remove (a 5) 0 [0,1] d5 b9
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (t9)))))))))
#print axioms chunk8
#print axioms chunk9
#print axioms chunk10
end PartitionCover205_227
