import PartitionData205_212
namespace PartitionCover205_212
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk24 (a : Nat → Nat)
    (d7 : a 7 ∈ [0,1,2])
    (d15 : a 15 ∈ [0,6])
    (d10 : a 10 ∈ [0,1,4,5])
    (d14 : a 14 ∈ [0])
    (d18 : a 18 ∈ [0,1,6,7])
    (d16 : a 16 ∈ [0])
    (d20 : a 20 ∈ [0,1])
    (d17 : a 17 ∈ [0,6])
    (d21 : a 21 ∈ [0])
    (d19 : a 19 ∈ [0,6])
    (d22 : a 22 ∈ [0])
    (d26 : a 26 ∈ [0,2])
    (d27 : a 27 ∈ [0,1])
    (d1 : a 1 ∈ [0,1])
    (d5 : a 5 ∈ [0])
    (d2 : a 2 ∈ [0,4,8,14])
    (d6 : a 6 ∈ [0,1])
    (d3 : a 3 ∈ [0,1])
    (c6 : edge r6 (a 1) (a 5)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    (c12 : edge r12 (a 2) (a 18)=true)
    (c15 : edge r15 (a 3) (a 19)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c36 : edge r36 (a 10) (a 14)=true)
    (c49 : edge r49 (a 16) (a 18)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    (c53 : edge r53 (a 17) (a 21)=true)
    (c55 : edge r55 (a 18) (a 19)=true)
    (c56 : edge r56 (a 18) (a 22)=true)
    (c57 : edge r57 (a 18) (a 26)=true)
    (c59 : edge r59 (a 19) (a 27)=true)
    : a 7 ∈ [0,2] ∧ a 10 ∈ [0,1] ∧ a 18 ∈ [0] ∧ a 20 ∈ [0] ∧ a 17 ∈ [0] ∧ a 19 ∈ [0] ∧ a 26 ∈ [0] ∧ a 27 ∈ [0] ∧ a 1 ∈ [0] ∧ a 2 ∈ [0] ∧ a 3 ∈ [0] := by
  have b0 : a 7 ≠ 1 := exclude [0,6] (edge r26) (a 7) (a 15) 1 d15 c26 (by decide +kernel)
  have t0 : a 7 ∈ [0,2] := remove (a 7) 1 [0,1,2] d7 b0
  have b1 : a 10 ≠ 4 := exclude [0] (edge r36) (a 10) (a 14) 4 d14 c36 (by decide +kernel)
  have t1 : a 10 ∈ [0,1,5] := remove (a 10) 4 [0,1,4,5] d10 b1
  have b2 : a 10 ≠ 5 := exclude [0] (edge r36) (a 10) (a 14) 5 d14 c36 (by decide +kernel)
  have t2 : a 10 ∈ [0,1] := remove (a 10) 5 [0,1,5] t1 b2
  have b3 : a 18 ≠ 6 := exclude [0] (fun u v => edge r49 v u) (a 18) (a 16) 6 d16 c49 (by decide +kernel)
  have t3 : a 18 ∈ [0,1,7] := remove (a 18) 6 [0,1,6,7] d18 b3
  have b4 : a 18 ≠ 7 := exclude [0] (fun u v => edge r49 v u) (a 18) (a 16) 7 d16 c49 (by decide +kernel)
  have t4 : a 18 ∈ [0,1] := remove (a 18) 7 [0,1,7] t3 b4
  have b5 : a 20 ≠ 1 := exclude [0] (fun u v => edge r50 v u) (a 20) (a 16) 1 d16 c50 (by decide +kernel)
  have t5 : a 20 ∈ [0] := remove (a 20) 1 [0,1] d20 b5
  have b6 : a 17 ≠ 6 := exclude [0] (edge r53) (a 17) (a 21) 6 d21 c53 (by decide +kernel)
  have t6 : a 17 ∈ [0] := remove (a 17) 6 [0,6] d17 b6
  have b7 : a 19 ≠ 6 := exclude [0,1] (fun u v => edge r55 v u) (a 19) (a 18) 6 t4 c55 (by decide +kernel)
  have t7 : a 19 ∈ [0] := remove (a 19) 6 [0,6] d19 b7
  have b8 : a 18 ≠ 1 := exclude [0] (edge r56) (a 18) (a 22) 1 d22 c56 (by decide +kernel)
  have t8 : a 18 ∈ [0] := remove (a 18) 1 [0,1] t4 b8
  have b9 : a 26 ≠ 2 := exclude [0] (fun u v => edge r57 v u) (a 26) (a 18) 2 t8 c57 (by decide +kernel)
  have t9 : a 26 ∈ [0] := remove (a 26) 2 [0,2] d26 b9
  have b10 : a 27 ≠ 1 := exclude [0] (fun u v => edge r59 v u) (a 27) (a 19) 1 t7 c59 (by decide +kernel)
  have t10 : a 27 ∈ [0] := remove (a 27) 1 [0,1] d27 b10
  have b11 : a 1 ≠ 1 := exclude [0] (edge r6) (a 1) (a 5) 1 d5 c6 (by decide +kernel)
  have t11 : a 1 ∈ [0] := remove (a 1) 1 [0,1] d1 b11
  have b12 : a 2 ≠ 8 := exclude [0,1] (edge r10) (a 2) (a 6) 8 d6 c10 (by decide +kernel)
  have t12 : a 2 ∈ [0,4,14] := remove (a 2) 8 [0,4,8,14] d2 b12
  have b13 : a 2 ≠ 14 := exclude [0,1] (edge r10) (a 2) (a 6) 14 d6 c10 (by decide +kernel)
  have t13 : a 2 ∈ [0,4] := remove (a 2) 14 [0,4,14] t12 b13
  have b14 : a 2 ≠ 4 := exclude [0] (edge r12) (a 2) (a 18) 4 t8 c12 (by decide +kernel)
  have t14 : a 2 ∈ [0] := remove (a 2) 4 [0,4] t13 b14
  have b15 : a 3 ≠ 1 := exclude [0] (edge r15) (a 3) (a 19) 1 t7 c15 (by decide +kernel)
  have t15 : a 3 ∈ [0] := remove (a 3) 1 [0,1] d3 b15
  exact And.intro t0 (And.intro t2 (And.intro t8 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t14 (t15))))))))))

theorem chunk25 (a : Nat → Nat)
    (d7 : a 7 ∈ [0,2])
    (d5 : a 5 ∈ [0])
    (d15 : a 15 ∈ [0,6])
    (d10 : a 10 ∈ [0,1])
    (d26 : a 26 ∈ [0])
    (d11 : a 11 ∈ [0,12])
    (d6 : a 6 ∈ [0,1])
    (d2 : a 2 ∈ [0])
    (d9 : a 9 ∈ [0,6])
    (c10 : edge r10 (a 2) (a 6)=true)
    (c20 : edge r20 (a 5) (a 7)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    : a 7 ∈ [0] ∧ a 15 ∈ [0] ∧ a 10 ∈ [0] ∧ a 11 ∈ [0] ∧ a 6 ∈ [0] ∧ a 9 ∈ [0] := by
  have b0 : a 7 ≠ 2 := exclude [0] (fun u v => edge r20 v u) (a 7) (a 5) 2 d5 c20 (by decide +kernel)
  have t0 : a 7 ∈ [0] := remove (a 7) 2 [0,2] d7 b0
  have b1 : a 15 ≠ 6 := exclude [0] (fun u v => edge r26 v u) (a 15) (a 7) 6 t0 c26 (by decide +kernel)
  have t1 : a 15 ∈ [0] := remove (a 15) 6 [0,6] d15 b1
  have b2 : a 10 ≠ 1 := exclude [0] (edge r37) (a 10) (a 26) 1 d26 c37 (by decide +kernel)
  have t2 : a 10 ∈ [0] := remove (a 10) 1 [0,1] d10 b2
  have b3 : a 11 ≠ 12 := exclude [0] (edge r38) (a 11) (a 15) 12 t1 c38 (by decide +kernel)
  have t3 : a 11 ∈ [0] := remove (a 11) 12 [0,12] d11 b3
  have b4 : a 6 ≠ 1 := exclude [0] (fun u v => edge r10 v u) (a 6) (a 2) 1 d2 c10 (by decide +kernel)
  have t4 : a 6 ∈ [0] := remove (a 6) 1 [0,1] d6 b4
  have b5 : a 9 ≠ 6 := exclude [0] (edge r32) (a 9) (a 11) 6 t3 c32 (by decide +kernel)
  have t5 : a 9 ∈ [0] := remove (a 9) 6 [0,6] d9 b5
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (t5)))))
#print axioms chunk24
#print axioms chunk25
end PartitionCover205_212
