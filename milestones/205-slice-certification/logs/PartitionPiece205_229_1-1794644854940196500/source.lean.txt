import PartitionData205_229
namespace PartitionCover205_229
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d23 : a 23 ∈ [0,2])
    (d22 : a 22 ∈ [0])
    (d25 : a 25 ∈ [0,2])
    (d53 : a 53 ∈ [0,1])
    (d31 : a 31 ∈ [0,1])
    (d38 : a 38 ∈ [0])
    (d39 : a 39 ∈ [0,1])
    (d46 : a 46 ∈ [0,1])
    (d47 : a 47 ∈ [0,1])
    (d54 : a 54 ∈ [0])
    (d55 : a 55 ∈ [0,2])
    (d9 : a 9 ∈ [0,1])
    (d8 : a 8 ∈ [0])
    (d37 : a 37 ∈ [0,1])
    (d15 : a 15 ∈ [0,1])
    (d14 : a 14 ∈ [0])
    (d29 : a 29 ∈ [0,1])
    (d30 : a 30 ∈ [0,1])
    (d34 : a 34 ∈ [0,2])
    (d50 : a 50 ∈ [0,1])
    (d48 : a 48 ∈ [0,1])
    (c33 : edge r33 (a 8) (a 9)=true)
    (c39 : edge r39 (a 9) (a 37)=true)
    (c50 : edge r50 (a 14) (a 15)=true)
    (c77 : edge r77 (a 22) (a 23)=true)
    (c80 : edge r80 (a 23) (a 25)=true)
    (c86 : edge r86 (a 25) (a 53)=true)
    (c93 : edge r93 (a 29) (a 31)=true)
    (c98 : edge r98 (a 30) (a 37)=true)
    (c100 : edge r100 (a 31) (a 34)=true)
    (c101 : edge r101 (a 31) (a 38)=true)
    (c120 : edge r120 (a 38) (a 39)=true)
    (c138 : edge r138 (a 46) (a 50)=true)
    (c139 : edge r139 (a 46) (a 53)=true)
    (c140 : edge r140 (a 47) (a 48)=true)
    (c142 : edge r142 (a 47) (a 54)=true)
    (c153 : edge r153 (a 54) (a 55)=true)
    : a 23 ∈ [0] ∧ a 25 ∈ [0] ∧ a 53 ∈ [0] ∧ a 31 ∈ [0] ∧ a 39 ∈ [0] ∧ a 46 ∈ [0] ∧ a 47 ∈ [0] ∧ a 55 ∈ [0] ∧ a 9 ∈ [0] ∧ a 37 ∈ [0] ∧ a 15 ∈ [0] ∧ a 29 ∈ [0] ∧ a 30 ∈ [0] ∧ a 34 ∈ [0] ∧ a 50 ∈ [0] ∧ a 48 ∈ [0] := by
  have b0 : a 23 ≠ 2 := exclude [0] (fun u v => edge r77 v u) (a 23) (a 22) 2 d22 c77 (by decide +kernel)
  have t0 : a 23 ∈ [0] := remove (a 23) 2 [0,2] d23 b0
  have b1 : a 25 ≠ 2 := exclude [0] (fun u v => edge r80 v u) (a 25) (a 23) 2 t0 c80 (by decide +kernel)
  have t1 : a 25 ∈ [0] := remove (a 25) 2 [0,2] d25 b1
  have b2 : a 53 ≠ 1 := exclude [0] (fun u v => edge r86 v u) (a 53) (a 25) 1 t1 c86 (by decide +kernel)
  have t2 : a 53 ∈ [0] := remove (a 53) 1 [0,1] d53 b2
  have b3 : a 31 ≠ 1 := exclude [0] (edge r101) (a 31) (a 38) 1 d38 c101 (by decide +kernel)
  have t3 : a 31 ∈ [0] := remove (a 31) 1 [0,1] d31 b3
  have b4 : a 39 ≠ 1 := exclude [0] (fun u v => edge r120 v u) (a 39) (a 38) 1 d38 c120 (by decide +kernel)
  have t4 : a 39 ∈ [0] := remove (a 39) 1 [0,1] d39 b4
  have b5 : a 46 ≠ 1 := exclude [0] (edge r139) (a 46) (a 53) 1 t2 c139 (by decide +kernel)
  have t5 : a 46 ∈ [0] := remove (a 46) 1 [0,1] d46 b5
  have b6 : a 47 ≠ 1 := exclude [0] (edge r142) (a 47) (a 54) 1 d54 c142 (by decide +kernel)
  have t6 : a 47 ∈ [0] := remove (a 47) 1 [0,1] d47 b6
  have b7 : a 55 ≠ 2 := exclude [0] (fun u v => edge r153 v u) (a 55) (a 54) 2 d54 c153 (by decide +kernel)
  have t7 : a 55 ∈ [0] := remove (a 55) 2 [0,2] d55 b7
  have b8 : a 9 ≠ 1 := exclude [0] (fun u v => edge r33 v u) (a 9) (a 8) 1 d8 c33 (by decide +kernel)
  have t8 : a 9 ∈ [0] := remove (a 9) 1 [0,1] d9 b8
  have b9 : a 37 ≠ 1 := exclude [0] (fun u v => edge r39 v u) (a 37) (a 9) 1 t8 c39 (by decide +kernel)
  have t9 : a 37 ∈ [0] := remove (a 37) 1 [0,1] d37 b9
  have b10 : a 15 ≠ 1 := exclude [0] (fun u v => edge r50 v u) (a 15) (a 14) 1 d14 c50 (by decide +kernel)
  have t10 : a 15 ∈ [0] := remove (a 15) 1 [0,1] d15 b10
  have b11 : a 29 ≠ 1 := exclude [0] (edge r93) (a 29) (a 31) 1 t3 c93 (by decide +kernel)
  have t11 : a 29 ∈ [0] := remove (a 29) 1 [0,1] d29 b11
  have b12 : a 30 ≠ 1 := exclude [0] (edge r98) (a 30) (a 37) 1 t9 c98 (by decide +kernel)
  have t12 : a 30 ∈ [0] := remove (a 30) 1 [0,1] d30 b12
  have b13 : a 34 ≠ 2 := exclude [0] (fun u v => edge r100 v u) (a 34) (a 31) 2 t3 c100 (by decide +kernel)
  have t13 : a 34 ∈ [0] := remove (a 34) 2 [0,2] d34 b13
  have b14 : a 50 ≠ 1 := exclude [0] (fun u v => edge r138 v u) (a 50) (a 46) 1 t5 c138 (by decide +kernel)
  have t14 : a 50 ∈ [0] := remove (a 50) 1 [0,1] d50 b14
  have b15 : a 48 ≠ 1 := exclude [0] (fun u v => edge r140 v u) (a 48) (a 47) 1 t6 c140 (by decide +kernel)
  have t15 : a 48 ∈ [0] := remove (a 48) 1 [0,1] d48 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk5 (a : Nat → Nat)
    (d7 : a 7 ∈ [0,1])
    (d3 : a 3 ∈ [1])
    (d5 : a 5 ∈ [0,1])
    (d13 : a 13 ∈ [0,2])
    (d12 : a 12 ∈ [0,1])
    (d27 : a 27 ∈ [0,1])
    (d20 : a 20 ∈ [0,1])
    (d56 : a 56 ∈ [0,2])
    (d54 : a 54 ∈ [0,2])
    (d4 : a 4 ∈ [0,1])
    (d11 : a 11 ∈ [0,1])
    (d8 : a 8 ∈ [0,1])
    (d22 : a 22 ∈ [0,2])
    (d10 : a 10 ∈ [0,2])
    (d38 : a 38 ∈ [0,2])
    (d14 : a 14 ∈ [0,1])
    (d16 : a 16 ∈ [0,1])
    (c16 : edge r16 (a 3) (a 7)=true)
    (c18 : edge r18 (a 4) (a 5)=true)
    (c20 : edge r20 (a 4) (a 11)=true)
    (c23 : edge r23 (a 5) (a 7)=true)
    (c30 : edge r30 (a 7) (a 13)=true)
    (c35 : edge r35 (a 8) (a 11)=true)
    (c36 : edge r36 (a 8) (a 22)=true)
    (c40 : edge r40 (a 10) (a 12)=true)
    (c42 : edge r42 (a 10) (a 38)=true)
    (c46 : edge r46 (a 12) (a 13)=true)
    (c47 : edge r47 (a 12) (a 27)=true)
    (c53 : edge r53 (a 14) (a 22)=true)
    (c60 : edge r60 (a 16) (a 20)=true)
    (c73 : edge r73 (a 20) (a 27)=true)
    (c90 : edge r90 (a 27) (a 56)=true)
    (c154 : edge r154 (a 54) (a 56)=true)
    : a 7 ∈ [1] ∧ a 5 ∈ [1] ∧ a 13 ∈ [2] ∧ a 12 ∈ [1] ∧ a 27 ∈ [1] ∧ a 20 ∈ [1] ∧ a 56 ∈ [2] ∧ a 54 ∈ [2] ∧ a 4 ∈ [1] ∧ a 11 ∈ [1] ∧ a 8 ∈ [1] ∧ a 22 ∈ [2] ∧ a 10 ∈ [2] ∧ a 38 ∈ [2] ∧ a 14 ∈ [1] ∧ a 16 ∈ [1] := by
  have b0 : a 7 ≠ 0 := exclude [1] (fun u v => edge r16 v u) (a 7) (a 3) 0 d3 c16 (by decide +kernel)
  have t0 : a 7 ∈ [1] := remove (a 7) 0 [0,1] d7 b0
  have b1 : a 5 ≠ 0 := exclude [1] (edge r23) (a 5) (a 7) 0 t0 c23 (by decide +kernel)
  have t1 : a 5 ∈ [1] := remove (a 5) 0 [0,1] d5 b1
  have b2 : a 13 ≠ 0 := exclude [1] (fun u v => edge r30 v u) (a 13) (a 7) 0 t0 c30 (by decide +kernel)
  have t2 : a 13 ∈ [2] := remove (a 13) 0 [0,2] d13 b2
  have b3 : a 12 ≠ 0 := exclude [2] (edge r46) (a 12) (a 13) 0 t2 c46 (by decide +kernel)
  have t3 : a 12 ∈ [1] := remove (a 12) 0 [0,1] d12 b3
  have b4 : a 27 ≠ 0 := exclude [1] (fun u v => edge r47 v u) (a 27) (a 12) 0 t3 c47 (by decide +kernel)
  have t4 : a 27 ∈ [1] := remove (a 27) 0 [0,1] d27 b4
  have b5 : a 20 ≠ 0 := exclude [1] (edge r73) (a 20) (a 27) 0 t4 c73 (by decide +kernel)
  have t5 : a 20 ∈ [1] := remove (a 20) 0 [0,1] d20 b5
  have b6 : a 56 ≠ 0 := exclude [1] (fun u v => edge r90 v u) (a 56) (a 27) 0 t4 c90 (by decide +kernel)
  have t6 : a 56 ∈ [2] := remove (a 56) 0 [0,2] d56 b6
  have b7 : a 54 ≠ 0 := exclude [2] (edge r154) (a 54) (a 56) 0 t6 c154 (by decide +kernel)
  have t7 : a 54 ∈ [2] := remove (a 54) 0 [0,2] d54 b7
  have b8 : a 4 ≠ 0 := exclude [1] (edge r18) (a 4) (a 5) 0 t1 c18 (by decide +kernel)
  have t8 : a 4 ∈ [1] := remove (a 4) 0 [0,1] d4 b8
  have b9 : a 11 ≠ 0 := exclude [1] (fun u v => edge r20 v u) (a 11) (a 4) 0 t8 c20 (by decide +kernel)
  have t9 : a 11 ∈ [1] := remove (a 11) 0 [0,1] d11 b9
  have b10 : a 8 ≠ 0 := exclude [1] (edge r35) (a 8) (a 11) 0 t9 c35 (by decide +kernel)
  have t10 : a 8 ∈ [1] := remove (a 8) 0 [0,1] d8 b10
  have b11 : a 22 ≠ 0 := exclude [1] (fun u v => edge r36 v u) (a 22) (a 8) 0 t10 c36 (by decide +kernel)
  have t11 : a 22 ∈ [2] := remove (a 22) 0 [0,2] d22 b11
  have b12 : a 10 ≠ 0 := exclude [1] (edge r40) (a 10) (a 12) 0 t3 c40 (by decide +kernel)
  have t12 : a 10 ∈ [2] := remove (a 10) 0 [0,2] d10 b12
  have b13 : a 38 ≠ 0 := exclude [2] (fun u v => edge r42 v u) (a 38) (a 10) 0 t12 c42 (by decide +kernel)
  have t13 : a 38 ∈ [2] := remove (a 38) 0 [0,2] d38 b13
  have b14 : a 14 ≠ 0 := exclude [2] (edge r53) (a 14) (a 22) 0 t11 c53 (by decide +kernel)
  have t14 : a 14 ∈ [1] := remove (a 14) 0 [0,1] d14 b14
  have b15 : a 16 ≠ 0 := exclude [1] (edge r60) (a 16) (a 20) 0 t5 c60 (by decide +kernel)
  have t15 : a 16 ∈ [1] := remove (a 16) 0 [0,1] d16 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk6 (a : Nat → Nat)
    (d23 : a 23 ∈ [0,2])
    (d22 : a 22 ∈ [2])
    (d25 : a 25 ∈ [0,2])
    (d53 : a 53 ∈ [0,1])
    (d31 : a 31 ∈ [0,1])
    (d38 : a 38 ∈ [2])
    (d39 : a 39 ∈ [0,1])
    (d46 : a 46 ∈ [0,1])
    (d47 : a 47 ∈ [0,1])
    (d54 : a 54 ∈ [2])
    (d55 : a 55 ∈ [0,2])
    (d9 : a 9 ∈ [0,1])
    (d8 : a 8 ∈ [1])
    (d37 : a 37 ∈ [0,1])
    (d15 : a 15 ∈ [0,1])
    (d14 : a 14 ∈ [1])
    (d29 : a 29 ∈ [0,1])
    (d30 : a 30 ∈ [0,1])
    (d34 : a 34 ∈ [0,2])
    (d50 : a 50 ∈ [0,1])
    (d48 : a 48 ∈ [0,1])
    (c33 : edge r33 (a 8) (a 9)=true)
    (c39 : edge r39 (a 9) (a 37)=true)
    (c50 : edge r50 (a 14) (a 15)=true)
    (c77 : edge r77 (a 22) (a 23)=true)
    (c80 : edge r80 (a 23) (a 25)=true)
    (c86 : edge r86 (a 25) (a 53)=true)
    (c93 : edge r93 (a 29) (a 31)=true)
    (c98 : edge r98 (a 30) (a 37)=true)
    (c100 : edge r100 (a 31) (a 34)=true)
    (c101 : edge r101 (a 31) (a 38)=true)
    (c120 : edge r120 (a 38) (a 39)=true)
    (c138 : edge r138 (a 46) (a 50)=true)
    (c139 : edge r139 (a 46) (a 53)=true)
    (c140 : edge r140 (a 47) (a 48)=true)
    (c142 : edge r142 (a 47) (a 54)=true)
    (c153 : edge r153 (a 54) (a 55)=true)
    : a 23 ∈ [2] ∧ a 25 ∈ [2] ∧ a 53 ∈ [1] ∧ a 31 ∈ [1] ∧ a 39 ∈ [1] ∧ a 46 ∈ [1] ∧ a 47 ∈ [1] ∧ a 55 ∈ [2] ∧ a 9 ∈ [1] ∧ a 37 ∈ [1] ∧ a 15 ∈ [1] ∧ a 29 ∈ [1] ∧ a 30 ∈ [1] ∧ a 34 ∈ [2] ∧ a 50 ∈ [1] ∧ a 48 ∈ [1] := by
  have b0 : a 23 ≠ 0 := exclude [2] (fun u v => edge r77 v u) (a 23) (a 22) 0 d22 c77 (by decide +kernel)
  have t0 : a 23 ∈ [2] := remove (a 23) 0 [0,2] d23 b0
  have b1 : a 25 ≠ 0 := exclude [2] (fun u v => edge r80 v u) (a 25) (a 23) 0 t0 c80 (by decide +kernel)
  have t1 : a 25 ∈ [2] := remove (a 25) 0 [0,2] d25 b1
  have b2 : a 53 ≠ 0 := exclude [2] (fun u v => edge r86 v u) (a 53) (a 25) 0 t1 c86 (by decide +kernel)
  have t2 : a 53 ∈ [1] := remove (a 53) 0 [0,1] d53 b2
  have b3 : a 31 ≠ 0 := exclude [2] (edge r101) (a 31) (a 38) 0 d38 c101 (by decide +kernel)
  have t3 : a 31 ∈ [1] := remove (a 31) 0 [0,1] d31 b3
  have b4 : a 39 ≠ 0 := exclude [2] (fun u v => edge r120 v u) (a 39) (a 38) 0 d38 c120 (by decide +kernel)
  have t4 : a 39 ∈ [1] := remove (a 39) 0 [0,1] d39 b4
  have b5 : a 46 ≠ 0 := exclude [1] (edge r139) (a 46) (a 53) 0 t2 c139 (by decide +kernel)
  have t5 : a 46 ∈ [1] := remove (a 46) 0 [0,1] d46 b5
  have b6 : a 47 ≠ 0 := exclude [2] (edge r142) (a 47) (a 54) 0 d54 c142 (by decide +kernel)
  have t6 : a 47 ∈ [1] := remove (a 47) 0 [0,1] d47 b6
  have b7 : a 55 ≠ 0 := exclude [2] (fun u v => edge r153 v u) (a 55) (a 54) 0 d54 c153 (by decide +kernel)
  have t7 : a 55 ∈ [2] := remove (a 55) 0 [0,2] d55 b7
  have b8 : a 9 ≠ 0 := exclude [1] (fun u v => edge r33 v u) (a 9) (a 8) 0 d8 c33 (by decide +kernel)
  have t8 : a 9 ∈ [1] := remove (a 9) 0 [0,1] d9 b8
  have b9 : a 37 ≠ 0 := exclude [1] (fun u v => edge r39 v u) (a 37) (a 9) 0 t8 c39 (by decide +kernel)
  have t9 : a 37 ∈ [1] := remove (a 37) 0 [0,1] d37 b9
  have b10 : a 15 ≠ 0 := exclude [1] (fun u v => edge r50 v u) (a 15) (a 14) 0 d14 c50 (by decide +kernel)
  have t10 : a 15 ∈ [1] := remove (a 15) 0 [0,1] d15 b10
  have b11 : a 29 ≠ 0 := exclude [1] (edge r93) (a 29) (a 31) 0 t3 c93 (by decide +kernel)
  have t11 : a 29 ∈ [1] := remove (a 29) 0 [0,1] d29 b11
  have b12 : a 30 ≠ 0 := exclude [1] (edge r98) (a 30) (a 37) 0 t9 c98 (by decide +kernel)
  have t12 : a 30 ∈ [1] := remove (a 30) 0 [0,1] d30 b12
  have b13 : a 34 ≠ 0 := exclude [1] (fun u v => edge r100 v u) (a 34) (a 31) 0 t3 c100 (by decide +kernel)
  have t13 : a 34 ∈ [2] := remove (a 34) 0 [0,2] d34 b13
  have b14 : a 50 ≠ 0 := exclude [1] (fun u v => edge r138 v u) (a 50) (a 46) 0 t5 c138 (by decide +kernel)
  have t14 : a 50 ∈ [1] := remove (a 50) 0 [0,1] d50 b14
  have b15 : a 48 ≠ 0 := exclude [1] (fun u v => edge r140 v u) (a 48) (a 47) 0 t6 c140 (by decide +kernel)
  have t15 : a 48 ∈ [1] := remove (a 48) 0 [0,1] d48 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))
#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
end PartitionCover205_229
