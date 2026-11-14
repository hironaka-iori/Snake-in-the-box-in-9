import PartitionData205_244
namespace PartitionCover205_244
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d31 : a 31 ∈ [0,1])
    (d23 : a 23 ∈ [0])
    (d55 : a 55 ∈ [0,1])
    (d25 : a 25 ∈ [0,1])
    (d24 : a 24 ∈ [0])
    (d56 : a 56 ∈ [0,1,2,3])
    (d27 : a 27 ∈ [0,1])
    (d30 : a 30 ∈ [0,1])
    (d26 : a 26 ∈ [0])
    (d58 : a 58 ∈ [0,1])
    (d62 : a 62 ∈ [0,1,2,3])
    (d63 : a 63 ∈ [0,1,2,3])
    (d40 : a 40 ∈ [0,1])
    (d32 : a 32 ∈ [0])
    (d37 : a 37 ∈ [0,1])
    (d33 : a 33 ∈ [0])
    (d43 : a 43 ∈ [0,1])
    (d35 : a 35 ∈ [0])
    (c90 : edge r90 (a 23) (a 31)=true)
    (c91 : edge r91 (a 23) (a 55)=true)
    (c92 : edge r92 (a 24) (a 25)=true)
    (c95 : edge r95 (a 24) (a 56)=true)
    (c96 : edge r96 (a 25) (a 27)=true)
    (c100 : edge r100 (a 26) (a 30)=true)
    (c101 : edge r101 (a 26) (a 58)=true)
    (c110 : edge r110 (a 30) (a 62)=true)
    (c111 : edge r111 (a 31) (a 63)=true)
    (c115 : edge r115 (a 32) (a 40)=true)
    (c118 : edge r118 (a 33) (a 37)=true)
    (c126 : edge r126 (a 35) (a 43)=true)
    : a 31 ∈ [0] ∧ a 55 ∈ [0] ∧ a 25 ∈ [0] ∧ a 56 ∈ [0] ∧ a 27 ∈ [0] ∧ a 30 ∈ [0] ∧ a 58 ∈ [0] ∧ a 62 ∈ [0,1] ∧ a 63 ∈ [0,1] ∧ a 40 ∈ [0] ∧ a 37 ∈ [0] ∧ a 43 ∈ [0] := by
  have b0 : a 31 ≠ 1 := exclude [0] (fun u v => edge r90 v u) (a 31) (a 23) 1 d23 c90 (by decide +kernel)
  have t0 : a 31 ∈ [0] := remove (a 31) 1 [0,1] d31 b0
  have b1 : a 55 ≠ 1 := exclude [0] (fun u v => edge r91 v u) (a 55) (a 23) 1 d23 c91 (by decide +kernel)
  have t1 : a 55 ∈ [0] := remove (a 55) 1 [0,1] d55 b1
  have b2 : a 25 ≠ 1 := exclude [0] (fun u v => edge r92 v u) (a 25) (a 24) 1 d24 c92 (by decide +kernel)
  have t2 : a 25 ∈ [0] := remove (a 25) 1 [0,1] d25 b2
  have b3 : a 56 ≠ 1 := exclude [0] (fun u v => edge r95 v u) (a 56) (a 24) 1 d24 c95 (by decide +kernel)
  have t3 : a 56 ∈ [0,2,3] := remove (a 56) 1 [0,1,2,3] d56 b3
  have b4 : a 56 ≠ 2 := exclude [0] (fun u v => edge r95 v u) (a 56) (a 24) 2 d24 c95 (by decide +kernel)
  have t4 : a 56 ∈ [0,3] := remove (a 56) 2 [0,2,3] t3 b4
  have b5 : a 56 ≠ 3 := exclude [0] (fun u v => edge r95 v u) (a 56) (a 24) 3 d24 c95 (by decide +kernel)
  have t5 : a 56 ∈ [0] := remove (a 56) 3 [0,3] t4 b5
  have b6 : a 27 ≠ 1 := exclude [0] (fun u v => edge r96 v u) (a 27) (a 25) 1 t2 c96 (by decide +kernel)
  have t6 : a 27 ∈ [0] := remove (a 27) 1 [0,1] d27 b6
  have b7 : a 30 ≠ 1 := exclude [0] (fun u v => edge r100 v u) (a 30) (a 26) 1 d26 c100 (by decide +kernel)
  have t7 : a 30 ∈ [0] := remove (a 30) 1 [0,1] d30 b7
  have b8 : a 58 ≠ 1 := exclude [0] (fun u v => edge r101 v u) (a 58) (a 26) 1 d26 c101 (by decide +kernel)
  have t8 : a 58 ∈ [0] := remove (a 58) 1 [0,1] d58 b8
  have b9 : a 62 ≠ 2 := exclude [0] (fun u v => edge r110 v u) (a 62) (a 30) 2 t7 c110 (by decide +kernel)
  have t9 : a 62 ∈ [0,1,3] := remove (a 62) 2 [0,1,2,3] d62 b9
  have b10 : a 62 ≠ 3 := exclude [0] (fun u v => edge r110 v u) (a 62) (a 30) 3 t7 c110 (by decide +kernel)
  have t10 : a 62 ∈ [0,1] := remove (a 62) 3 [0,1,3] t9 b10
  have b11 : a 63 ≠ 2 := exclude [0] (fun u v => edge r111 v u) (a 63) (a 31) 2 t0 c111 (by decide +kernel)
  have t11 : a 63 ∈ [0,1,3] := remove (a 63) 2 [0,1,2,3] d63 b11
  have b12 : a 63 ≠ 3 := exclude [0] (fun u v => edge r111 v u) (a 63) (a 31) 3 t0 c111 (by decide +kernel)
  have t12 : a 63 ∈ [0,1] := remove (a 63) 3 [0,1,3] t11 b12
  have b13 : a 40 ≠ 1 := exclude [0] (fun u v => edge r115 v u) (a 40) (a 32) 1 d32 c115 (by decide +kernel)
  have t13 : a 40 ∈ [0] := remove (a 40) 1 [0,1] d40 b13
  have b14 : a 37 ≠ 1 := exclude [0] (fun u v => edge r118 v u) (a 37) (a 33) 1 d33 c118 (by decide +kernel)
  have t14 : a 37 ∈ [0] := remove (a 37) 1 [0,1] d37 b14
  have b15 : a 43 ≠ 1 := exclude [0] (fun u v => edge r126 v u) (a 43) (a 35) 1 d35 c126 (by decide +kernel)
  have t15 : a 43 ∈ [0] := remove (a 43) 1 [0,1] d43 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t10 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))

theorem chunk5 (a : Nat → Nat)
    (d51 : a 51 ∈ [0,1])
    (d35 : a 35 ∈ [0])
    (d53 : a 53 ∈ [0,1])
    (d37 : a 37 ∈ [0])
    (d46 : a 46 ∈ [0,1])
    (d38 : a 38 ∈ [0])
    (d54 : a 54 ∈ [0,1])
    (d41 : a 41 ∈ [0,1])
    (d40 : a 40 ∈ [0])
    (d62 : a 62 ∈ [0,1])
    (d63 : a 63 ∈ [0,1])
    (d47 : a 47 ∈ [0])
    (d49 : a 49 ∈ [0,1])
    (d48 : a 48 ∈ [0])
    (d52 : a 52 ∈ [0,1])
    (d61 : a 61 ∈ [0,1])
    (d57 : a 57 ∈ [0,1])
    (d56 : a 56 ∈ [0])
    (d60 : a 60 ∈ [0,1])
    (d59 : a 59 ∈ [0,1])
    (c127 : edge r127 (a 35) (a 51)=true)
    (c134 : edge r134 (a 37) (a 53)=true)
    (c136 : edge r136 (a 38) (a 46)=true)
    (c137 : edge r137 (a 38) (a 54)=true)
    (c140 : edge r140 (a 40) (a 41)=true)
    (c158 : edge r158 (a 46) (a 62)=true)
    (c159 : edge r159 (a 47) (a 63)=true)
    (c160 : edge r160 (a 48) (a 49)=true)
    (c162 : edge r162 (a 48) (a 52)=true)
    (c176 : edge r176 (a 53) (a 61)=true)
    (c180 : edge r180 (a 56) (a 57)=true)
    (c182 : edge r182 (a 56) (a 60)=true)
    (c183 : edge r183 (a 57) (a 59)=true)
    : a 51 ∈ [0] ∧ a 53 ∈ [0] ∧ a 46 ∈ [0] ∧ a 54 ∈ [0] ∧ a 41 ∈ [0] ∧ a 62 ∈ [0] ∧ a 63 ∈ [0] ∧ a 49 ∈ [0] ∧ a 52 ∈ [0] ∧ a 61 ∈ [0] ∧ a 57 ∈ [0] ∧ a 60 ∈ [0] ∧ a 59 ∈ [0] := by
  have b0 : a 51 ≠ 1 := exclude [0] (fun u v => edge r127 v u) (a 51) (a 35) 1 d35 c127 (by decide +kernel)
  have t0 : a 51 ∈ [0] := remove (a 51) 1 [0,1] d51 b0
  have b1 : a 53 ≠ 1 := exclude [0] (fun u v => edge r134 v u) (a 53) (a 37) 1 d37 c134 (by decide +kernel)
  have t1 : a 53 ∈ [0] := remove (a 53) 1 [0,1] d53 b1
  have b2 : a 46 ≠ 1 := exclude [0] (fun u v => edge r136 v u) (a 46) (a 38) 1 d38 c136 (by decide +kernel)
  have t2 : a 46 ∈ [0] := remove (a 46) 1 [0,1] d46 b2
  have b3 : a 54 ≠ 1 := exclude [0] (fun u v => edge r137 v u) (a 54) (a 38) 1 d38 c137 (by decide +kernel)
  have t3 : a 54 ∈ [0] := remove (a 54) 1 [0,1] d54 b3
  have b4 : a 41 ≠ 1 := exclude [0] (fun u v => edge r140 v u) (a 41) (a 40) 1 d40 c140 (by decide +kernel)
  have t4 : a 41 ∈ [0] := remove (a 41) 1 [0,1] d41 b4
  have b5 : a 62 ≠ 1 := exclude [0] (fun u v => edge r158 v u) (a 62) (a 46) 1 t2 c158 (by decide +kernel)
  have t5 : a 62 ∈ [0] := remove (a 62) 1 [0,1] d62 b5
  have b6 : a 63 ≠ 1 := exclude [0] (fun u v => edge r159 v u) (a 63) (a 47) 1 d47 c159 (by decide +kernel)
  have t6 : a 63 ∈ [0] := remove (a 63) 1 [0,1] d63 b6
  have b7 : a 49 ≠ 1 := exclude [0] (fun u v => edge r160 v u) (a 49) (a 48) 1 d48 c160 (by decide +kernel)
  have t7 : a 49 ∈ [0] := remove (a 49) 1 [0,1] d49 b7
  have b8 : a 52 ≠ 1 := exclude [0] (fun u v => edge r162 v u) (a 52) (a 48) 1 d48 c162 (by decide +kernel)
  have t8 : a 52 ∈ [0] := remove (a 52) 1 [0,1] d52 b8
  have b9 : a 61 ≠ 1 := exclude [0] (fun u v => edge r176 v u) (a 61) (a 53) 1 t1 c176 (by decide +kernel)
  have t9 : a 61 ∈ [0] := remove (a 61) 1 [0,1] d61 b9
  have b10 : a 57 ≠ 1 := exclude [0] (fun u v => edge r180 v u) (a 57) (a 56) 1 d56 c180 (by decide +kernel)
  have t10 : a 57 ∈ [0] := remove (a 57) 1 [0,1] d57 b10
  have b11 : a 60 ≠ 1 := exclude [0] (fun u v => edge r182 v u) (a 60) (a 56) 1 d56 c182 (by decide +kernel)
  have t11 : a 60 ∈ [0] := remove (a 60) 1 [0,1] d60 b11
  have b12 : a 59 ≠ 1 := exclude [0] (fun u v => edge r183 v u) (a 59) (a 57) 1 t10 c183 (by decide +kernel)
  have t12 : a 59 ∈ [0] := remove (a 59) 1 [0,1] d59 b12
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (t12))))))))))))
#print axioms chunk4
#print axioms chunk5
end PartitionCover205_244
