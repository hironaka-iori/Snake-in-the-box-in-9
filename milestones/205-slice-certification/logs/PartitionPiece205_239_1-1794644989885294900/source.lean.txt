import PartitionData205_239
namespace PartitionCover205_239
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d24 : a 24 ∈ [0,2])
    (d23 : a 23 ∈ [0])
    (d55 : a 55 ∈ [0,1])
    (d56 : a 56 ∈ [0,1])
    (d57 : a 57 ∈ [0,1])
    (d25 : a 25 ∈ [0])
    (d58 : a 58 ∈ [0,1])
    (d26 : a 26 ∈ [0])
    (d59 : a 59 ∈ [0,1])
    (d27 : a 27 ∈ [0])
    (d60 : a 60 ∈ [0,1,2,3])
    (d28 : a 28 ∈ [0])
    (d39 : a 39 ∈ [0,1])
    (d31 : a 31 ∈ [0])
    (d34 : a 34 ∈ [0,1])
    (d33 : a 33 ∈ [0])
    (d49 : a 49 ∈ [0,1])
    (d38 : a 38 ∈ [0,1])
    (d44 : a 44 ∈ [0,1])
    (d36 : a 36 ∈ [0])
    (d40 : a 40 ∈ [0,1])
    (d46 : a 46 ∈ [0,1])
    (d42 : a 42 ∈ [0])
    (c86 : edge r86 (a 23) (a 24)=true)
    (c89 : edge r89 (a 23) (a 55)=true)
    (c92 : edge r92 (a 24) (a 56)=true)
    (c95 : edge r95 (a 25) (a 57)=true)
    (c97 : edge r97 (a 26) (a 58)=true)
    (c100 : edge r100 (a 27) (a 59)=true)
    (c102 : edge r102 (a 28) (a 60)=true)
    (c109 : edge r109 (a 31) (a 39)=true)
    (c115 : edge r115 (a 33) (a 34)=true)
    (c118 : edge r118 (a 33) (a 49)=true)
    (c119 : edge r119 (a 34) (a 38)=true)
    (c127 : edge r127 (a 36) (a 44)=true)
    (c134 : edge r134 (a 39) (a 40)=true)
    (c144 : edge r144 (a 42) (a 46)=true)
    : a 24 ∈ [0] ∧ a 55 ∈ [0] ∧ a 56 ∈ [0] ∧ a 57 ∈ [0] ∧ a 58 ∈ [0] ∧ a 59 ∈ [0] ∧ a 60 ∈ [0] ∧ a 39 ∈ [0] ∧ a 34 ∈ [0] ∧ a 49 ∈ [0] ∧ a 38 ∈ [0] ∧ a 44 ∈ [0] ∧ a 40 ∈ [0] ∧ a 46 ∈ [0] := by
  have b0 : a 24 ≠ 2 := exclude [0] (fun u v => edge r86 v u) (a 24) (a 23) 2 d23 c86 (by decide +kernel)
  have t0 : a 24 ∈ [0] := remove (a 24) 2 [0,2] d24 b0
  have b1 : a 55 ≠ 1 := exclude [0] (fun u v => edge r89 v u) (a 55) (a 23) 1 d23 c89 (by decide +kernel)
  have t1 : a 55 ∈ [0] := remove (a 55) 1 [0,1] d55 b1
  have b2 : a 56 ≠ 1 := exclude [0] (fun u v => edge r92 v u) (a 56) (a 24) 1 t0 c92 (by decide +kernel)
  have t2 : a 56 ∈ [0] := remove (a 56) 1 [0,1] d56 b2
  have b3 : a 57 ≠ 1 := exclude [0] (fun u v => edge r95 v u) (a 57) (a 25) 1 d25 c95 (by decide +kernel)
  have t3 : a 57 ∈ [0] := remove (a 57) 1 [0,1] d57 b3
  have b4 : a 58 ≠ 1 := exclude [0] (fun u v => edge r97 v u) (a 58) (a 26) 1 d26 c97 (by decide +kernel)
  have t4 : a 58 ∈ [0] := remove (a 58) 1 [0,1] d58 b4
  have b5 : a 59 ≠ 1 := exclude [0] (fun u v => edge r100 v u) (a 59) (a 27) 1 d27 c100 (by decide +kernel)
  have t5 : a 59 ∈ [0] := remove (a 59) 1 [0,1] d59 b5
  have b6 : a 60 ≠ 1 := exclude [0] (fun u v => edge r102 v u) (a 60) (a 28) 1 d28 c102 (by decide +kernel)
  have t6 : a 60 ∈ [0,2,3] := remove (a 60) 1 [0,1,2,3] d60 b6
  have b7 : a 60 ≠ 2 := exclude [0] (fun u v => edge r102 v u) (a 60) (a 28) 2 d28 c102 (by decide +kernel)
  have t7 : a 60 ∈ [0,3] := remove (a 60) 2 [0,2,3] t6 b7
  have b8 : a 60 ≠ 3 := exclude [0] (fun u v => edge r102 v u) (a 60) (a 28) 3 d28 c102 (by decide +kernel)
  have t8 : a 60 ∈ [0] := remove (a 60) 3 [0,3] t7 b8
  have b9 : a 39 ≠ 1 := exclude [0] (fun u v => edge r109 v u) (a 39) (a 31) 1 d31 c109 (by decide +kernel)
  have t9 : a 39 ∈ [0] := remove (a 39) 1 [0,1] d39 b9
  have b10 : a 34 ≠ 1 := exclude [0] (fun u v => edge r115 v u) (a 34) (a 33) 1 d33 c115 (by decide +kernel)
  have t10 : a 34 ∈ [0] := remove (a 34) 1 [0,1] d34 b10
  have b11 : a 49 ≠ 1 := exclude [0] (fun u v => edge r118 v u) (a 49) (a 33) 1 d33 c118 (by decide +kernel)
  have t11 : a 49 ∈ [0] := remove (a 49) 1 [0,1] d49 b11
  have b12 : a 38 ≠ 1 := exclude [0] (fun u v => edge r119 v u) (a 38) (a 34) 1 t10 c119 (by decide +kernel)
  have t12 : a 38 ∈ [0] := remove (a 38) 1 [0,1] d38 b12
  have b13 : a 44 ≠ 1 := exclude [0] (fun u v => edge r127 v u) (a 44) (a 36) 1 d36 c127 (by decide +kernel)
  have t13 : a 44 ∈ [0] := remove (a 44) 1 [0,1] d44 b13
  have b14 : a 40 ≠ 1 := exclude [0] (fun u v => edge r134 v u) (a 40) (a 39) 1 t9 c134 (by decide +kernel)
  have t14 : a 40 ∈ [0] := remove (a 40) 1 [0,1] d40 b14
  have b15 : a 46 ≠ 1 := exclude [0] (fun u v => edge r144 v u) (a 46) (a 42) 1 d42 c144 (by decide +kernel)
  have t15 : a 46 ∈ [0] := remove (a 46) 1 [0,1] d46 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))

theorem chunk5 (a : Nat → Nat)
    (d62 : a 62 ∈ [0,1])
    (d46 : a 46 ∈ [0])
    (d48 : a 48 ∈ [0,1])
    (d47 : a 47 ∈ [0])
    (d52 : a 52 ∈ [0,1])
    (d50 : a 50 ∈ [0,1])
    (d49 : a 49 ∈ [0])
    (d54 : a 54 ∈ [0,1])
    (d61 : a 61 ∈ [0,1])
    (d53 : a 53 ∈ [0])
    (d8 : a 8 ∈ [0,1])
    (d12 : a 12 ∈ [0])
    (c36 : edge r36 (a 8) (a 12)=true)
    (c153 : edge r153 (a 46) (a 62)=true)
    (c154 : edge r154 (a 47) (a 48)=true)
    (c159 : edge r159 (a 48) (a 52)=true)
    (c161 : edge r161 (a 49) (a 50)=true)
    (c164 : edge r164 (a 50) (a 54)=true)
    (c172 : edge r172 (a 53) (a 61)=true)
    : a 62 ∈ [0] ∧ a 48 ∈ [0] ∧ a 52 ∈ [0] ∧ a 50 ∈ [0] ∧ a 54 ∈ [0] ∧ a 61 ∈ [0] ∧ a 8 ∈ [0] := by
  have b0 : a 62 ≠ 1 := exclude [0] (fun u v => edge r153 v u) (a 62) (a 46) 1 d46 c153 (by decide +kernel)
  have t0 : a 62 ∈ [0] := remove (a 62) 1 [0,1] d62 b0
  have b1 : a 48 ≠ 1 := exclude [0] (fun u v => edge r154 v u) (a 48) (a 47) 1 d47 c154 (by decide +kernel)
  have t1 : a 48 ∈ [0] := remove (a 48) 1 [0,1] d48 b1
  have b2 : a 52 ≠ 1 := exclude [0] (fun u v => edge r159 v u) (a 52) (a 48) 1 t1 c159 (by decide +kernel)
  have t2 : a 52 ∈ [0] := remove (a 52) 1 [0,1] d52 b2
  have b3 : a 50 ≠ 1 := exclude [0] (fun u v => edge r161 v u) (a 50) (a 49) 1 d49 c161 (by decide +kernel)
  have t3 : a 50 ∈ [0] := remove (a 50) 1 [0,1] d50 b3
  have b4 : a 54 ≠ 1 := exclude [0] (fun u v => edge r164 v u) (a 54) (a 50) 1 t3 c164 (by decide +kernel)
  have t4 : a 54 ∈ [0] := remove (a 54) 1 [0,1] d54 b4
  have b5 : a 61 ≠ 1 := exclude [0] (fun u v => edge r172 v u) (a 61) (a 53) 1 d53 c172 (by decide +kernel)
  have t5 : a 61 ∈ [0] := remove (a 61) 1 [0,1] d61 b5
  have b6 : a 8 ≠ 1 := exclude [0] (edge r36) (a 8) (a 12) 1 d12 c36 (by decide +kernel)
  have t6 : a 8 ∈ [0] := remove (a 8) 1 [0,1] d8 b6
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (t6))))))
#print axioms chunk4
#print axioms chunk5
end PartitionCover205_239
