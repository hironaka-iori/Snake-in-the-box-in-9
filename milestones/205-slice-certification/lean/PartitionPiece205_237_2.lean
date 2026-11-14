import PartitionData205_237
namespace PartitionCover205_237
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d23 : a 23 ∈ [0,1])
    (d9 : a 9 ∈ [1])
    (d38 : a 38 ∈ [0,1])
    (d40 : a 40 ∈ [0,1])
    (d10 : a 10 ∈ [1])
    (d14 : a 14 ∈ [0,1])
    (d15 : a 15 ∈ [2])
    (d44 : a 44 ∈ [0,2])
    (d46 : a 46 ∈ [0,1])
    (d16 : a 16 ∈ [1])
    (d24 : a 24 ∈ [0,2])
    (d27 : a 27 ∈ [0,1])
    (d52 : a 52 ∈ [0,1])
    (d28 : a 28 ∈ [0,1])
    (d57 : a 57 ∈ [0,1])
    (d29 : a 29 ∈ [0,2])
    (d30 : a 30 ∈ [1])
    (d33 : a 33 ∈ [0,1])
    (d48 : a 48 ∈ [0,1])
    (d42 : a 42 ∈ [0,1])
    (d34 : a 34 ∈ [1])
    (d49 : a 49 ∈ [0,2])
    (c36 : edge r36 (a 9) (a 23)=true)
    (c37 : edge r37 (a 9) (a 38)=true)
    (c41 : edge r41 (a 10) (a 40)=true)
    (c50 : edge r50 (a 14) (a 15)=true)
    (c54 : edge r54 (a 14) (a 44)=true)
    (c61 : edge r61 (a 16) (a 46)=true)
    (c78 : edge r78 (a 23) (a 24)=true)
    (c79 : edge r79 (a 23) (a 27)=true)
    (c80 : edge r80 (a 23) (a 52)=true)
    (c81 : edge r81 (a 24) (a 28)=true)
    (c90 : edge r90 (a 28) (a 57)=true)
    (c91 : edge r91 (a 29) (a 30)=true)
    (c96 : edge r96 (a 30) (a 33)=true)
    (c108 : edge r108 (a 33) (a 48)=true)
    (c110 : edge r110 (a 34) (a 42)=true)
    (c111 : edge r111 (a 34) (a 49)=true)
    : a 23 ∈ [1] ∧ a 38 ∈ [1] ∧ a 40 ∈ [1] ∧ a 14 ∈ [1] ∧ a 44 ∈ [2] ∧ a 46 ∈ [1] ∧ a 24 ∈ [2] ∧ a 27 ∈ [1] ∧ a 52 ∈ [1] ∧ a 28 ∈ [1] ∧ a 57 ∈ [1] ∧ a 29 ∈ [2] ∧ a 33 ∈ [1] ∧ a 48 ∈ [1] ∧ a 42 ∈ [1] ∧ a 49 ∈ [2] := by
  have b0 : a 23 ≠ 0 := exclude [1] (fun u v => edge r36 v u) (a 23) (a 9) 0 d9 c36 (by decide +kernel)
  have t0 : a 23 ∈ [1] := remove (a 23) 0 [0,1] d23 b0
  have b1 : a 38 ≠ 0 := exclude [1] (fun u v => edge r37 v u) (a 38) (a 9) 0 d9 c37 (by decide +kernel)
  have t1 : a 38 ∈ [1] := remove (a 38) 0 [0,1] d38 b1
  have b2 : a 40 ≠ 0 := exclude [1] (fun u v => edge r41 v u) (a 40) (a 10) 0 d10 c41 (by decide +kernel)
  have t2 : a 40 ∈ [1] := remove (a 40) 0 [0,1] d40 b2
  have b3 : a 14 ≠ 0 := exclude [2] (edge r50) (a 14) (a 15) 0 d15 c50 (by decide +kernel)
  have t3 : a 14 ∈ [1] := remove (a 14) 0 [0,1] d14 b3
  have b4 : a 44 ≠ 0 := exclude [1] (fun u v => edge r54 v u) (a 44) (a 14) 0 t3 c54 (by decide +kernel)
  have t4 : a 44 ∈ [2] := remove (a 44) 0 [0,2] d44 b4
  have b5 : a 46 ≠ 0 := exclude [1] (fun u v => edge r61 v u) (a 46) (a 16) 0 d16 c61 (by decide +kernel)
  have t5 : a 46 ∈ [1] := remove (a 46) 0 [0,1] d46 b5
  have b6 : a 24 ≠ 0 := exclude [1] (fun u v => edge r78 v u) (a 24) (a 23) 0 t0 c78 (by decide +kernel)
  have t6 : a 24 ∈ [2] := remove (a 24) 0 [0,2] d24 b6
  have b7 : a 27 ≠ 0 := exclude [1] (fun u v => edge r79 v u) (a 27) (a 23) 0 t0 c79 (by decide +kernel)
  have t7 : a 27 ∈ [1] := remove (a 27) 0 [0,1] d27 b7
  have b8 : a 52 ≠ 0 := exclude [1] (fun u v => edge r80 v u) (a 52) (a 23) 0 t0 c80 (by decide +kernel)
  have t8 : a 52 ∈ [1] := remove (a 52) 0 [0,1] d52 b8
  have b9 : a 28 ≠ 0 := exclude [2] (fun u v => edge r81 v u) (a 28) (a 24) 0 t6 c81 (by decide +kernel)
  have t9 : a 28 ∈ [1] := remove (a 28) 0 [0,1] d28 b9
  have b10 : a 57 ≠ 0 := exclude [1] (fun u v => edge r90 v u) (a 57) (a 28) 0 t9 c90 (by decide +kernel)
  have t10 : a 57 ∈ [1] := remove (a 57) 0 [0,1] d57 b10
  have b11 : a 29 ≠ 0 := exclude [1] (edge r91) (a 29) (a 30) 0 d30 c91 (by decide +kernel)
  have t11 : a 29 ∈ [2] := remove (a 29) 0 [0,2] d29 b11
  have b12 : a 33 ≠ 0 := exclude [1] (fun u v => edge r96 v u) (a 33) (a 30) 0 d30 c96 (by decide +kernel)
  have t12 : a 33 ∈ [1] := remove (a 33) 0 [0,1] d33 b12
  have b13 : a 48 ≠ 0 := exclude [1] (fun u v => edge r108 v u) (a 48) (a 33) 0 t12 c108 (by decide +kernel)
  have t13 : a 48 ∈ [1] := remove (a 48) 0 [0,1] d48 b13
  have b14 : a 42 ≠ 0 := exclude [1] (fun u v => edge r110 v u) (a 42) (a 34) 0 d34 c110 (by decide +kernel)
  have t14 : a 42 ∈ [1] := remove (a 42) 0 [0,1] d42 b14
  have b15 : a 49 ≠ 0 := exclude [1] (fun u v => edge r111 v u) (a 49) (a 34) 0 d34 c111 (by decide +kernel)
  have t15 : a 49 ∈ [2] := remove (a 49) 0 [0,2] d49 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk9 (a : Nat → Nat)
    (d39 : a 39 ∈ [0,2])
    (d38 : a 38 ∈ [1])
    (d43 : a 43 ∈ [0,1])
    (d47 : a 47 ∈ [0,1])
    (d46 : a 46 ∈ [1])
    (d55 : a 55 ∈ [0,1])
    (d48 : a 48 ∈ [1])
    (d51 : a 51 ∈ [0,2])
    (d13 : a 13 ∈ [0,1])
    (d28 : a 28 ∈ [1])
    (c48 : edge r48 (a 13) (a 28)=true)
    (c120 : edge r120 (a 38) (a 39)=true)
    (c123 : edge r123 (a 39) (a 43)=true)
    (c138 : edge r138 (a 46) (a 47)=true)
    (c144 : edge r144 (a 48) (a 55)=true)
    (c149 : edge r149 (a 51) (a 55)=true)
    : a 39 ∈ [2] ∧ a 43 ∈ [1] ∧ a 47 ∈ [1] ∧ a 55 ∈ [1] ∧ a 51 ∈ [2] ∧ a 13 ∈ [1] := by
  have b0 : a 39 ≠ 0 := exclude [1] (fun u v => edge r120 v u) (a 39) (a 38) 0 d38 c120 (by decide +kernel)
  have t0 : a 39 ∈ [2] := remove (a 39) 0 [0,2] d39 b0
  have b1 : a 43 ≠ 0 := exclude [2] (fun u v => edge r123 v u) (a 43) (a 39) 0 t0 c123 (by decide +kernel)
  have t1 : a 43 ∈ [1] := remove (a 43) 0 [0,1] d43 b1
  have b2 : a 47 ≠ 0 := exclude [1] (fun u v => edge r138 v u) (a 47) (a 46) 0 d46 c138 (by decide +kernel)
  have t2 : a 47 ∈ [1] := remove (a 47) 0 [0,1] d47 b2
  have b3 : a 55 ≠ 0 := exclude [1] (fun u v => edge r144 v u) (a 55) (a 48) 0 d48 c144 (by decide +kernel)
  have t3 : a 55 ∈ [1] := remove (a 55) 0 [0,1] d55 b3
  have b4 : a 51 ≠ 0 := exclude [1] (edge r149) (a 51) (a 55) 0 t3 c149 (by decide +kernel)
  have t4 : a 51 ∈ [2] := remove (a 51) 0 [0,2] d51 b4
  have b5 : a 13 ≠ 0 := exclude [1] (edge r48) (a 13) (a 28) 0 d28 c48 (by decide +kernel)
  have t5 : a 13 ∈ [1] := remove (a 13) 0 [0,1] d13 b5
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (t5)))))
#print axioms chunk8
#print axioms chunk9
end PartitionCover205_237
