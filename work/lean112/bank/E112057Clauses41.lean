import E112057Semantics
import B112E057Inputs
namespace Snake9.Regrowth.E112057
noncomputable section
local instance blockDec41 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1313 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 891 = true := by
  have hs : count891 q = (countLit q [-17]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-19])
  have hm := merge_left (literal (valuationOf q) (-17)) (literal (valuationOf q) (891)) (countLit q [-17]) (countLit q [-19]) (count891 q) 1 (meaningNeg17 q) (meaning891 q) hs
  change (! (valuationOf q 17)) = false ∨ valuationOf q 891 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1313 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 891 = true := counterClause1313 (baseVal q)

theorem counterClause1314 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 19 = true ∨ valuationOf q 892 = true := by
  have hs : count891 q = (countLit q [-17]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-19])
  have hm := merge_two (literal (valuationOf q) (-17)) (literal (valuationOf q) (-19)) (literal (valuationOf q) (892)) (countLit q [-17]) (countLit q [-19]) (count891 q) 1 1 (meaningNeg17 q) (meaningNeg19 q) (meaning892 q) hs
  change (! (valuationOf q 17)) = false ∨ (! (valuationOf q 19)) = false ∨ valuationOf q 892 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1314 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 19 = true ∨ valuation q 892 = true := counterClause1314 (baseVal q)

theorem counterClause1315 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 893 = true := by
  have hs : count893 q = (countLit q [-22]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-25])
  have hm := merge_right (literal (valuationOf q) (-25)) (literal (valuationOf q) (893)) (countLit q [-22]) (countLit q [-25]) (count893 q) 1 (meaningNeg25 q) (meaning893 q) hs
  change (! (valuationOf q 25)) = false ∨ valuationOf q 893 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1315 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 893 = true := counterClause1315 (baseVal q)

theorem counterClause1316 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 893 = true := by
  have hs : count893 q = (countLit q [-22]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-25])
  have hm := merge_left (literal (valuationOf q) (-22)) (literal (valuationOf q) (893)) (countLit q [-22]) (countLit q [-25]) (count893 q) 1 (meaningNeg22 q) (meaning893 q) hs
  change (! (valuationOf q 22)) = false ∨ valuationOf q 893 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1316 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 893 = true := counterClause1316 (baseVal q)

theorem counterClause1317 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 25 = true ∨ valuationOf q 894 = true := by
  have hs : count893 q = (countLit q [-22]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-25])
  have hm := merge_two (literal (valuationOf q) (-22)) (literal (valuationOf q) (-25)) (literal (valuationOf q) (894)) (countLit q [-22]) (countLit q [-25]) (count893 q) 1 1 (meaningNeg22 q) (meaningNeg25 q) (meaning894 q) hs
  change (! (valuationOf q 22)) = false ∨ (! (valuationOf q 25)) = false ∨ valuationOf q 894 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1317 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 25 = true ∨ valuation q 894 = true := counterClause1317 (baseVal q)

theorem counterClause1318 (q : Nat → Bool) : valuationOf q 893 = false ∨ valuationOf q 895 = true := by
  have hs : count895 q = (countLit q [-17, -19]) + (countLit q [-22, -25]) := List.countP_append (p := literal q) (l₁ := [-17, -19]) (l₂ := [-22, -25])
  have hm := merge_right (literal (valuationOf q) (893)) (literal (valuationOf q) (895)) (countLit q [-17, -19]) (countLit q [-22, -25]) (count895 q) 1 (meaning893 q) (meaning895 q) hs
  change valuationOf q 893 = false ∨ valuationOf q 895 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1318 (q : Snake 81) (h : Conditions q) : valuation q 893 = false ∨ valuation q 895 = true := counterClause1318 (baseVal q)

theorem counterClause1319 (q : Nat → Bool) : valuationOf q 894 = false ∨ valuationOf q 896 = true := by
  have hs : count895 q = (countLit q [-17, -19]) + (countLit q [-22, -25]) := List.countP_append (p := literal q) (l₁ := [-17, -19]) (l₂ := [-22, -25])
  have hm := merge_right (literal (valuationOf q) (894)) (literal (valuationOf q) (896)) (countLit q [-17, -19]) (countLit q [-22, -25]) (count895 q) 2 (meaning894 q) (meaning896 q) hs
  change valuationOf q 894 = false ∨ valuationOf q 896 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1319 (q : Snake 81) (h : Conditions q) : valuation q 894 = false ∨ valuation q 896 = true := counterClause1319 (baseVal q)

theorem counterClause1320 (q : Nat → Bool) : valuationOf q 891 = false ∨ valuationOf q 895 = true := by
  have hs : count895 q = (countLit q [-17, -19]) + (countLit q [-22, -25]) := List.countP_append (p := literal q) (l₁ := [-17, -19]) (l₂ := [-22, -25])
  have hm := merge_left (literal (valuationOf q) (891)) (literal (valuationOf q) (895)) (countLit q [-17, -19]) (countLit q [-22, -25]) (count895 q) 1 (meaning891 q) (meaning895 q) hs
  change valuationOf q 891 = false ∨ valuationOf q 895 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1320 (q : Snake 81) (h : Conditions q) : valuation q 891 = false ∨ valuation q 895 = true := counterClause1320 (baseVal q)

theorem counterClause1321 (q : Nat → Bool) : valuationOf q 891 = false ∨ valuationOf q 893 = false ∨ valuationOf q 896 = true := by
  have hs : count895 q = (countLit q [-17, -19]) + (countLit q [-22, -25]) := List.countP_append (p := literal q) (l₁ := [-17, -19]) (l₂ := [-22, -25])
  have hm := merge_two (literal (valuationOf q) (891)) (literal (valuationOf q) (893)) (literal (valuationOf q) (896)) (countLit q [-17, -19]) (countLit q [-22, -25]) (count895 q) 1 1 (meaning891 q) (meaning893 q) (meaning896 q) hs
  change valuationOf q 891 = false ∨ valuationOf q 893 = false ∨ valuationOf q 896 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1321 (q : Snake 81) (h : Conditions q) : valuation q 891 = false ∨ valuation q 893 = false ∨ valuation q 896 = true := counterClause1321 (baseVal q)

theorem counterClause1322 (q : Nat → Bool) : valuationOf q 891 = false ∨ valuationOf q 894 = false ∨ valuationOf q 897 = true := by
  have hs : count895 q = (countLit q [-17, -19]) + (countLit q [-22, -25]) := List.countP_append (p := literal q) (l₁ := [-17, -19]) (l₂ := [-22, -25])
  have hm := merge_two (literal (valuationOf q) (891)) (literal (valuationOf q) (894)) (literal (valuationOf q) (897)) (countLit q [-17, -19]) (countLit q [-22, -25]) (count895 q) 1 2 (meaning891 q) (meaning894 q) (meaning897 q) hs
  change valuationOf q 891 = false ∨ valuationOf q 894 = false ∨ valuationOf q 897 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1322 (q : Snake 81) (h : Conditions q) : valuation q 891 = false ∨ valuation q 894 = false ∨ valuation q 897 = true := counterClause1322 (baseVal q)

theorem counterClause1323 (q : Nat → Bool) : valuationOf q 892 = false ∨ valuationOf q 896 = true := by
  have hs : count895 q = (countLit q [-17, -19]) + (countLit q [-22, -25]) := List.countP_append (p := literal q) (l₁ := [-17, -19]) (l₂ := [-22, -25])
  have hm := merge_left (literal (valuationOf q) (892)) (literal (valuationOf q) (896)) (countLit q [-17, -19]) (countLit q [-22, -25]) (count895 q) 2 (meaning892 q) (meaning896 q) hs
  change valuationOf q 892 = false ∨ valuationOf q 896 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1323 (q : Snake 81) (h : Conditions q) : valuation q 892 = false ∨ valuation q 896 = true := counterClause1323 (baseVal q)

theorem counterClause1324 (q : Nat → Bool) : valuationOf q 892 = false ∨ valuationOf q 893 = false ∨ valuationOf q 897 = true := by
  have hs : count895 q = (countLit q [-17, -19]) + (countLit q [-22, -25]) := List.countP_append (p := literal q) (l₁ := [-17, -19]) (l₂ := [-22, -25])
  have hm := merge_two (literal (valuationOf q) (892)) (literal (valuationOf q) (893)) (literal (valuationOf q) (897)) (countLit q [-17, -19]) (countLit q [-22, -25]) (count895 q) 2 1 (meaning892 q) (meaning893 q) (meaning897 q) hs
  change valuationOf q 892 = false ∨ valuationOf q 893 = false ∨ valuationOf q 897 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1324 (q : Snake 81) (h : Conditions q) : valuation q 892 = false ∨ valuation q 893 = false ∨ valuation q 897 = true := counterClause1324 (baseVal q)

theorem counterClause1325 (q : Nat → Bool) : valuationOf q 892 = false ∨ valuationOf q 894 = false ∨ valuationOf q 898 = true := by
  have hs : count895 q = (countLit q [-17, -19]) + (countLit q [-22, -25]) := List.countP_append (p := literal q) (l₁ := [-17, -19]) (l₂ := [-22, -25])
  have hm := merge_two (literal (valuationOf q) (892)) (literal (valuationOf q) (894)) (literal (valuationOf q) (898)) (countLit q [-17, -19]) (countLit q [-22, -25]) (count895 q) 2 2 (meaning892 q) (meaning894 q) (meaning898 q) hs
  change valuationOf q 892 = false ∨ valuationOf q 894 = false ∨ valuationOf q 898 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1325 (q : Snake 81) (h : Conditions q) : valuation q 892 = false ∨ valuation q 894 = false ∨ valuation q 898 = true := counterClause1325 (baseVal q)

theorem counterClause1326 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 899 = true := by
  have hs : count899 q = (countLit q [-26]) + (countLit q [-28]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-28])
  have hm := merge_right (literal (valuationOf q) (-28)) (literal (valuationOf q) (899)) (countLit q [-26]) (countLit q [-28]) (count899 q) 1 (meaningNeg28 q) (meaning899 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 899 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1326 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 899 = true := counterClause1326 (baseVal q)

theorem counterClause1327 (q : Nat → Bool) : valuationOf q 26 = true ∨ valuationOf q 899 = true := by
  have hs : count899 q = (countLit q [-26]) + (countLit q [-28]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-28])
  have hm := merge_left (literal (valuationOf q) (-26)) (literal (valuationOf q) (899)) (countLit q [-26]) (countLit q [-28]) (count899 q) 1 (meaningNeg26 q) (meaning899 q) hs
  change (! (valuationOf q 26)) = false ∨ valuationOf q 899 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1327 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 899 = true := counterClause1327 (baseVal q)

theorem counterClause1328 (q : Nat → Bool) : valuationOf q 26 = true ∨ valuationOf q 28 = true ∨ valuationOf q 900 = true := by
  have hs : count899 q = (countLit q [-26]) + (countLit q [-28]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-28])
  have hm := merge_two (literal (valuationOf q) (-26)) (literal (valuationOf q) (-28)) (literal (valuationOf q) (900)) (countLit q [-26]) (countLit q [-28]) (count899 q) 1 1 (meaningNeg26 q) (meaningNeg28 q) (meaning900 q) hs
  change (! (valuationOf q 26)) = false ∨ (! (valuationOf q 28)) = false ∨ valuationOf q 900 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1328 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 28 = true ∨ valuation q 900 = true := counterClause1328 (baseVal q)

theorem counterClause1329 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 901 = true := by
  have hs : count901 q = (countLit q [-30]) + (countLit q [-33]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-33])
  have hm := merge_right (literal (valuationOf q) (-33)) (literal (valuationOf q) (901)) (countLit q [-30]) (countLit q [-33]) (count901 q) 1 (meaningNeg33 q) (meaning901 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 901 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1329 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 901 = true := counterClause1329 (baseVal q)

theorem counterClause1330 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 901 = true := by
  have hs : count901 q = (countLit q [-30]) + (countLit q [-33]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-33])
  have hm := merge_left (literal (valuationOf q) (-30)) (literal (valuationOf q) (901)) (countLit q [-30]) (countLit q [-33]) (count901 q) 1 (meaningNeg30 q) (meaning901 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 901 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1330 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 901 = true := counterClause1330 (baseVal q)

theorem counterClause1331 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 33 = true ∨ valuationOf q 902 = true := by
  have hs : count901 q = (countLit q [-30]) + (countLit q [-33]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-33])
  have hm := merge_two (literal (valuationOf q) (-30)) (literal (valuationOf q) (-33)) (literal (valuationOf q) (902)) (countLit q [-30]) (countLit q [-33]) (count901 q) 1 1 (meaningNeg30 q) (meaningNeg33 q) (meaning902 q) hs
  change (! (valuationOf q 30)) = false ∨ (! (valuationOf q 33)) = false ∨ valuationOf q 902 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1331 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 33 = true ∨ valuation q 902 = true := counterClause1331 (baseVal q)

theorem counterClause1332 (q : Nat → Bool) : valuationOf q 901 = false ∨ valuationOf q 903 = true := by
  have hs : count903 q = (countLit q [-26, -28]) + (countLit q [-30, -33]) := List.countP_append (p := literal q) (l₁ := [-26, -28]) (l₂ := [-30, -33])
  have hm := merge_right (literal (valuationOf q) (901)) (literal (valuationOf q) (903)) (countLit q [-26, -28]) (countLit q [-30, -33]) (count903 q) 1 (meaning901 q) (meaning903 q) hs
  change valuationOf q 901 = false ∨ valuationOf q 903 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1332 (q : Snake 81) (h : Conditions q) : valuation q 901 = false ∨ valuation q 903 = true := counterClause1332 (baseVal q)

theorem counterClause1333 (q : Nat → Bool) : valuationOf q 902 = false ∨ valuationOf q 904 = true := by
  have hs : count903 q = (countLit q [-26, -28]) + (countLit q [-30, -33]) := List.countP_append (p := literal q) (l₁ := [-26, -28]) (l₂ := [-30, -33])
  have hm := merge_right (literal (valuationOf q) (902)) (literal (valuationOf q) (904)) (countLit q [-26, -28]) (countLit q [-30, -33]) (count903 q) 2 (meaning902 q) (meaning904 q) hs
  change valuationOf q 902 = false ∨ valuationOf q 904 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1333 (q : Snake 81) (h : Conditions q) : valuation q 902 = false ∨ valuation q 904 = true := counterClause1333 (baseVal q)

theorem counterClause1334 (q : Nat → Bool) : valuationOf q 899 = false ∨ valuationOf q 903 = true := by
  have hs : count903 q = (countLit q [-26, -28]) + (countLit q [-30, -33]) := List.countP_append (p := literal q) (l₁ := [-26, -28]) (l₂ := [-30, -33])
  have hm := merge_left (literal (valuationOf q) (899)) (literal (valuationOf q) (903)) (countLit q [-26, -28]) (countLit q [-30, -33]) (count903 q) 1 (meaning899 q) (meaning903 q) hs
  change valuationOf q 899 = false ∨ valuationOf q 903 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1334 (q : Snake 81) (h : Conditions q) : valuation q 899 = false ∨ valuation q 903 = true := counterClause1334 (baseVal q)

theorem counterClause1335 (q : Nat → Bool) : valuationOf q 899 = false ∨ valuationOf q 901 = false ∨ valuationOf q 904 = true := by
  have hs : count903 q = (countLit q [-26, -28]) + (countLit q [-30, -33]) := List.countP_append (p := literal q) (l₁ := [-26, -28]) (l₂ := [-30, -33])
  have hm := merge_two (literal (valuationOf q) (899)) (literal (valuationOf q) (901)) (literal (valuationOf q) (904)) (countLit q [-26, -28]) (countLit q [-30, -33]) (count903 q) 1 1 (meaning899 q) (meaning901 q) (meaning904 q) hs
  change valuationOf q 899 = false ∨ valuationOf q 901 = false ∨ valuationOf q 904 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1335 (q : Snake 81) (h : Conditions q) : valuation q 899 = false ∨ valuation q 901 = false ∨ valuation q 904 = true := counterClause1335 (baseVal q)

theorem counterClause1336 (q : Nat → Bool) : valuationOf q 899 = false ∨ valuationOf q 902 = false ∨ valuationOf q 905 = true := by
  have hs : count903 q = (countLit q [-26, -28]) + (countLit q [-30, -33]) := List.countP_append (p := literal q) (l₁ := [-26, -28]) (l₂ := [-30, -33])
  have hm := merge_two (literal (valuationOf q) (899)) (literal (valuationOf q) (902)) (literal (valuationOf q) (905)) (countLit q [-26, -28]) (countLit q [-30, -33]) (count903 q) 1 2 (meaning899 q) (meaning902 q) (meaning905 q) hs
  change valuationOf q 899 = false ∨ valuationOf q 902 = false ∨ valuationOf q 905 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1336 (q : Snake 81) (h : Conditions q) : valuation q 899 = false ∨ valuation q 902 = false ∨ valuation q 905 = true := counterClause1336 (baseVal q)

theorem counterClause1337 (q : Nat → Bool) : valuationOf q 900 = false ∨ valuationOf q 904 = true := by
  have hs : count903 q = (countLit q [-26, -28]) + (countLit q [-30, -33]) := List.countP_append (p := literal q) (l₁ := [-26, -28]) (l₂ := [-30, -33])
  have hm := merge_left (literal (valuationOf q) (900)) (literal (valuationOf q) (904)) (countLit q [-26, -28]) (countLit q [-30, -33]) (count903 q) 2 (meaning900 q) (meaning904 q) hs
  change valuationOf q 900 = false ∨ valuationOf q 904 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1337 (q : Snake 81) (h : Conditions q) : valuation q 900 = false ∨ valuation q 904 = true := counterClause1337 (baseVal q)

theorem counterClause1338 (q : Nat → Bool) : valuationOf q 900 = false ∨ valuationOf q 901 = false ∨ valuationOf q 905 = true := by
  have hs : count903 q = (countLit q [-26, -28]) + (countLit q [-30, -33]) := List.countP_append (p := literal q) (l₁ := [-26, -28]) (l₂ := [-30, -33])
  have hm := merge_two (literal (valuationOf q) (900)) (literal (valuationOf q) (901)) (literal (valuationOf q) (905)) (countLit q [-26, -28]) (countLit q [-30, -33]) (count903 q) 2 1 (meaning900 q) (meaning901 q) (meaning905 q) hs
  change valuationOf q 900 = false ∨ valuationOf q 901 = false ∨ valuationOf q 905 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1338 (q : Snake 81) (h : Conditions q) : valuation q 900 = false ∨ valuation q 901 = false ∨ valuation q 905 = true := counterClause1338 (baseVal q)

theorem counterClause1339 (q : Nat → Bool) : valuationOf q 900 = false ∨ valuationOf q 902 = false ∨ valuationOf q 906 = true := by
  have hs : count903 q = (countLit q [-26, -28]) + (countLit q [-30, -33]) := List.countP_append (p := literal q) (l₁ := [-26, -28]) (l₂ := [-30, -33])
  have hm := merge_two (literal (valuationOf q) (900)) (literal (valuationOf q) (902)) (literal (valuationOf q) (906)) (countLit q [-26, -28]) (countLit q [-30, -33]) (count903 q) 2 2 (meaning900 q) (meaning902 q) (meaning906 q) hs
  change valuationOf q 900 = false ∨ valuationOf q 902 = false ∨ valuationOf q 906 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1339 (q : Snake 81) (h : Conditions q) : valuation q 900 = false ∨ valuation q 902 = false ∨ valuation q 906 = true := counterClause1339 (baseVal q)

theorem counterClause1340 (q : Nat → Bool) : valuationOf q 903 = false ∨ valuationOf q 907 = true := by
  have hs : count907 q = (countLit q [-17, -19, -22, -25]) + (countLit q [-26, -28, -30, -33]) := List.countP_append (p := literal q) (l₁ := [-17, -19, -22, -25]) (l₂ := [-26, -28, -30, -33])
  have hm := merge_right (literal (valuationOf q) (903)) (literal (valuationOf q) (907)) (countLit q [-17, -19, -22, -25]) (countLit q [-26, -28, -30, -33]) (count907 q) 1 (meaning903 q) (meaning907 q) hs
  change valuationOf q 903 = false ∨ valuationOf q 907 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1340 (q : Snake 81) (h : Conditions q) : valuation q 903 = false ∨ valuation q 907 = true := counterClause1340 (baseVal q)

theorem counterClause1341 (q : Nat → Bool) : valuationOf q 904 = false ∨ valuationOf q 908 = true := by
  have hs : count907 q = (countLit q [-17, -19, -22, -25]) + (countLit q [-26, -28, -30, -33]) := List.countP_append (p := literal q) (l₁ := [-17, -19, -22, -25]) (l₂ := [-26, -28, -30, -33])
  have hm := merge_right (literal (valuationOf q) (904)) (literal (valuationOf q) (908)) (countLit q [-17, -19, -22, -25]) (countLit q [-26, -28, -30, -33]) (count907 q) 2 (meaning904 q) (meaning908 q) hs
  change valuationOf q 904 = false ∨ valuationOf q 908 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1341 (q : Snake 81) (h : Conditions q) : valuation q 904 = false ∨ valuation q 908 = true := counterClause1341 (baseVal q)

theorem counterClause1342 (q : Nat → Bool) : valuationOf q 905 = false ∨ valuationOf q 909 = true := by
  have hs : count907 q = (countLit q [-17, -19, -22, -25]) + (countLit q [-26, -28, -30, -33]) := List.countP_append (p := literal q) (l₁ := [-17, -19, -22, -25]) (l₂ := [-26, -28, -30, -33])
  have hm := merge_right (literal (valuationOf q) (905)) (literal (valuationOf q) (909)) (countLit q [-17, -19, -22, -25]) (countLit q [-26, -28, -30, -33]) (count907 q) 3 (meaning905 q) (meaning909 q) hs
  change valuationOf q 905 = false ∨ valuationOf q 909 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1342 (q : Snake 81) (h : Conditions q) : valuation q 905 = false ∨ valuation q 909 = true := counterClause1342 (baseVal q)

theorem counterClause1343 (q : Nat → Bool) : valuationOf q 906 = false ∨ valuationOf q 910 = true := by
  have hs : count907 q = (countLit q [-17, -19, -22, -25]) + (countLit q [-26, -28, -30, -33]) := List.countP_append (p := literal q) (l₁ := [-17, -19, -22, -25]) (l₂ := [-26, -28, -30, -33])
  have hm := merge_right (literal (valuationOf q) (906)) (literal (valuationOf q) (910)) (countLit q [-17, -19, -22, -25]) (countLit q [-26, -28, -30, -33]) (count907 q) 4 (meaning906 q) (meaning910 q) hs
  change valuationOf q 906 = false ∨ valuationOf q 910 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1343 (q : Snake 81) (h : Conditions q) : valuation q 906 = false ∨ valuation q 910 = true := counterClause1343 (baseVal q)

theorem counterClause1344 (q : Nat → Bool) : valuationOf q 895 = false ∨ valuationOf q 907 = true := by
  have hs : count907 q = (countLit q [-17, -19, -22, -25]) + (countLit q [-26, -28, -30, -33]) := List.countP_append (p := literal q) (l₁ := [-17, -19, -22, -25]) (l₂ := [-26, -28, -30, -33])
  have hm := merge_left (literal (valuationOf q) (895)) (literal (valuationOf q) (907)) (countLit q [-17, -19, -22, -25]) (countLit q [-26, -28, -30, -33]) (count907 q) 1 (meaning895 q) (meaning907 q) hs
  change valuationOf q 895 = false ∨ valuationOf q 907 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1344 (q : Snake 81) (h : Conditions q) : valuation q 895 = false ∨ valuation q 907 = true := counterClause1344 (baseVal q)

theorem block41 (q : Snake 81) (h : Conditions q) : B112E057.Block41 (valuation q) :=
  ⟨clause1313 q h, clause1314 q h, clause1315 q h, clause1316 q h, clause1317 q h, clause1318 q h, clause1319 q h, clause1320 q h, clause1321 q h, clause1322 q h, clause1323 q h, clause1324 q h, clause1325 q h, clause1326 q h, clause1327 q h, clause1328 q h, clause1329 q h, clause1330 q h, clause1331 q h, clause1332 q h, clause1333 q h, clause1334 q h, clause1335 q h, clause1336 q h, clause1337 q h, clause1338 q h, clause1339 q h, clause1340 q h, clause1341 q h, clause1342 q h, clause1343 q h, clause1344 q h⟩

end
end Snake9.Regrowth.E112057
