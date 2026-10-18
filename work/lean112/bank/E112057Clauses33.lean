import E112057Semantics
import B112E057Inputs
namespace Snake9.Regrowth.E112057
noncomputable section
local instance blockDec33 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1057 (q : Nat → Bool) : valuationOf q 288 = false ∨ valuationOf q 296 = true := by
  have hs : count295 q = (countLit q [143, 144, 145, 146]) + (countLit q [147, 148, 149, 150]) := List.countP_append (p := literal q) (l₁ := [143, 144, 145, 146]) (l₂ := [147, 148, 149, 150])
  have hm := merge_left (literal (valuationOf q) (288)) (literal (valuationOf q) (296)) (countLit q [143, 144, 145, 146]) (countLit q [147, 148, 149, 150]) (count295 q) 2 (meaning288 q) (meaning296 q) hs
  change valuationOf q 288 = false ∨ valuationOf q 296 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1057 (q : Snake 81) (h : Conditions q) : valuation q 288 = false ∨ valuation q 296 = true := counterClause1057 (baseVal q)

theorem counterClause1058 (q : Nat → Bool) : valuationOf q 151 = false ∨ valuationOf q 297 = true := by
  have hs : count297 q = (countLit q [151]) + (countLit q [152]) := List.countP_append (p := literal q) (l₁ := [151]) (l₂ := [152])
  have hm := merge_left (literal (valuationOf q) (151)) (literal (valuationOf q) (297)) (countLit q [151]) (countLit q [152]) (count297 q) 1 (meaning151 q) (meaning297 q) hs
  change valuationOf q 151 = false ∨ valuationOf q 297 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1058 (q : Snake 81) (h : Conditions q) : valuation q 151 = false ∨ valuation q 297 = true := counterClause1058 (baseVal q)

theorem counterClause1059 (q : Nat → Bool) : valuationOf q 154 = false ∨ valuationOf q 299 = true := by
  have hs : count299 q = (countLit q [153]) + (countLit q [154]) := List.countP_append (p := literal q) (l₁ := [153]) (l₂ := [154])
  have hm := merge_right (literal (valuationOf q) (154)) (literal (valuationOf q) (299)) (countLit q [153]) (countLit q [154]) (count299 q) 1 (meaning154 q) (meaning299 q) hs
  change valuationOf q 154 = false ∨ valuationOf q 299 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1059 (q : Snake 81) (h : Conditions q) : valuation q 154 = false ∨ valuation q 299 = true := counterClause1059 (baseVal q)

theorem counterClause1060 (q : Nat → Bool) : valuationOf q 299 = false ∨ valuationOf q 301 = true := by
  have hs : count301 q = (countLit q [151, 152]) + (countLit q [153, 154]) := List.countP_append (p := literal q) (l₁ := [151, 152]) (l₂ := [153, 154])
  have hm := merge_right (literal (valuationOf q) (299)) (literal (valuationOf q) (301)) (countLit q [151, 152]) (countLit q [153, 154]) (count301 q) 1 (meaning299 q) (meaning301 q) hs
  change valuationOf q 299 = false ∨ valuationOf q 301 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1060 (q : Snake 81) (h : Conditions q) : valuation q 299 = false ∨ valuation q 301 = true := counterClause1060 (baseVal q)

theorem counterClause1061 (q : Nat → Bool) : valuationOf q 297 = false ∨ valuationOf q 301 = true := by
  have hs : count301 q = (countLit q [151, 152]) + (countLit q [153, 154]) := List.countP_append (p := literal q) (l₁ := [151, 152]) (l₂ := [153, 154])
  have hm := merge_left (literal (valuationOf q) (297)) (literal (valuationOf q) (301)) (countLit q [151, 152]) (countLit q [153, 154]) (count301 q) 1 (meaning297 q) (meaning301 q) hs
  change valuationOf q 297 = false ∨ valuationOf q 301 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1061 (q : Snake 81) (h : Conditions q) : valuation q 297 = false ∨ valuation q 301 = true := counterClause1061 (baseVal q)

theorem counterClause1062 (q : Nat → Bool) : valuationOf q 156 = false ∨ valuationOf q 303 = true := by
  have hs : count303 q = (countLit q [155]) + (countLit q [156]) := List.countP_append (p := literal q) (l₁ := [155]) (l₂ := [156])
  have hm := merge_right (literal (valuationOf q) (156)) (literal (valuationOf q) (303)) (countLit q [155]) (countLit q [156]) (count303 q) 1 (meaning156 q) (meaning303 q) hs
  change valuationOf q 156 = false ∨ valuationOf q 303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1062 (q : Snake 81) (h : Conditions q) : valuation q 156 = false ∨ valuation q 303 = true := counterClause1062 (baseVal q)

theorem counterClause1063 (q : Nat → Bool) : valuationOf q 158 = false ∨ valuationOf q 305 = true := by
  have hs : count305 q = (countLit q [157]) + (countLit q [158]) := List.countP_append (p := literal q) (l₁ := [157]) (l₂ := [158])
  have hm := merge_right (literal (valuationOf q) (158)) (literal (valuationOf q) (305)) (countLit q [157]) (countLit q [158]) (count305 q) 1 (meaning158 q) (meaning305 q) hs
  change valuationOf q 158 = false ∨ valuationOf q 305 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1063 (q : Snake 81) (h : Conditions q) : valuation q 158 = false ∨ valuation q 305 = true := counterClause1063 (baseVal q)

theorem counterClause1064 (q : Nat → Bool) : valuationOf q 305 = false ∨ valuationOf q 307 = true := by
  have hs : count307 q = (countLit q [155, 156]) + (countLit q [157, 158]) := List.countP_append (p := literal q) (l₁ := [155, 156]) (l₂ := [157, 158])
  have hm := merge_right (literal (valuationOf q) (305)) (literal (valuationOf q) (307)) (countLit q [155, 156]) (countLit q [157, 158]) (count307 q) 1 (meaning305 q) (meaning307 q) hs
  change valuationOf q 305 = false ∨ valuationOf q 307 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1064 (q : Snake 81) (h : Conditions q) : valuation q 305 = false ∨ valuation q 307 = true := counterClause1064 (baseVal q)

theorem counterClause1065 (q : Nat → Bool) : valuationOf q 303 = false ∨ valuationOf q 307 = true := by
  have hs : count307 q = (countLit q [155, 156]) + (countLit q [157, 158]) := List.countP_append (p := literal q) (l₁ := [155, 156]) (l₂ := [157, 158])
  have hm := merge_left (literal (valuationOf q) (303)) (literal (valuationOf q) (307)) (countLit q [155, 156]) (countLit q [157, 158]) (count307 q) 1 (meaning303 q) (meaning307 q) hs
  change valuationOf q 303 = false ∨ valuationOf q 307 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1065 (q : Snake 81) (h : Conditions q) : valuation q 303 = false ∨ valuation q 307 = true := counterClause1065 (baseVal q)

theorem counterClause1066 (q : Nat → Bool) : valuationOf q 307 = false ∨ valuationOf q 309 = true := by
  have hs : count309 q = (countLit q [151, 152, 153, 154]) + (countLit q [155, 156, 157, 158]) := List.countP_append (p := literal q) (l₁ := [151, 152, 153, 154]) (l₂ := [155, 156, 157, 158])
  have hm := merge_right (literal (valuationOf q) (307)) (literal (valuationOf q) (309)) (countLit q [151, 152, 153, 154]) (countLit q [155, 156, 157, 158]) (count309 q) 1 (meaning307 q) (meaning309 q) hs
  change valuationOf q 307 = false ∨ valuationOf q 309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1066 (q : Snake 81) (h : Conditions q) : valuation q 307 = false ∨ valuation q 309 = true := counterClause1066 (baseVal q)

theorem counterClause1067 (q : Nat → Bool) : valuationOf q 301 = false ∨ valuationOf q 309 = true := by
  have hs : count309 q = (countLit q [151, 152, 153, 154]) + (countLit q [155, 156, 157, 158]) := List.countP_append (p := literal q) (l₁ := [151, 152, 153, 154]) (l₂ := [155, 156, 157, 158])
  have hm := merge_left (literal (valuationOf q) (301)) (literal (valuationOf q) (309)) (countLit q [151, 152, 153, 154]) (countLit q [155, 156, 157, 158]) (count309 q) 1 (meaning301 q) (meaning309 q) hs
  change valuationOf q 301 = false ∨ valuationOf q 309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1067 (q : Snake 81) (h : Conditions q) : valuation q 301 = false ∨ valuation q 309 = true := counterClause1067 (baseVal q)

theorem counterClause1068 (q : Nat → Bool) : valuationOf q 309 = false ∨ valuationOf q 311 = true := by
  have hs : count311 q = (countLit q [143, 144, 145, 146, 147, 148, 149, 150]) + (countLit q [151, 152, 153, 154, 155, 156, 157, 158]) := List.countP_append (p := literal q) (l₁ := [143, 144, 145, 146, 147, 148, 149, 150]) (l₂ := [151, 152, 153, 154, 155, 156, 157, 158])
  have hm := merge_right (literal (valuationOf q) (309)) (literal (valuationOf q) (311)) (countLit q [143, 144, 145, 146, 147, 148, 149, 150]) (countLit q [151, 152, 153, 154, 155, 156, 157, 158]) (count311 q) 1 (meaning309 q) (meaning311 q) hs
  change valuationOf q 309 = false ∨ valuationOf q 311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1068 (q : Snake 81) (h : Conditions q) : valuation q 309 = false ∨ valuation q 311 = true := counterClause1068 (baseVal q)

theorem counterClause1069 (q : Nat → Bool) : valuationOf q 295 = false ∨ valuationOf q 311 = true := by
  have hs : count311 q = (countLit q [143, 144, 145, 146, 147, 148, 149, 150]) + (countLit q [151, 152, 153, 154, 155, 156, 157, 158]) := List.countP_append (p := literal q) (l₁ := [143, 144, 145, 146, 147, 148, 149, 150]) (l₂ := [151, 152, 153, 154, 155, 156, 157, 158])
  have hm := merge_left (literal (valuationOf q) (295)) (literal (valuationOf q) (311)) (countLit q [143, 144, 145, 146, 147, 148, 149, 150]) (countLit q [151, 152, 153, 154, 155, 156, 157, 158]) (count311 q) 1 (meaning295 q) (meaning311 q) hs
  change valuationOf q 295 = false ∨ valuationOf q 311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1069 (q : Snake 81) (h : Conditions q) : valuation q 295 = false ∨ valuation q 311 = true := counterClause1069 (baseVal q)

theorem counterClause1070 (q : Nat → Bool) : valuationOf q 295 = false ∨ valuationOf q 309 = false ∨ valuationOf q 312 = true := by
  have hs : count311 q = (countLit q [143, 144, 145, 146, 147, 148, 149, 150]) + (countLit q [151, 152, 153, 154, 155, 156, 157, 158]) := List.countP_append (p := literal q) (l₁ := [143, 144, 145, 146, 147, 148, 149, 150]) (l₂ := [151, 152, 153, 154, 155, 156, 157, 158])
  have hm := merge_two (literal (valuationOf q) (295)) (literal (valuationOf q) (309)) (literal (valuationOf q) (312)) (countLit q [143, 144, 145, 146, 147, 148, 149, 150]) (countLit q [151, 152, 153, 154, 155, 156, 157, 158]) (count311 q) 1 1 (meaning295 q) (meaning309 q) (meaning312 q) hs
  change valuationOf q 295 = false ∨ valuationOf q 309 = false ∨ valuationOf q 312 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1070 (q : Snake 81) (h : Conditions q) : valuation q 295 = false ∨ valuation q 309 = false ∨ valuation q 312 = true := counterClause1070 (baseVal q)

theorem counterClause1071 (q : Nat → Bool) : valuationOf q 296 = false ∨ valuationOf q 312 = true := by
  have hs : count311 q = (countLit q [143, 144, 145, 146, 147, 148, 149, 150]) + (countLit q [151, 152, 153, 154, 155, 156, 157, 158]) := List.countP_append (p := literal q) (l₁ := [143, 144, 145, 146, 147, 148, 149, 150]) (l₂ := [151, 152, 153, 154, 155, 156, 157, 158])
  have hm := merge_left (literal (valuationOf q) (296)) (literal (valuationOf q) (312)) (countLit q [143, 144, 145, 146, 147, 148, 149, 150]) (countLit q [151, 152, 153, 154, 155, 156, 157, 158]) (count311 q) 2 (meaning296 q) (meaning312 q) hs
  change valuationOf q 296 = false ∨ valuationOf q 312 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1071 (q : Snake 81) (h : Conditions q) : valuation q 296 = false ∨ valuation q 312 = true := counterClause1071 (baseVal q)

theorem counterClause1072 (q : Nat → Bool) : valuationOf q 311 = false ∨ valuationOf q 313 = true := by
  have hs : count313 q = (countLit q [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) + (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) := List.countP_append (p := literal q) (l₁ := [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (l₂ := [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158])
  have hm := merge_right (literal (valuationOf q) (311)) (literal (valuationOf q) (313)) (countLit q [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (count313 q) 1 (meaning311 q) (meaning313 q) hs
  change valuationOf q 311 = false ∨ valuationOf q 313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1072 (q : Snake 81) (h : Conditions q) : valuation q 311 = false ∨ valuation q 313 = true := counterClause1072 (baseVal q)

theorem counterClause1073 (q : Nat → Bool) : valuationOf q 312 = false ∨ valuationOf q 314 = true := by
  have hs : count313 q = (countLit q [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) + (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) := List.countP_append (p := literal q) (l₁ := [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (l₂ := [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158])
  have hm := merge_right (literal (valuationOf q) (312)) (literal (valuationOf q) (314)) (countLit q [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (count313 q) 2 (meaning312 q) (meaning314 q) hs
  change valuationOf q 312 = false ∨ valuationOf q 314 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1073 (q : Snake 81) (h : Conditions q) : valuation q 312 = false ∨ valuation q 314 = true := counterClause1073 (baseVal q)

theorem counterClause1074 (q : Nat → Bool) : valuationOf q 281 = false ∨ valuationOf q 313 = true := by
  have hs : count313 q = (countLit q [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) + (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) := List.countP_append (p := literal q) (l₁ := [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (l₂ := [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158])
  have hm := merge_left (literal (valuationOf q) (281)) (literal (valuationOf q) (313)) (countLit q [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (count313 q) 1 (meaning281 q) (meaning313 q) hs
  change valuationOf q 281 = false ∨ valuationOf q 313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1074 (q : Snake 81) (h : Conditions q) : valuation q 281 = false ∨ valuation q 313 = true := counterClause1074 (baseVal q)

theorem counterClause1075 (q : Nat → Bool) : valuationOf q 281 = false ∨ valuationOf q 311 = false ∨ valuationOf q 314 = true := by
  have hs : count313 q = (countLit q [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) + (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) := List.countP_append (p := literal q) (l₁ := [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (l₂ := [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158])
  have hm := merge_two (literal (valuationOf q) (281)) (literal (valuationOf q) (311)) (literal (valuationOf q) (314)) (countLit q [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (count313 q) 1 1 (meaning281 q) (meaning311 q) (meaning314 q) hs
  change valuationOf q 281 = false ∨ valuationOf q 311 = false ∨ valuationOf q 314 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1075 (q : Snake 81) (h : Conditions q) : valuation q 281 = false ∨ valuation q 311 = false ∨ valuation q 314 = true := counterClause1075 (baseVal q)

theorem counterClause1076 (q : Nat → Bool) : valuationOf q 282 = false ∨ valuationOf q 314 = true := by
  have hs : count313 q = (countLit q [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) + (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) := List.countP_append (p := literal q) (l₁ := [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (l₂ := [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158])
  have hm := merge_left (literal (valuationOf q) (282)) (literal (valuationOf q) (314)) (countLit q [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (count313 q) 2 (meaning282 q) (meaning314 q) hs
  change valuationOf q 282 = false ∨ valuationOf q 314 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1076 (q : Snake 81) (h : Conditions q) : valuation q 282 = false ∨ valuation q 314 = true := counterClause1076 (baseVal q)

theorem counterClause1077 (q : Nat → Bool) : valuationOf q 159 = false ∨ valuationOf q 315 = true := by
  have hs : count315 q = (countLit q [159]) + (countLit q [160]) := List.countP_append (p := literal q) (l₁ := [159]) (l₂ := [160])
  have hm := merge_left (literal (valuationOf q) (159)) (literal (valuationOf q) (315)) (countLit q [159]) (countLit q [160]) (count315 q) 1 (meaning159 q) (meaning315 q) hs
  change valuationOf q 159 = false ∨ valuationOf q 315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1077 (q : Snake 81) (h : Conditions q) : valuation q 159 = false ∨ valuation q 315 = true := counterClause1077 (baseVal q)

theorem counterClause1078 (q : Nat → Bool) : valuationOf q 161 = false ∨ valuationOf q 317 = true := by
  have hs : count317 q = (countLit q [161]) + (countLit q [162]) := List.countP_append (p := literal q) (l₁ := [161]) (l₂ := [162])
  have hm := merge_left (literal (valuationOf q) (161)) (literal (valuationOf q) (317)) (countLit q [161]) (countLit q [162]) (count317 q) 1 (meaning161 q) (meaning317 q) hs
  change valuationOf q 161 = false ∨ valuationOf q 317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1078 (q : Snake 81) (h : Conditions q) : valuation q 161 = false ∨ valuation q 317 = true := counterClause1078 (baseVal q)

theorem counterClause1079 (q : Nat → Bool) : valuationOf q 317 = false ∨ valuationOf q 319 = true := by
  have hs : count319 q = (countLit q [159, 160]) + (countLit q [161, 162]) := List.countP_append (p := literal q) (l₁ := [159, 160]) (l₂ := [161, 162])
  have hm := merge_right (literal (valuationOf q) (317)) (literal (valuationOf q) (319)) (countLit q [159, 160]) (countLit q [161, 162]) (count319 q) 1 (meaning317 q) (meaning319 q) hs
  change valuationOf q 317 = false ∨ valuationOf q 319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1079 (q : Snake 81) (h : Conditions q) : valuation q 317 = false ∨ valuation q 319 = true := counterClause1079 (baseVal q)

theorem counterClause1080 (q : Nat → Bool) : valuationOf q 315 = false ∨ valuationOf q 319 = true := by
  have hs : count319 q = (countLit q [159, 160]) + (countLit q [161, 162]) := List.countP_append (p := literal q) (l₁ := [159, 160]) (l₂ := [161, 162])
  have hm := merge_left (literal (valuationOf q) (315)) (literal (valuationOf q) (319)) (countLit q [159, 160]) (countLit q [161, 162]) (count319 q) 1 (meaning315 q) (meaning319 q) hs
  change valuationOf q 315 = false ∨ valuationOf q 319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1080 (q : Snake 81) (h : Conditions q) : valuation q 315 = false ∨ valuation q 319 = true := counterClause1080 (baseVal q)

theorem counterClause1081 (q : Nat → Bool) : valuationOf q 164 = false ∨ valuationOf q 321 = true := by
  have hs : count321 q = (countLit q [163]) + (countLit q [164]) := List.countP_append (p := literal q) (l₁ := [163]) (l₂ := [164])
  have hm := merge_right (literal (valuationOf q) (164)) (literal (valuationOf q) (321)) (countLit q [163]) (countLit q [164]) (count321 q) 1 (meaning164 q) (meaning321 q) hs
  change valuationOf q 164 = false ∨ valuationOf q 321 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1081 (q : Snake 81) (h : Conditions q) : valuation q 164 = false ∨ valuation q 321 = true := counterClause1081 (baseVal q)

theorem counterClause1082 (q : Nat → Bool) : valuationOf q 165 = false ∨ valuationOf q 323 = true := by
  have hs : count323 q = (countLit q [165]) + (countLit q [166]) := List.countP_append (p := literal q) (l₁ := [165]) (l₂ := [166])
  have hm := merge_left (literal (valuationOf q) (165)) (literal (valuationOf q) (323)) (countLit q [165]) (countLit q [166]) (count323 q) 1 (meaning165 q) (meaning323 q) hs
  change valuationOf q 165 = false ∨ valuationOf q 323 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1082 (q : Snake 81) (h : Conditions q) : valuation q 165 = false ∨ valuation q 323 = true := counterClause1082 (baseVal q)

theorem counterClause1083 (q : Nat → Bool) : valuationOf q 323 = false ∨ valuationOf q 325 = true := by
  have hs : count325 q = (countLit q [163, 164]) + (countLit q [165, 166]) := List.countP_append (p := literal q) (l₁ := [163, 164]) (l₂ := [165, 166])
  have hm := merge_right (literal (valuationOf q) (323)) (literal (valuationOf q) (325)) (countLit q [163, 164]) (countLit q [165, 166]) (count325 q) 1 (meaning323 q) (meaning325 q) hs
  change valuationOf q 323 = false ∨ valuationOf q 325 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1083 (q : Snake 81) (h : Conditions q) : valuation q 323 = false ∨ valuation q 325 = true := counterClause1083 (baseVal q)

theorem counterClause1084 (q : Nat → Bool) : valuationOf q 321 = false ∨ valuationOf q 325 = true := by
  have hs : count325 q = (countLit q [163, 164]) + (countLit q [165, 166]) := List.countP_append (p := literal q) (l₁ := [163, 164]) (l₂ := [165, 166])
  have hm := merge_left (literal (valuationOf q) (321)) (literal (valuationOf q) (325)) (countLit q [163, 164]) (countLit q [165, 166]) (count325 q) 1 (meaning321 q) (meaning325 q) hs
  change valuationOf q 321 = false ∨ valuationOf q 325 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1084 (q : Snake 81) (h : Conditions q) : valuation q 321 = false ∨ valuation q 325 = true := counterClause1084 (baseVal q)

theorem counterClause1085 (q : Nat → Bool) : valuationOf q 325 = false ∨ valuationOf q 327 = true := by
  have hs : count327 q = (countLit q [159, 160, 161, 162]) + (countLit q [163, 164, 165, 166]) := List.countP_append (p := literal q) (l₁ := [159, 160, 161, 162]) (l₂ := [163, 164, 165, 166])
  have hm := merge_right (literal (valuationOf q) (325)) (literal (valuationOf q) (327)) (countLit q [159, 160, 161, 162]) (countLit q [163, 164, 165, 166]) (count327 q) 1 (meaning325 q) (meaning327 q) hs
  change valuationOf q 325 = false ∨ valuationOf q 327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1085 (q : Snake 81) (h : Conditions q) : valuation q 325 = false ∨ valuation q 327 = true := counterClause1085 (baseVal q)

theorem counterClause1086 (q : Nat → Bool) : valuationOf q 319 = false ∨ valuationOf q 327 = true := by
  have hs : count327 q = (countLit q [159, 160, 161, 162]) + (countLit q [163, 164, 165, 166]) := List.countP_append (p := literal q) (l₁ := [159, 160, 161, 162]) (l₂ := [163, 164, 165, 166])
  have hm := merge_left (literal (valuationOf q) (319)) (literal (valuationOf q) (327)) (countLit q [159, 160, 161, 162]) (countLit q [163, 164, 165, 166]) (count327 q) 1 (meaning319 q) (meaning327 q) hs
  change valuationOf q 319 = false ∨ valuationOf q 327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1086 (q : Snake 81) (h : Conditions q) : valuation q 319 = false ∨ valuation q 327 = true := counterClause1086 (baseVal q)

theorem counterClause1087 (q : Nat → Bool) : valuationOf q 168 = false ∨ valuationOf q 329 = true := by
  have hs : count329 q = (countLit q [167]) + (countLit q [168]) := List.countP_append (p := literal q) (l₁ := [167]) (l₂ := [168])
  have hm := merge_right (literal (valuationOf q) (168)) (literal (valuationOf q) (329)) (countLit q [167]) (countLit q [168]) (count329 q) 1 (meaning168 q) (meaning329 q) hs
  change valuationOf q 168 = false ∨ valuationOf q 329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1087 (q : Snake 81) (h : Conditions q) : valuation q 168 = false ∨ valuation q 329 = true := counterClause1087 (baseVal q)

theorem counterClause1088 (q : Nat → Bool) : valuationOf q 167 = false ∨ valuationOf q 329 = true := by
  have hs : count329 q = (countLit q [167]) + (countLit q [168]) := List.countP_append (p := literal q) (l₁ := [167]) (l₂ := [168])
  have hm := merge_left (literal (valuationOf q) (167)) (literal (valuationOf q) (329)) (countLit q [167]) (countLit q [168]) (count329 q) 1 (meaning167 q) (meaning329 q) hs
  change valuationOf q 167 = false ∨ valuationOf q 329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1088 (q : Snake 81) (h : Conditions q) : valuation q 167 = false ∨ valuation q 329 = true := counterClause1088 (baseVal q)

theorem block33 (q : Snake 81) (h : Conditions q) : B112E057.Block33 (valuation q) :=
  ⟨clause1057 q h, clause1058 q h, clause1059 q h, clause1060 q h, clause1061 q h, clause1062 q h, clause1063 q h, clause1064 q h, clause1065 q h, clause1066 q h, clause1067 q h, clause1068 q h, clause1069 q h, clause1070 q h, clause1071 q h, clause1072 q h, clause1073 q h, clause1074 q h, clause1075 q h, clause1076 q h, clause1077 q h, clause1078 q h, clause1079 q h, clause1080 q h, clause1081 q h, clause1082 q h, clause1083 q h, clause1084 q h, clause1085 q h, clause1086 q h, clause1087 q h, clause1088 q h⟩

end
end Snake9.Regrowth.E112057
