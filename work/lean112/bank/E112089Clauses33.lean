import E112089Semantics
import B112E089Inputs
namespace Snake9.Regrowth.E112089
noncomputable section
local instance blockDec33 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1057 (q : Nat → Bool) : valuationOf q 272 = false ∨ valuationOf q 274 = true := by
  have hs : count273 q = (countLit q [132, 133, 134, 135]) + (countLit q [136, 137, 138, 139]) := List.countP_append (p := literal q) (l₁ := [132, 133, 134, 135]) (l₂ := [136, 137, 138, 139])
  have hm := merge_right (literal (valuationOf q) (272)) (literal (valuationOf q) (274)) (countLit q [132, 133, 134, 135]) (countLit q [136, 137, 138, 139]) (count273 q) 2 (meaning272 q) (meaning274 q) hs
  change valuationOf q 272 = false ∨ valuationOf q 274 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1057 (q : Snake 81) (h : Conditions q) : valuation q 272 = false ∨ valuation q 274 = true := counterClause1057 (baseVal q)

theorem counterClause1058 (q : Nat → Bool) : valuationOf q 265 = false ∨ valuationOf q 273 = true := by
  have hs : count273 q = (countLit q [132, 133, 134, 135]) + (countLit q [136, 137, 138, 139]) := List.countP_append (p := literal q) (l₁ := [132, 133, 134, 135]) (l₂ := [136, 137, 138, 139])
  have hm := merge_left (literal (valuationOf q) (265)) (literal (valuationOf q) (273)) (countLit q [132, 133, 134, 135]) (countLit q [136, 137, 138, 139]) (count273 q) 1 (meaning265 q) (meaning273 q) hs
  change valuationOf q 265 = false ∨ valuationOf q 273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1058 (q : Snake 81) (h : Conditions q) : valuation q 265 = false ∨ valuation q 273 = true := counterClause1058 (baseVal q)

theorem counterClause1059 (q : Nat → Bool) : valuationOf q 265 = false ∨ valuationOf q 271 = false ∨ valuationOf q 274 = true := by
  have hs : count273 q = (countLit q [132, 133, 134, 135]) + (countLit q [136, 137, 138, 139]) := List.countP_append (p := literal q) (l₁ := [132, 133, 134, 135]) (l₂ := [136, 137, 138, 139])
  have hm := merge_two (literal (valuationOf q) (265)) (literal (valuationOf q) (271)) (literal (valuationOf q) (274)) (countLit q [132, 133, 134, 135]) (countLit q [136, 137, 138, 139]) (count273 q) 1 1 (meaning265 q) (meaning271 q) (meaning274 q) hs
  change valuationOf q 265 = false ∨ valuationOf q 271 = false ∨ valuationOf q 274 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1059 (q : Snake 81) (h : Conditions q) : valuation q 265 = false ∨ valuation q 271 = false ∨ valuation q 274 = true := counterClause1059 (baseVal q)

theorem counterClause1060 (q : Nat → Bool) : valuationOf q 266 = false ∨ valuationOf q 274 = true := by
  have hs : count273 q = (countLit q [132, 133, 134, 135]) + (countLit q [136, 137, 138, 139]) := List.countP_append (p := literal q) (l₁ := [132, 133, 134, 135]) (l₂ := [136, 137, 138, 139])
  have hm := merge_left (literal (valuationOf q) (266)) (literal (valuationOf q) (274)) (countLit q [132, 133, 134, 135]) (countLit q [136, 137, 138, 139]) (count273 q) 2 (meaning266 q) (meaning274 q) hs
  change valuationOf q 266 = false ∨ valuationOf q 274 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1060 (q : Snake 81) (h : Conditions q) : valuation q 266 = false ∨ valuation q 274 = true := counterClause1060 (baseVal q)

theorem counterClause1061 (q : Nat → Bool) : valuationOf q 273 = false ∨ valuationOf q 275 = true := by
  have hs : count275 q = (countLit q [125, 126, 127, 128, 129, 130, 131]) + (countLit q [132, 133, 134, 135, 136, 137, 138, 139]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 130, 131]) (l₂ := [132, 133, 134, 135, 136, 137, 138, 139])
  have hm := merge_right (literal (valuationOf q) (273)) (literal (valuationOf q) (275)) (countLit q [125, 126, 127, 128, 129, 130, 131]) (countLit q [132, 133, 134, 135, 136, 137, 138, 139]) (count275 q) 1 (meaning273 q) (meaning275 q) hs
  change valuationOf q 273 = false ∨ valuationOf q 275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1061 (q : Snake 81) (h : Conditions q) : valuation q 273 = false ∨ valuation q 275 = true := counterClause1061 (baseVal q)

theorem counterClause1062 (q : Nat → Bool) : valuationOf q 274 = false ∨ valuationOf q 276 = true := by
  have hs : count275 q = (countLit q [125, 126, 127, 128, 129, 130, 131]) + (countLit q [132, 133, 134, 135, 136, 137, 138, 139]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 130, 131]) (l₂ := [132, 133, 134, 135, 136, 137, 138, 139])
  have hm := merge_right (literal (valuationOf q) (274)) (literal (valuationOf q) (276)) (countLit q [125, 126, 127, 128, 129, 130, 131]) (countLit q [132, 133, 134, 135, 136, 137, 138, 139]) (count275 q) 2 (meaning274 q) (meaning276 q) hs
  change valuationOf q 274 = false ∨ valuationOf q 276 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1062 (q : Snake 81) (h : Conditions q) : valuation q 274 = false ∨ valuation q 276 = true := counterClause1062 (baseVal q)

theorem counterClause1063 (q : Nat → Bool) : valuationOf q 259 = false ∨ valuationOf q 275 = true := by
  have hs : count275 q = (countLit q [125, 126, 127, 128, 129, 130, 131]) + (countLit q [132, 133, 134, 135, 136, 137, 138, 139]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 130, 131]) (l₂ := [132, 133, 134, 135, 136, 137, 138, 139])
  have hm := merge_left (literal (valuationOf q) (259)) (literal (valuationOf q) (275)) (countLit q [125, 126, 127, 128, 129, 130, 131]) (countLit q [132, 133, 134, 135, 136, 137, 138, 139]) (count275 q) 1 (meaning259 q) (meaning275 q) hs
  change valuationOf q 259 = false ∨ valuationOf q 275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1063 (q : Snake 81) (h : Conditions q) : valuation q 259 = false ∨ valuation q 275 = true := counterClause1063 (baseVal q)

theorem counterClause1064 (q : Nat → Bool) : valuationOf q 259 = false ∨ valuationOf q 273 = false ∨ valuationOf q 276 = true := by
  have hs : count275 q = (countLit q [125, 126, 127, 128, 129, 130, 131]) + (countLit q [132, 133, 134, 135, 136, 137, 138, 139]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 130, 131]) (l₂ := [132, 133, 134, 135, 136, 137, 138, 139])
  have hm := merge_two (literal (valuationOf q) (259)) (literal (valuationOf q) (273)) (literal (valuationOf q) (276)) (countLit q [125, 126, 127, 128, 129, 130, 131]) (countLit q [132, 133, 134, 135, 136, 137, 138, 139]) (count275 q) 1 1 (meaning259 q) (meaning273 q) (meaning276 q) hs
  change valuationOf q 259 = false ∨ valuationOf q 273 = false ∨ valuationOf q 276 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1064 (q : Snake 81) (h : Conditions q) : valuation q 259 = false ∨ valuation q 273 = false ∨ valuation q 276 = true := counterClause1064 (baseVal q)

theorem counterClause1065 (q : Nat → Bool) : valuationOf q 142 = false ∨ valuationOf q 277 = true := by
  have hs : count277 q = (countLit q [141]) + (countLit q [142]) := List.countP_append (p := literal q) (l₁ := [141]) (l₂ := [142])
  have hm := merge_right (literal (valuationOf q) (142)) (literal (valuationOf q) (277)) (countLit q [141]) (countLit q [142]) (count277 q) 1 (meaning142 q) (meaning277 q) hs
  change valuationOf q 142 = false ∨ valuationOf q 277 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1065 (q : Snake 81) (h : Conditions q) : valuation q 142 = false ∨ valuation q 277 = true := counterClause1065 (baseVal q)

theorem counterClause1066 (q : Nat → Bool) : valuationOf q 277 = false ∨ valuationOf q 279 = true := by
  have hs : count279 q = (countLit q [140]) + (countLit q [141, 142]) := List.countP_append (p := literal q) (l₁ := [140]) (l₂ := [141, 142])
  have hm := merge_right (literal (valuationOf q) (277)) (literal (valuationOf q) (279)) (countLit q [140]) (countLit q [141, 142]) (count279 q) 1 (meaning277 q) (meaning279 q) hs
  change valuationOf q 277 = false ∨ valuationOf q 279 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1066 (q : Snake 81) (h : Conditions q) : valuation q 277 = false ∨ valuation q 279 = true := counterClause1066 (baseVal q)

theorem counterClause1067 (q : Nat → Bool) : valuationOf q 146 = false ∨ valuationOf q 283 = true := by
  have hs : count283 q = (countLit q [145]) + (countLit q [146]) := List.countP_append (p := literal q) (l₁ := [145]) (l₂ := [146])
  have hm := merge_right (literal (valuationOf q) (146)) (literal (valuationOf q) (283)) (countLit q [145]) (countLit q [146]) (count283 q) 1 (meaning146 q) (meaning283 q) hs
  change valuationOf q 146 = false ∨ valuationOf q 283 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1067 (q : Snake 81) (h : Conditions q) : valuation q 146 = false ∨ valuation q 283 = true := counterClause1067 (baseVal q)

theorem counterClause1068 (q : Nat → Bool) : valuationOf q 283 = false ∨ valuationOf q 285 = true := by
  have hs : count285 q = (countLit q [143, 144]) + (countLit q [145, 146]) := List.countP_append (p := literal q) (l₁ := [143, 144]) (l₂ := [145, 146])
  have hm := merge_right (literal (valuationOf q) (283)) (literal (valuationOf q) (285)) (countLit q [143, 144]) (countLit q [145, 146]) (count285 q) 1 (meaning283 q) (meaning285 q) hs
  change valuationOf q 283 = false ∨ valuationOf q 285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1068 (q : Snake 81) (h : Conditions q) : valuation q 283 = false ∨ valuation q 285 = true := counterClause1068 (baseVal q)

theorem counterClause1069 (q : Nat → Bool) : valuationOf q 285 = false ∨ valuationOf q 287 = true := by
  have hs : count287 q = (countLit q [140, 141, 142]) + (countLit q [143, 144, 145, 146]) := List.countP_append (p := literal q) (l₁ := [140, 141, 142]) (l₂ := [143, 144, 145, 146])
  have hm := merge_right (literal (valuationOf q) (285)) (literal (valuationOf q) (287)) (countLit q [140, 141, 142]) (countLit q [143, 144, 145, 146]) (count287 q) 1 (meaning285 q) (meaning287 q) hs
  change valuationOf q 285 = false ∨ valuationOf q 287 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1069 (q : Snake 81) (h : Conditions q) : valuation q 285 = false ∨ valuation q 287 = true := counterClause1069 (baseVal q)

theorem counterClause1070 (q : Nat → Bool) : valuationOf q 279 = false ∨ valuationOf q 287 = true := by
  have hs : count287 q = (countLit q [140, 141, 142]) + (countLit q [143, 144, 145, 146]) := List.countP_append (p := literal q) (l₁ := [140, 141, 142]) (l₂ := [143, 144, 145, 146])
  have hm := merge_left (literal (valuationOf q) (279)) (literal (valuationOf q) (287)) (countLit q [140, 141, 142]) (countLit q [143, 144, 145, 146]) (count287 q) 1 (meaning279 q) (meaning287 q) hs
  change valuationOf q 279 = false ∨ valuationOf q 287 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1070 (q : Snake 81) (h : Conditions q) : valuation q 279 = false ∨ valuation q 287 = true := counterClause1070 (baseVal q)

theorem counterClause1071 (q : Nat → Bool) : valuationOf q 148 = false ∨ valuationOf q 289 = true := by
  have hs : count289 q = (countLit q [147]) + (countLit q [148]) := List.countP_append (p := literal q) (l₁ := [147]) (l₂ := [148])
  have hm := merge_right (literal (valuationOf q) (148)) (literal (valuationOf q) (289)) (countLit q [147]) (countLit q [148]) (count289 q) 1 (meaning148 q) (meaning289 q) hs
  change valuationOf q 148 = false ∨ valuationOf q 289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1071 (q : Snake 81) (h : Conditions q) : valuation q 148 = false ∨ valuation q 289 = true := counterClause1071 (baseVal q)

theorem counterClause1072 (q : Nat → Bool) : valuationOf q 149 = false ∨ valuationOf q 291 = true := by
  have hs : count291 q = (countLit q [149]) + (countLit q [150]) := List.countP_append (p := literal q) (l₁ := [149]) (l₂ := [150])
  have hm := merge_left (literal (valuationOf q) (149)) (literal (valuationOf q) (291)) (countLit q [149]) (countLit q [150]) (count291 q) 1 (meaning149 q) (meaning291 q) hs
  change valuationOf q 149 = false ∨ valuationOf q 291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1072 (q : Snake 81) (h : Conditions q) : valuation q 149 = false ∨ valuation q 291 = true := counterClause1072 (baseVal q)

theorem counterClause1073 (q : Nat → Bool) : valuationOf q 291 = false ∨ valuationOf q 293 = true := by
  have hs : count293 q = (countLit q [147, 148]) + (countLit q [149, 150]) := List.countP_append (p := literal q) (l₁ := [147, 148]) (l₂ := [149, 150])
  have hm := merge_right (literal (valuationOf q) (291)) (literal (valuationOf q) (293)) (countLit q [147, 148]) (countLit q [149, 150]) (count293 q) 1 (meaning291 q) (meaning293 q) hs
  change valuationOf q 291 = false ∨ valuationOf q 293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1073 (q : Snake 81) (h : Conditions q) : valuation q 291 = false ∨ valuation q 293 = true := counterClause1073 (baseVal q)

theorem counterClause1074 (q : Nat → Bool) : valuationOf q 289 = false ∨ valuationOf q 293 = true := by
  have hs : count293 q = (countLit q [147, 148]) + (countLit q [149, 150]) := List.countP_append (p := literal q) (l₁ := [147, 148]) (l₂ := [149, 150])
  have hm := merge_left (literal (valuationOf q) (289)) (literal (valuationOf q) (293)) (countLit q [147, 148]) (countLit q [149, 150]) (count293 q) 1 (meaning289 q) (meaning293 q) hs
  change valuationOf q 289 = false ∨ valuationOf q 293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1074 (q : Snake 81) (h : Conditions q) : valuation q 289 = false ∨ valuation q 293 = true := counterClause1074 (baseVal q)

theorem counterClause1075 (q : Nat → Bool) : valuationOf q 151 = false ∨ valuationOf q 295 = true := by
  have hs : count295 q = (countLit q [151]) + (countLit q [152]) := List.countP_append (p := literal q) (l₁ := [151]) (l₂ := [152])
  have hm := merge_left (literal (valuationOf q) (151)) (literal (valuationOf q) (295)) (countLit q [151]) (countLit q [152]) (count295 q) 1 (meaning151 q) (meaning295 q) hs
  change valuationOf q 151 = false ∨ valuationOf q 295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1075 (q : Snake 81) (h : Conditions q) : valuation q 151 = false ∨ valuation q 295 = true := counterClause1075 (baseVal q)

theorem counterClause1076 (q : Nat → Bool) : valuationOf q 153 = false ∨ valuationOf q 297 = true := by
  have hs : count297 q = (countLit q [153]) + (countLit q [154]) := List.countP_append (p := literal q) (l₁ := [153]) (l₂ := [154])
  have hm := merge_left (literal (valuationOf q) (153)) (literal (valuationOf q) (297)) (countLit q [153]) (countLit q [154]) (count297 q) 1 (meaning153 q) (meaning297 q) hs
  change valuationOf q 153 = false ∨ valuationOf q 297 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1076 (q : Snake 81) (h : Conditions q) : valuation q 153 = false ∨ valuation q 297 = true := counterClause1076 (baseVal q)

theorem counterClause1077 (q : Nat → Bool) : valuationOf q 297 = false ∨ valuationOf q 299 = true := by
  have hs : count299 q = (countLit q [151, 152]) + (countLit q [153, 154]) := List.countP_append (p := literal q) (l₁ := [151, 152]) (l₂ := [153, 154])
  have hm := merge_right (literal (valuationOf q) (297)) (literal (valuationOf q) (299)) (countLit q [151, 152]) (countLit q [153, 154]) (count299 q) 1 (meaning297 q) (meaning299 q) hs
  change valuationOf q 297 = false ∨ valuationOf q 299 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1077 (q : Snake 81) (h : Conditions q) : valuation q 297 = false ∨ valuation q 299 = true := counterClause1077 (baseVal q)

theorem counterClause1078 (q : Nat → Bool) : valuationOf q 295 = false ∨ valuationOf q 299 = true := by
  have hs : count299 q = (countLit q [151, 152]) + (countLit q [153, 154]) := List.countP_append (p := literal q) (l₁ := [151, 152]) (l₂ := [153, 154])
  have hm := merge_left (literal (valuationOf q) (295)) (literal (valuationOf q) (299)) (countLit q [151, 152]) (countLit q [153, 154]) (count299 q) 1 (meaning295 q) (meaning299 q) hs
  change valuationOf q 295 = false ∨ valuationOf q 299 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1078 (q : Snake 81) (h : Conditions q) : valuation q 295 = false ∨ valuation q 299 = true := counterClause1078 (baseVal q)

theorem counterClause1079 (q : Nat → Bool) : valuationOf q 295 = false ∨ valuationOf q 297 = false ∨ valuationOf q 300 = true := by
  have hs : count299 q = (countLit q [151, 152]) + (countLit q [153, 154]) := List.countP_append (p := literal q) (l₁ := [151, 152]) (l₂ := [153, 154])
  have hm := merge_two (literal (valuationOf q) (295)) (literal (valuationOf q) (297)) (literal (valuationOf q) (300)) (countLit q [151, 152]) (countLit q [153, 154]) (count299 q) 1 1 (meaning295 q) (meaning297 q) (meaning300 q) hs
  change valuationOf q 295 = false ∨ valuationOf q 297 = false ∨ valuationOf q 300 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1079 (q : Snake 81) (h : Conditions q) : valuation q 295 = false ∨ valuation q 297 = false ∨ valuation q 300 = true := counterClause1079 (baseVal q)

theorem counterClause1080 (q : Nat → Bool) : valuationOf q 299 = false ∨ valuationOf q 301 = true := by
  have hs : count301 q = (countLit q [147, 148, 149, 150]) + (countLit q [151, 152, 153, 154]) := List.countP_append (p := literal q) (l₁ := [147, 148, 149, 150]) (l₂ := [151, 152, 153, 154])
  have hm := merge_right (literal (valuationOf q) (299)) (literal (valuationOf q) (301)) (countLit q [147, 148, 149, 150]) (countLit q [151, 152, 153, 154]) (count301 q) 1 (meaning299 q) (meaning301 q) hs
  change valuationOf q 299 = false ∨ valuationOf q 301 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1080 (q : Snake 81) (h : Conditions q) : valuation q 299 = false ∨ valuation q 301 = true := counterClause1080 (baseVal q)

theorem counterClause1081 (q : Nat → Bool) : valuationOf q 300 = false ∨ valuationOf q 302 = true := by
  have hs : count301 q = (countLit q [147, 148, 149, 150]) + (countLit q [151, 152, 153, 154]) := List.countP_append (p := literal q) (l₁ := [147, 148, 149, 150]) (l₂ := [151, 152, 153, 154])
  have hm := merge_right (literal (valuationOf q) (300)) (literal (valuationOf q) (302)) (countLit q [147, 148, 149, 150]) (countLit q [151, 152, 153, 154]) (count301 q) 2 (meaning300 q) (meaning302 q) hs
  change valuationOf q 300 = false ∨ valuationOf q 302 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1081 (q : Snake 81) (h : Conditions q) : valuation q 300 = false ∨ valuation q 302 = true := counterClause1081 (baseVal q)

theorem counterClause1082 (q : Nat → Bool) : valuationOf q 293 = false ∨ valuationOf q 301 = true := by
  have hs : count301 q = (countLit q [147, 148, 149, 150]) + (countLit q [151, 152, 153, 154]) := List.countP_append (p := literal q) (l₁ := [147, 148, 149, 150]) (l₂ := [151, 152, 153, 154])
  have hm := merge_left (literal (valuationOf q) (293)) (literal (valuationOf q) (301)) (countLit q [147, 148, 149, 150]) (countLit q [151, 152, 153, 154]) (count301 q) 1 (meaning293 q) (meaning301 q) hs
  change valuationOf q 293 = false ∨ valuationOf q 301 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1082 (q : Snake 81) (h : Conditions q) : valuation q 293 = false ∨ valuation q 301 = true := counterClause1082 (baseVal q)

theorem counterClause1083 (q : Nat → Bool) : valuationOf q 293 = false ∨ valuationOf q 299 = false ∨ valuationOf q 302 = true := by
  have hs : count301 q = (countLit q [147, 148, 149, 150]) + (countLit q [151, 152, 153, 154]) := List.countP_append (p := literal q) (l₁ := [147, 148, 149, 150]) (l₂ := [151, 152, 153, 154])
  have hm := merge_two (literal (valuationOf q) (293)) (literal (valuationOf q) (299)) (literal (valuationOf q) (302)) (countLit q [147, 148, 149, 150]) (countLit q [151, 152, 153, 154]) (count301 q) 1 1 (meaning293 q) (meaning299 q) (meaning302 q) hs
  change valuationOf q 293 = false ∨ valuationOf q 299 = false ∨ valuationOf q 302 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1083 (q : Snake 81) (h : Conditions q) : valuation q 293 = false ∨ valuation q 299 = false ∨ valuation q 302 = true := counterClause1083 (baseVal q)

theorem counterClause1084 (q : Nat → Bool) : valuationOf q 301 = false ∨ valuationOf q 303 = true := by
  have hs : count303 q = (countLit q [140, 141, 142, 143, 144, 145, 146]) + (countLit q [147, 148, 149, 150, 151, 152, 153, 154]) := List.countP_append (p := literal q) (l₁ := [140, 141, 142, 143, 144, 145, 146]) (l₂ := [147, 148, 149, 150, 151, 152, 153, 154])
  have hm := merge_right (literal (valuationOf q) (301)) (literal (valuationOf q) (303)) (countLit q [140, 141, 142, 143, 144, 145, 146]) (countLit q [147, 148, 149, 150, 151, 152, 153, 154]) (count303 q) 1 (meaning301 q) (meaning303 q) hs
  change valuationOf q 301 = false ∨ valuationOf q 303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1084 (q : Snake 81) (h : Conditions q) : valuation q 301 = false ∨ valuation q 303 = true := counterClause1084 (baseVal q)

theorem counterClause1085 (q : Nat → Bool) : valuationOf q 302 = false ∨ valuationOf q 304 = true := by
  have hs : count303 q = (countLit q [140, 141, 142, 143, 144, 145, 146]) + (countLit q [147, 148, 149, 150, 151, 152, 153, 154]) := List.countP_append (p := literal q) (l₁ := [140, 141, 142, 143, 144, 145, 146]) (l₂ := [147, 148, 149, 150, 151, 152, 153, 154])
  have hm := merge_right (literal (valuationOf q) (302)) (literal (valuationOf q) (304)) (countLit q [140, 141, 142, 143, 144, 145, 146]) (countLit q [147, 148, 149, 150, 151, 152, 153, 154]) (count303 q) 2 (meaning302 q) (meaning304 q) hs
  change valuationOf q 302 = false ∨ valuationOf q 304 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1085 (q : Snake 81) (h : Conditions q) : valuation q 302 = false ∨ valuation q 304 = true := counterClause1085 (baseVal q)

theorem counterClause1086 (q : Nat → Bool) : valuationOf q 287 = false ∨ valuationOf q 303 = true := by
  have hs : count303 q = (countLit q [140, 141, 142, 143, 144, 145, 146]) + (countLit q [147, 148, 149, 150, 151, 152, 153, 154]) := List.countP_append (p := literal q) (l₁ := [140, 141, 142, 143, 144, 145, 146]) (l₂ := [147, 148, 149, 150, 151, 152, 153, 154])
  have hm := merge_left (literal (valuationOf q) (287)) (literal (valuationOf q) (303)) (countLit q [140, 141, 142, 143, 144, 145, 146]) (countLit q [147, 148, 149, 150, 151, 152, 153, 154]) (count303 q) 1 (meaning287 q) (meaning303 q) hs
  change valuationOf q 287 = false ∨ valuationOf q 303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1086 (q : Snake 81) (h : Conditions q) : valuation q 287 = false ∨ valuation q 303 = true := counterClause1086 (baseVal q)

theorem counterClause1087 (q : Nat → Bool) : valuationOf q 287 = false ∨ valuationOf q 301 = false ∨ valuationOf q 304 = true := by
  have hs : count303 q = (countLit q [140, 141, 142, 143, 144, 145, 146]) + (countLit q [147, 148, 149, 150, 151, 152, 153, 154]) := List.countP_append (p := literal q) (l₁ := [140, 141, 142, 143, 144, 145, 146]) (l₂ := [147, 148, 149, 150, 151, 152, 153, 154])
  have hm := merge_two (literal (valuationOf q) (287)) (literal (valuationOf q) (301)) (literal (valuationOf q) (304)) (countLit q [140, 141, 142, 143, 144, 145, 146]) (countLit q [147, 148, 149, 150, 151, 152, 153, 154]) (count303 q) 1 1 (meaning287 q) (meaning301 q) (meaning304 q) hs
  change valuationOf q 287 = false ∨ valuationOf q 301 = false ∨ valuationOf q 304 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1087 (q : Snake 81) (h : Conditions q) : valuation q 287 = false ∨ valuation q 301 = false ∨ valuation q 304 = true := counterClause1087 (baseVal q)

theorem counterClause1088 (q : Nat → Bool) : valuationOf q 303 = false ∨ valuationOf q 305 = true := by
  have hs : count305 q = (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139]) + (countLit q [140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139]) (l₂ := [140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154])
  have hm := merge_right (literal (valuationOf q) (303)) (literal (valuationOf q) (305)) (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139]) (countLit q [140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154]) (count305 q) 1 (meaning303 q) (meaning305 q) hs
  change valuationOf q 303 = false ∨ valuationOf q 305 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1088 (q : Snake 81) (h : Conditions q) : valuation q 303 = false ∨ valuation q 305 = true := counterClause1088 (baseVal q)

theorem block33 (q : Snake 81) (h : Conditions q) : B112E089.Block33 (valuation q) :=
  ⟨clause1057 q h, clause1058 q h, clause1059 q h, clause1060 q h, clause1061 q h, clause1062 q h, clause1063 q h, clause1064 q h, clause1065 q h, clause1066 q h, clause1067 q h, clause1068 q h, clause1069 q h, clause1070 q h, clause1071 q h, clause1072 q h, clause1073 q h, clause1074 q h, clause1075 q h, clause1076 q h, clause1077 q h, clause1078 q h, clause1079 q h, clause1080 q h, clause1081 q h, clause1082 q h, clause1083 q h, clause1084 q h, clause1085 q h, clause1086 q h, clause1087 q h, clause1088 q h⟩

end
end Snake9.Regrowth.E112089
