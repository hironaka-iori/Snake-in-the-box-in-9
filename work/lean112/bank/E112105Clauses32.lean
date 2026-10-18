import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec32 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1025 (q : Nat → Bool) : valuationOf q 273 = false ∨ valuationOf q 275 = true := by
  have hs : count275 q = (countLit q [125, 126, 127, 128, 129, 130, 131]) + (countLit q [132, 134, 135, 136, 137, 138, 139, 140]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 130, 131]) (l₂ := [132, 134, 135, 136, 137, 138, 139, 140])
  have hm := merge_right (literal (valuationOf q) (273)) (literal (valuationOf q) (275)) (countLit q [125, 126, 127, 128, 129, 130, 131]) (countLit q [132, 134, 135, 136, 137, 138, 139, 140]) (count275 q) 1 (meaning273 q) (meaning275 q) hs
  change valuationOf q 273 = false ∨ valuationOf q 275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1025 (q : Snake 81) (h : Conditions q) : valuation q 273 = false ∨ valuation q 275 = true := counterClause1025 (baseVal q)

theorem counterClause1026 (q : Nat → Bool) : valuationOf q 274 = false ∨ valuationOf q 276 = true := by
  have hs : count275 q = (countLit q [125, 126, 127, 128, 129, 130, 131]) + (countLit q [132, 134, 135, 136, 137, 138, 139, 140]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 130, 131]) (l₂ := [132, 134, 135, 136, 137, 138, 139, 140])
  have hm := merge_right (literal (valuationOf q) (274)) (literal (valuationOf q) (276)) (countLit q [125, 126, 127, 128, 129, 130, 131]) (countLit q [132, 134, 135, 136, 137, 138, 139, 140]) (count275 q) 2 (meaning274 q) (meaning276 q) hs
  change valuationOf q 274 = false ∨ valuationOf q 276 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1026 (q : Snake 81) (h : Conditions q) : valuation q 274 = false ∨ valuation q 276 = true := counterClause1026 (baseVal q)

theorem counterClause1027 (q : Nat → Bool) : valuationOf q 259 = false ∨ valuationOf q 275 = true := by
  have hs : count275 q = (countLit q [125, 126, 127, 128, 129, 130, 131]) + (countLit q [132, 134, 135, 136, 137, 138, 139, 140]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 130, 131]) (l₂ := [132, 134, 135, 136, 137, 138, 139, 140])
  have hm := merge_left (literal (valuationOf q) (259)) (literal (valuationOf q) (275)) (countLit q [125, 126, 127, 128, 129, 130, 131]) (countLit q [132, 134, 135, 136, 137, 138, 139, 140]) (count275 q) 1 (meaning259 q) (meaning275 q) hs
  change valuationOf q 259 = false ∨ valuationOf q 275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1027 (q : Snake 81) (h : Conditions q) : valuation q 259 = false ∨ valuation q 275 = true := counterClause1027 (baseVal q)

theorem counterClause1028 (q : Nat → Bool) : valuationOf q 259 = false ∨ valuationOf q 273 = false ∨ valuationOf q 276 = true := by
  have hs : count275 q = (countLit q [125, 126, 127, 128, 129, 130, 131]) + (countLit q [132, 134, 135, 136, 137, 138, 139, 140]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 130, 131]) (l₂ := [132, 134, 135, 136, 137, 138, 139, 140])
  have hm := merge_two (literal (valuationOf q) (259)) (literal (valuationOf q) (273)) (literal (valuationOf q) (276)) (countLit q [125, 126, 127, 128, 129, 130, 131]) (countLit q [132, 134, 135, 136, 137, 138, 139, 140]) (count275 q) 1 1 (meaning259 q) (meaning273 q) (meaning276 q) hs
  change valuationOf q 259 = false ∨ valuationOf q 273 = false ∨ valuationOf q 276 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1028 (q : Snake 81) (h : Conditions q) : valuation q 259 = false ∨ valuation q 273 = false ∨ valuation q 276 = true := counterClause1028 (baseVal q)

theorem counterClause1029 (q : Nat → Bool) : valuationOf q 141 = false ∨ valuationOf q 279 = true := by
  have hs : count279 q = (countLit q [141]) + (countLit q [142, 143]) := List.countP_append (p := literal q) (l₁ := [141]) (l₂ := [142, 143])
  have hm := merge_left (literal (valuationOf q) (141)) (literal (valuationOf q) (279)) (countLit q [141]) (countLit q [142, 143]) (count279 q) 1 (meaning141 q) (meaning279 q) hs
  change valuationOf q 141 = false ∨ valuationOf q 279 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1029 (q : Snake 81) (h : Conditions q) : valuation q 141 = false ∨ valuation q 279 = true := counterClause1029 (baseVal q)

theorem counterClause1030 (q : Nat → Bool) : valuationOf q 144 = false ∨ valuationOf q 281 = true := by
  have hs : count281 q = (countLit q [144]) + (countLit q [145]) := List.countP_append (p := literal q) (l₁ := [144]) (l₂ := [145])
  have hm := merge_left (literal (valuationOf q) (144)) (literal (valuationOf q) (281)) (countLit q [144]) (countLit q [145]) (count281 q) 1 (meaning144 q) (meaning281 q) hs
  change valuationOf q 144 = false ∨ valuationOf q 281 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1030 (q : Snake 81) (h : Conditions q) : valuation q 144 = false ∨ valuation q 281 = true := counterClause1030 (baseVal q)

theorem counterClause1031 (q : Nat → Bool) : valuationOf q 147 = false ∨ valuationOf q 283 = true := by
  have hs : count283 q = (countLit q [146]) + (countLit q [147]) := List.countP_append (p := literal q) (l₁ := [146]) (l₂ := [147])
  have hm := merge_right (literal (valuationOf q) (147)) (literal (valuationOf q) (283)) (countLit q [146]) (countLit q [147]) (count283 q) 1 (meaning147 q) (meaning283 q) hs
  change valuationOf q 147 = false ∨ valuationOf q 283 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1031 (q : Snake 81) (h : Conditions q) : valuation q 147 = false ∨ valuation q 283 = true := counterClause1031 (baseVal q)

theorem counterClause1032 (q : Nat → Bool) : valuationOf q 146 = false ∨ valuationOf q 283 = true := by
  have hs : count283 q = (countLit q [146]) + (countLit q [147]) := List.countP_append (p := literal q) (l₁ := [146]) (l₂ := [147])
  have hm := merge_left (literal (valuationOf q) (146)) (literal (valuationOf q) (283)) (countLit q [146]) (countLit q [147]) (count283 q) 1 (meaning146 q) (meaning283 q) hs
  change valuationOf q 146 = false ∨ valuationOf q 283 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1032 (q : Snake 81) (h : Conditions q) : valuation q 146 = false ∨ valuation q 283 = true := counterClause1032 (baseVal q)

theorem counterClause1033 (q : Nat → Bool) : valuationOf q 146 = false ∨ valuationOf q 147 = false ∨ valuationOf q 284 = true := by
  have hs : count283 q = (countLit q [146]) + (countLit q [147]) := List.countP_append (p := literal q) (l₁ := [146]) (l₂ := [147])
  have hm := merge_two (literal (valuationOf q) (146)) (literal (valuationOf q) (147)) (literal (valuationOf q) (284)) (countLit q [146]) (countLit q [147]) (count283 q) 1 1 (meaning146 q) (meaning147 q) (meaning284 q) hs
  change valuationOf q 146 = false ∨ valuationOf q 147 = false ∨ valuationOf q 284 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1033 (q : Snake 81) (h : Conditions q) : valuation q 146 = false ∨ valuation q 147 = false ∨ valuation q 284 = true := counterClause1033 (baseVal q)

theorem counterClause1034 (q : Nat → Bool) : valuationOf q 283 = false ∨ valuationOf q 285 = true := by
  have hs : count285 q = (countLit q [144, 145]) + (countLit q [146, 147]) := List.countP_append (p := literal q) (l₁ := [144, 145]) (l₂ := [146, 147])
  have hm := merge_right (literal (valuationOf q) (283)) (literal (valuationOf q) (285)) (countLit q [144, 145]) (countLit q [146, 147]) (count285 q) 1 (meaning283 q) (meaning285 q) hs
  change valuationOf q 283 = false ∨ valuationOf q 285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1034 (q : Snake 81) (h : Conditions q) : valuation q 283 = false ∨ valuation q 285 = true := counterClause1034 (baseVal q)

theorem counterClause1035 (q : Nat → Bool) : valuationOf q 284 = false ∨ valuationOf q 286 = true := by
  have hs : count285 q = (countLit q [144, 145]) + (countLit q [146, 147]) := List.countP_append (p := literal q) (l₁ := [144, 145]) (l₂ := [146, 147])
  have hm := merge_right (literal (valuationOf q) (284)) (literal (valuationOf q) (286)) (countLit q [144, 145]) (countLit q [146, 147]) (count285 q) 2 (meaning284 q) (meaning286 q) hs
  change valuationOf q 284 = false ∨ valuationOf q 286 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1035 (q : Snake 81) (h : Conditions q) : valuation q 284 = false ∨ valuation q 286 = true := counterClause1035 (baseVal q)

theorem counterClause1036 (q : Nat → Bool) : valuationOf q 281 = false ∨ valuationOf q 285 = true := by
  have hs : count285 q = (countLit q [144, 145]) + (countLit q [146, 147]) := List.countP_append (p := literal q) (l₁ := [144, 145]) (l₂ := [146, 147])
  have hm := merge_left (literal (valuationOf q) (281)) (literal (valuationOf q) (285)) (countLit q [144, 145]) (countLit q [146, 147]) (count285 q) 1 (meaning281 q) (meaning285 q) hs
  change valuationOf q 281 = false ∨ valuationOf q 285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1036 (q : Snake 81) (h : Conditions q) : valuation q 281 = false ∨ valuation q 285 = true := counterClause1036 (baseVal q)

theorem counterClause1037 (q : Nat → Bool) : valuationOf q 285 = false ∨ valuationOf q 287 = true := by
  have hs : count287 q = (countLit q [141, 142, 143]) + (countLit q [144, 145, 146, 147]) := List.countP_append (p := literal q) (l₁ := [141, 142, 143]) (l₂ := [144, 145, 146, 147])
  have hm := merge_right (literal (valuationOf q) (285)) (literal (valuationOf q) (287)) (countLit q [141, 142, 143]) (countLit q [144, 145, 146, 147]) (count287 q) 1 (meaning285 q) (meaning287 q) hs
  change valuationOf q 285 = false ∨ valuationOf q 287 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1037 (q : Snake 81) (h : Conditions q) : valuation q 285 = false ∨ valuation q 287 = true := counterClause1037 (baseVal q)

theorem counterClause1038 (q : Nat → Bool) : valuationOf q 286 = false ∨ valuationOf q 288 = true := by
  have hs : count287 q = (countLit q [141, 142, 143]) + (countLit q [144, 145, 146, 147]) := List.countP_append (p := literal q) (l₁ := [141, 142, 143]) (l₂ := [144, 145, 146, 147])
  have hm := merge_right (literal (valuationOf q) (286)) (literal (valuationOf q) (288)) (countLit q [141, 142, 143]) (countLit q [144, 145, 146, 147]) (count287 q) 2 (meaning286 q) (meaning288 q) hs
  change valuationOf q 286 = false ∨ valuationOf q 288 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1038 (q : Snake 81) (h : Conditions q) : valuation q 286 = false ∨ valuation q 288 = true := counterClause1038 (baseVal q)

theorem counterClause1039 (q : Nat → Bool) : valuationOf q 279 = false ∨ valuationOf q 287 = true := by
  have hs : count287 q = (countLit q [141, 142, 143]) + (countLit q [144, 145, 146, 147]) := List.countP_append (p := literal q) (l₁ := [141, 142, 143]) (l₂ := [144, 145, 146, 147])
  have hm := merge_left (literal (valuationOf q) (279)) (literal (valuationOf q) (287)) (countLit q [141, 142, 143]) (countLit q [144, 145, 146, 147]) (count287 q) 1 (meaning279 q) (meaning287 q) hs
  change valuationOf q 279 = false ∨ valuationOf q 287 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1039 (q : Snake 81) (h : Conditions q) : valuation q 279 = false ∨ valuation q 287 = true := counterClause1039 (baseVal q)

theorem counterClause1040 (q : Nat → Bool) : valuationOf q 149 = false ∨ valuationOf q 289 = true := by
  have hs : count289 q = (countLit q [148]) + (countLit q [149]) := List.countP_append (p := literal q) (l₁ := [148]) (l₂ := [149])
  have hm := merge_right (literal (valuationOf q) (149)) (literal (valuationOf q) (289)) (countLit q [148]) (countLit q [149]) (count289 q) 1 (meaning149 q) (meaning289 q) hs
  change valuationOf q 149 = false ∨ valuationOf q 289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1040 (q : Snake 81) (h : Conditions q) : valuation q 149 = false ∨ valuation q 289 = true := counterClause1040 (baseVal q)

theorem counterClause1041 (q : Nat → Bool) : valuationOf q 151 = false ∨ valuationOf q 291 = true := by
  have hs : count291 q = (countLit q [150]) + (countLit q [151]) := List.countP_append (p := literal q) (l₁ := [150]) (l₂ := [151])
  have hm := merge_right (literal (valuationOf q) (151)) (literal (valuationOf q) (291)) (countLit q [150]) (countLit q [151]) (count291 q) 1 (meaning151 q) (meaning291 q) hs
  change valuationOf q 151 = false ∨ valuationOf q 291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1041 (q : Snake 81) (h : Conditions q) : valuation q 151 = false ∨ valuation q 291 = true := counterClause1041 (baseVal q)

theorem counterClause1042 (q : Nat → Bool) : valuationOf q 291 = false ∨ valuationOf q 293 = true := by
  have hs : count293 q = (countLit q [148, 149]) + (countLit q [150, 151]) := List.countP_append (p := literal q) (l₁ := [148, 149]) (l₂ := [150, 151])
  have hm := merge_right (literal (valuationOf q) (291)) (literal (valuationOf q) (293)) (countLit q [148, 149]) (countLit q [150, 151]) (count293 q) 1 (meaning291 q) (meaning293 q) hs
  change valuationOf q 291 = false ∨ valuationOf q 293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1042 (q : Snake 81) (h : Conditions q) : valuation q 291 = false ∨ valuation q 293 = true := counterClause1042 (baseVal q)

theorem counterClause1043 (q : Nat → Bool) : valuationOf q 289 = false ∨ valuationOf q 293 = true := by
  have hs : count293 q = (countLit q [148, 149]) + (countLit q [150, 151]) := List.countP_append (p := literal q) (l₁ := [148, 149]) (l₂ := [150, 151])
  have hm := merge_left (literal (valuationOf q) (289)) (literal (valuationOf q) (293)) (countLit q [148, 149]) (countLit q [150, 151]) (count293 q) 1 (meaning289 q) (meaning293 q) hs
  change valuationOf q 289 = false ∨ valuationOf q 293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1043 (q : Snake 81) (h : Conditions q) : valuation q 289 = false ∨ valuation q 293 = true := counterClause1043 (baseVal q)

theorem counterClause1044 (q : Nat → Bool) : valuationOf q 152 = false ∨ valuationOf q 295 = true := by
  have hs : count295 q = (countLit q [152]) + (countLit q [153]) := List.countP_append (p := literal q) (l₁ := [152]) (l₂ := [153])
  have hm := merge_left (literal (valuationOf q) (152)) (literal (valuationOf q) (295)) (countLit q [152]) (countLit q [153]) (count295 q) 1 (meaning152 q) (meaning295 q) hs
  change valuationOf q 152 = false ∨ valuationOf q 295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1044 (q : Snake 81) (h : Conditions q) : valuation q 152 = false ∨ valuation q 295 = true := counterClause1044 (baseVal q)

theorem counterClause1045 (q : Nat → Bool) : valuationOf q 155 = false ∨ valuationOf q 297 = true := by
  have hs : count297 q = (countLit q [154]) + (countLit q [155]) := List.countP_append (p := literal q) (l₁ := [154]) (l₂ := [155])
  have hm := merge_right (literal (valuationOf q) (155)) (literal (valuationOf q) (297)) (countLit q [154]) (countLit q [155]) (count297 q) 1 (meaning155 q) (meaning297 q) hs
  change valuationOf q 155 = false ∨ valuationOf q 297 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1045 (q : Snake 81) (h : Conditions q) : valuation q 155 = false ∨ valuation q 297 = true := counterClause1045 (baseVal q)

theorem counterClause1046 (q : Nat → Bool) : valuationOf q 297 = false ∨ valuationOf q 299 = true := by
  have hs : count299 q = (countLit q [152, 153]) + (countLit q [154, 155]) := List.countP_append (p := literal q) (l₁ := [152, 153]) (l₂ := [154, 155])
  have hm := merge_right (literal (valuationOf q) (297)) (literal (valuationOf q) (299)) (countLit q [152, 153]) (countLit q [154, 155]) (count299 q) 1 (meaning297 q) (meaning299 q) hs
  change valuationOf q 297 = false ∨ valuationOf q 299 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1046 (q : Snake 81) (h : Conditions q) : valuation q 297 = false ∨ valuation q 299 = true := counterClause1046 (baseVal q)

theorem counterClause1047 (q : Nat → Bool) : valuationOf q 295 = false ∨ valuationOf q 299 = true := by
  have hs : count299 q = (countLit q [152, 153]) + (countLit q [154, 155]) := List.countP_append (p := literal q) (l₁ := [152, 153]) (l₂ := [154, 155])
  have hm := merge_left (literal (valuationOf q) (295)) (literal (valuationOf q) (299)) (countLit q [152, 153]) (countLit q [154, 155]) (count299 q) 1 (meaning295 q) (meaning299 q) hs
  change valuationOf q 295 = false ∨ valuationOf q 299 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1047 (q : Snake 81) (h : Conditions q) : valuation q 295 = false ∨ valuation q 299 = true := counterClause1047 (baseVal q)

theorem counterClause1048 (q : Nat → Bool) : valuationOf q 299 = false ∨ valuationOf q 301 = true := by
  have hs : count301 q = (countLit q [148, 149, 150, 151]) + (countLit q [152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [148, 149, 150, 151]) (l₂ := [152, 153, 154, 155])
  have hm := merge_right (literal (valuationOf q) (299)) (literal (valuationOf q) (301)) (countLit q [148, 149, 150, 151]) (countLit q [152, 153, 154, 155]) (count301 q) 1 (meaning299 q) (meaning301 q) hs
  change valuationOf q 299 = false ∨ valuationOf q 301 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1048 (q : Snake 81) (h : Conditions q) : valuation q 299 = false ∨ valuation q 301 = true := counterClause1048 (baseVal q)

theorem counterClause1049 (q : Nat → Bool) : valuationOf q 293 = false ∨ valuationOf q 301 = true := by
  have hs : count301 q = (countLit q [148, 149, 150, 151]) + (countLit q [152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [148, 149, 150, 151]) (l₂ := [152, 153, 154, 155])
  have hm := merge_left (literal (valuationOf q) (293)) (literal (valuationOf q) (301)) (countLit q [148, 149, 150, 151]) (countLit q [152, 153, 154, 155]) (count301 q) 1 (meaning293 q) (meaning301 q) hs
  change valuationOf q 293 = false ∨ valuationOf q 301 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1049 (q : Snake 81) (h : Conditions q) : valuation q 293 = false ∨ valuation q 301 = true := counterClause1049 (baseVal q)

theorem counterClause1050 (q : Nat → Bool) : valuationOf q 293 = false ∨ valuationOf q 299 = false ∨ valuationOf q 302 = true := by
  have hs : count301 q = (countLit q [148, 149, 150, 151]) + (countLit q [152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [148, 149, 150, 151]) (l₂ := [152, 153, 154, 155])
  have hm := merge_two (literal (valuationOf q) (293)) (literal (valuationOf q) (299)) (literal (valuationOf q) (302)) (countLit q [148, 149, 150, 151]) (countLit q [152, 153, 154, 155]) (count301 q) 1 1 (meaning293 q) (meaning299 q) (meaning302 q) hs
  change valuationOf q 293 = false ∨ valuationOf q 299 = false ∨ valuationOf q 302 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1050 (q : Snake 81) (h : Conditions q) : valuation q 293 = false ∨ valuation q 299 = false ∨ valuation q 302 = true := counterClause1050 (baseVal q)

theorem counterClause1051 (q : Nat → Bool) : valuationOf q 301 = false ∨ valuationOf q 303 = true := by
  have hs : count303 q = (countLit q [141, 142, 143, 144, 145, 146, 147]) + (countLit q [148, 149, 150, 151, 152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [141, 142, 143, 144, 145, 146, 147]) (l₂ := [148, 149, 150, 151, 152, 153, 154, 155])
  have hm := merge_right (literal (valuationOf q) (301)) (literal (valuationOf q) (303)) (countLit q [141, 142, 143, 144, 145, 146, 147]) (countLit q [148, 149, 150, 151, 152, 153, 154, 155]) (count303 q) 1 (meaning301 q) (meaning303 q) hs
  change valuationOf q 301 = false ∨ valuationOf q 303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1051 (q : Snake 81) (h : Conditions q) : valuation q 301 = false ∨ valuation q 303 = true := counterClause1051 (baseVal q)

theorem counterClause1052 (q : Nat → Bool) : valuationOf q 302 = false ∨ valuationOf q 304 = true := by
  have hs : count303 q = (countLit q [141, 142, 143, 144, 145, 146, 147]) + (countLit q [148, 149, 150, 151, 152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [141, 142, 143, 144, 145, 146, 147]) (l₂ := [148, 149, 150, 151, 152, 153, 154, 155])
  have hm := merge_right (literal (valuationOf q) (302)) (literal (valuationOf q) (304)) (countLit q [141, 142, 143, 144, 145, 146, 147]) (countLit q [148, 149, 150, 151, 152, 153, 154, 155]) (count303 q) 2 (meaning302 q) (meaning304 q) hs
  change valuationOf q 302 = false ∨ valuationOf q 304 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1052 (q : Snake 81) (h : Conditions q) : valuation q 302 = false ∨ valuation q 304 = true := counterClause1052 (baseVal q)

theorem counterClause1053 (q : Nat → Bool) : valuationOf q 287 = false ∨ valuationOf q 303 = true := by
  have hs : count303 q = (countLit q [141, 142, 143, 144, 145, 146, 147]) + (countLit q [148, 149, 150, 151, 152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [141, 142, 143, 144, 145, 146, 147]) (l₂ := [148, 149, 150, 151, 152, 153, 154, 155])
  have hm := merge_left (literal (valuationOf q) (287)) (literal (valuationOf q) (303)) (countLit q [141, 142, 143, 144, 145, 146, 147]) (countLit q [148, 149, 150, 151, 152, 153, 154, 155]) (count303 q) 1 (meaning287 q) (meaning303 q) hs
  change valuationOf q 287 = false ∨ valuationOf q 303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1053 (q : Snake 81) (h : Conditions q) : valuation q 287 = false ∨ valuation q 303 = true := counterClause1053 (baseVal q)

theorem counterClause1054 (q : Nat → Bool) : valuationOf q 287 = false ∨ valuationOf q 301 = false ∨ valuationOf q 304 = true := by
  have hs : count303 q = (countLit q [141, 142, 143, 144, 145, 146, 147]) + (countLit q [148, 149, 150, 151, 152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [141, 142, 143, 144, 145, 146, 147]) (l₂ := [148, 149, 150, 151, 152, 153, 154, 155])
  have hm := merge_two (literal (valuationOf q) (287)) (literal (valuationOf q) (301)) (literal (valuationOf q) (304)) (countLit q [141, 142, 143, 144, 145, 146, 147]) (countLit q [148, 149, 150, 151, 152, 153, 154, 155]) (count303 q) 1 1 (meaning287 q) (meaning301 q) (meaning304 q) hs
  change valuationOf q 287 = false ∨ valuationOf q 301 = false ∨ valuationOf q 304 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1054 (q : Snake 81) (h : Conditions q) : valuation q 287 = false ∨ valuation q 301 = false ∨ valuation q 304 = true := counterClause1054 (baseVal q)

theorem counterClause1055 (q : Nat → Bool) : valuationOf q 288 = false ∨ valuationOf q 304 = true := by
  have hs : count303 q = (countLit q [141, 142, 143, 144, 145, 146, 147]) + (countLit q [148, 149, 150, 151, 152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [141, 142, 143, 144, 145, 146, 147]) (l₂ := [148, 149, 150, 151, 152, 153, 154, 155])
  have hm := merge_left (literal (valuationOf q) (288)) (literal (valuationOf q) (304)) (countLit q [141, 142, 143, 144, 145, 146, 147]) (countLit q [148, 149, 150, 151, 152, 153, 154, 155]) (count303 q) 2 (meaning288 q) (meaning304 q) hs
  change valuationOf q 288 = false ∨ valuationOf q 304 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1055 (q : Snake 81) (h : Conditions q) : valuation q 288 = false ∨ valuation q 304 = true := counterClause1055 (baseVal q)

theorem counterClause1056 (q : Nat → Bool) : valuationOf q 303 = false ∨ valuationOf q 305 = true := by
  have hs : count305 q = (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 134, 135, 136, 137, 138, 139, 140]) + (countLit q [141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 130, 131, 132, 134, 135, 136, 137, 138, 139, 140]) (l₂ := [141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155])
  have hm := merge_right (literal (valuationOf q) (303)) (literal (valuationOf q) (305)) (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 134, 135, 136, 137, 138, 139, 140]) (countLit q [141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (count305 q) 1 (meaning303 q) (meaning305 q) hs
  change valuationOf q 303 = false ∨ valuationOf q 305 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1056 (q : Snake 81) (h : Conditions q) : valuation q 303 = false ∨ valuation q 305 = true := counterClause1056 (baseVal q)

theorem block32 (q : Snake 81) (h : Conditions q) : B112E105.Block32 (valuation q) :=
  ⟨clause1025 q h, clause1026 q h, clause1027 q h, clause1028 q h, clause1029 q h, clause1030 q h, clause1031 q h, clause1032 q h, clause1033 q h, clause1034 q h, clause1035 q h, clause1036 q h, clause1037 q h, clause1038 q h, clause1039 q h, clause1040 q h, clause1041 q h, clause1042 q h, clause1043 q h, clause1044 q h, clause1045 q h, clause1046 q h, clause1047 q h, clause1048 q h, clause1049 q h, clause1050 q h, clause1051 q h, clause1052 q h, clause1053 q h, clause1054 q h, clause1055 q h, clause1056 q h⟩

end
end Snake9.Regrowth.E112105
