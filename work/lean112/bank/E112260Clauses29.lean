import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec29 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause929 (q : Nat → Bool) : valuationOf q 303 = false ∨ valuationOf q 307 = true := by
  have hs : count307 q = (countLit q [155, 156]) + (countLit q [157, 158]) := List.countP_append (p := literal q) (l₁ := [155, 156]) (l₂ := [157, 158])
  have hm := merge_left (literal (valuationOf q) (303)) (literal (valuationOf q) (307)) (countLit q [155, 156]) (countLit q [157, 158]) (count307 q) 1 (meaning303 q) (meaning307 q) hs
  change valuationOf q 303 = false ∨ valuationOf q 307 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause929 (q : Snake 81) (h : Conditions q) : valuation q 303 = false ∨ valuation q 307 = true := counterClause929 (baseVal q)

theorem counterClause930 (q : Nat → Bool) : valuationOf q 303 = false ∨ valuationOf q 305 = false ∨ valuationOf q 308 = true := by
  have hs : count307 q = (countLit q [155, 156]) + (countLit q [157, 158]) := List.countP_append (p := literal q) (l₁ := [155, 156]) (l₂ := [157, 158])
  have hm := merge_two (literal (valuationOf q) (303)) (literal (valuationOf q) (305)) (literal (valuationOf q) (308)) (countLit q [155, 156]) (countLit q [157, 158]) (count307 q) 1 1 (meaning303 q) (meaning305 q) (meaning308 q) hs
  change valuationOf q 303 = false ∨ valuationOf q 305 = false ∨ valuationOf q 308 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause930 (q : Snake 81) (h : Conditions q) : valuation q 303 = false ∨ valuation q 305 = false ∨ valuation q 308 = true := counterClause930 (baseVal q)

theorem counterClause931 (q : Nat → Bool) : valuationOf q 307 = false ∨ valuationOf q 309 = true := by
  have hs : count309 q = (countLit q [151, 152, 153, 154]) + (countLit q [155, 156, 157, 158]) := List.countP_append (p := literal q) (l₁ := [151, 152, 153, 154]) (l₂ := [155, 156, 157, 158])
  have hm := merge_right (literal (valuationOf q) (307)) (literal (valuationOf q) (309)) (countLit q [151, 152, 153, 154]) (countLit q [155, 156, 157, 158]) (count309 q) 1 (meaning307 q) (meaning309 q) hs
  change valuationOf q 307 = false ∨ valuationOf q 309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause931 (q : Snake 81) (h : Conditions q) : valuation q 307 = false ∨ valuation q 309 = true := counterClause931 (baseVal q)

theorem counterClause932 (q : Nat → Bool) : valuationOf q 308 = false ∨ valuationOf q 310 = true := by
  have hs : count309 q = (countLit q [151, 152, 153, 154]) + (countLit q [155, 156, 157, 158]) := List.countP_append (p := literal q) (l₁ := [151, 152, 153, 154]) (l₂ := [155, 156, 157, 158])
  have hm := merge_right (literal (valuationOf q) (308)) (literal (valuationOf q) (310)) (countLit q [151, 152, 153, 154]) (countLit q [155, 156, 157, 158]) (count309 q) 2 (meaning308 q) (meaning310 q) hs
  change valuationOf q 308 = false ∨ valuationOf q 310 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause932 (q : Snake 81) (h : Conditions q) : valuation q 308 = false ∨ valuation q 310 = true := counterClause932 (baseVal q)

theorem counterClause933 (q : Nat → Bool) : valuationOf q 301 = false ∨ valuationOf q 309 = true := by
  have hs : count309 q = (countLit q [151, 152, 153, 154]) + (countLit q [155, 156, 157, 158]) := List.countP_append (p := literal q) (l₁ := [151, 152, 153, 154]) (l₂ := [155, 156, 157, 158])
  have hm := merge_left (literal (valuationOf q) (301)) (literal (valuationOf q) (309)) (countLit q [151, 152, 153, 154]) (countLit q [155, 156, 157, 158]) (count309 q) 1 (meaning301 q) (meaning309 q) hs
  change valuationOf q 301 = false ∨ valuationOf q 309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause933 (q : Snake 81) (h : Conditions q) : valuation q 301 = false ∨ valuation q 309 = true := counterClause933 (baseVal q)

theorem counterClause934 (q : Nat → Bool) : valuationOf q 301 = false ∨ valuationOf q 307 = false ∨ valuationOf q 310 = true := by
  have hs : count309 q = (countLit q [151, 152, 153, 154]) + (countLit q [155, 156, 157, 158]) := List.countP_append (p := literal q) (l₁ := [151, 152, 153, 154]) (l₂ := [155, 156, 157, 158])
  have hm := merge_two (literal (valuationOf q) (301)) (literal (valuationOf q) (307)) (literal (valuationOf q) (310)) (countLit q [151, 152, 153, 154]) (countLit q [155, 156, 157, 158]) (count309 q) 1 1 (meaning301 q) (meaning307 q) (meaning310 q) hs
  change valuationOf q 301 = false ∨ valuationOf q 307 = false ∨ valuationOf q 310 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause934 (q : Snake 81) (h : Conditions q) : valuation q 301 = false ∨ valuation q 307 = false ∨ valuation q 310 = true := counterClause934 (baseVal q)

theorem counterClause935 (q : Nat → Bool) : valuationOf q 302 = false ∨ valuationOf q 310 = true := by
  have hs : count309 q = (countLit q [151, 152, 153, 154]) + (countLit q [155, 156, 157, 158]) := List.countP_append (p := literal q) (l₁ := [151, 152, 153, 154]) (l₂ := [155, 156, 157, 158])
  have hm := merge_left (literal (valuationOf q) (302)) (literal (valuationOf q) (310)) (countLit q [151, 152, 153, 154]) (countLit q [155, 156, 157, 158]) (count309 q) 2 (meaning302 q) (meaning310 q) hs
  change valuationOf q 302 = false ∨ valuationOf q 310 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause935 (q : Snake 81) (h : Conditions q) : valuation q 302 = false ∨ valuation q 310 = true := counterClause935 (baseVal q)

theorem counterClause936 (q : Nat → Bool) : valuationOf q 309 = false ∨ valuationOf q 311 = true := by
  have hs : count311 q = (countLit q [143, 144, 145, 146, 147, 148, 149, 150]) + (countLit q [151, 152, 153, 154, 155, 156, 157, 158]) := List.countP_append (p := literal q) (l₁ := [143, 144, 145, 146, 147, 148, 149, 150]) (l₂ := [151, 152, 153, 154, 155, 156, 157, 158])
  have hm := merge_right (literal (valuationOf q) (309)) (literal (valuationOf q) (311)) (countLit q [143, 144, 145, 146, 147, 148, 149, 150]) (countLit q [151, 152, 153, 154, 155, 156, 157, 158]) (count311 q) 1 (meaning309 q) (meaning311 q) hs
  change valuationOf q 309 = false ∨ valuationOf q 311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause936 (q : Snake 81) (h : Conditions q) : valuation q 309 = false ∨ valuation q 311 = true := counterClause936 (baseVal q)

theorem counterClause937 (q : Nat → Bool) : valuationOf q 310 = false ∨ valuationOf q 312 = true := by
  have hs : count311 q = (countLit q [143, 144, 145, 146, 147, 148, 149, 150]) + (countLit q [151, 152, 153, 154, 155, 156, 157, 158]) := List.countP_append (p := literal q) (l₁ := [143, 144, 145, 146, 147, 148, 149, 150]) (l₂ := [151, 152, 153, 154, 155, 156, 157, 158])
  have hm := merge_right (literal (valuationOf q) (310)) (literal (valuationOf q) (312)) (countLit q [143, 144, 145, 146, 147, 148, 149, 150]) (countLit q [151, 152, 153, 154, 155, 156, 157, 158]) (count311 q) 2 (meaning310 q) (meaning312 q) hs
  change valuationOf q 310 = false ∨ valuationOf q 312 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause937 (q : Snake 81) (h : Conditions q) : valuation q 310 = false ∨ valuation q 312 = true := counterClause937 (baseVal q)

theorem counterClause938 (q : Nat → Bool) : valuationOf q 295 = false ∨ valuationOf q 311 = true := by
  have hs : count311 q = (countLit q [143, 144, 145, 146, 147, 148, 149, 150]) + (countLit q [151, 152, 153, 154, 155, 156, 157, 158]) := List.countP_append (p := literal q) (l₁ := [143, 144, 145, 146, 147, 148, 149, 150]) (l₂ := [151, 152, 153, 154, 155, 156, 157, 158])
  have hm := merge_left (literal (valuationOf q) (295)) (literal (valuationOf q) (311)) (countLit q [143, 144, 145, 146, 147, 148, 149, 150]) (countLit q [151, 152, 153, 154, 155, 156, 157, 158]) (count311 q) 1 (meaning295 q) (meaning311 q) hs
  change valuationOf q 295 = false ∨ valuationOf q 311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause938 (q : Snake 81) (h : Conditions q) : valuation q 295 = false ∨ valuation q 311 = true := counterClause938 (baseVal q)

theorem counterClause939 (q : Nat → Bool) : valuationOf q 295 = false ∨ valuationOf q 309 = false ∨ valuationOf q 312 = true := by
  have hs : count311 q = (countLit q [143, 144, 145, 146, 147, 148, 149, 150]) + (countLit q [151, 152, 153, 154, 155, 156, 157, 158]) := List.countP_append (p := literal q) (l₁ := [143, 144, 145, 146, 147, 148, 149, 150]) (l₂ := [151, 152, 153, 154, 155, 156, 157, 158])
  have hm := merge_two (literal (valuationOf q) (295)) (literal (valuationOf q) (309)) (literal (valuationOf q) (312)) (countLit q [143, 144, 145, 146, 147, 148, 149, 150]) (countLit q [151, 152, 153, 154, 155, 156, 157, 158]) (count311 q) 1 1 (meaning295 q) (meaning309 q) (meaning312 q) hs
  change valuationOf q 295 = false ∨ valuationOf q 309 = false ∨ valuationOf q 312 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause939 (q : Snake 81) (h : Conditions q) : valuation q 295 = false ∨ valuation q 309 = false ∨ valuation q 312 = true := counterClause939 (baseVal q)

theorem counterClause940 (q : Nat → Bool) : valuationOf q 296 = false ∨ valuationOf q 312 = true := by
  have hs : count311 q = (countLit q [143, 144, 145, 146, 147, 148, 149, 150]) + (countLit q [151, 152, 153, 154, 155, 156, 157, 158]) := List.countP_append (p := literal q) (l₁ := [143, 144, 145, 146, 147, 148, 149, 150]) (l₂ := [151, 152, 153, 154, 155, 156, 157, 158])
  have hm := merge_left (literal (valuationOf q) (296)) (literal (valuationOf q) (312)) (countLit q [143, 144, 145, 146, 147, 148, 149, 150]) (countLit q [151, 152, 153, 154, 155, 156, 157, 158]) (count311 q) 2 (meaning296 q) (meaning312 q) hs
  change valuationOf q 296 = false ∨ valuationOf q 312 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause940 (q : Snake 81) (h : Conditions q) : valuation q 296 = false ∨ valuation q 312 = true := counterClause940 (baseVal q)

theorem counterClause941 (q : Nat → Bool) : valuationOf q 311 = false ∨ valuationOf q 313 = true := by
  have hs : count313 q = (countLit q [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) + (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) := List.countP_append (p := literal q) (l₁ := [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (l₂ := [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158])
  have hm := merge_right (literal (valuationOf q) (311)) (literal (valuationOf q) (313)) (countLit q [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (count313 q) 1 (meaning311 q) (meaning313 q) hs
  change valuationOf q 311 = false ∨ valuationOf q 313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause941 (q : Snake 81) (h : Conditions q) : valuation q 311 = false ∨ valuation q 313 = true := counterClause941 (baseVal q)

theorem counterClause942 (q : Nat → Bool) : valuationOf q 312 = false ∨ valuationOf q 314 = true := by
  have hs : count313 q = (countLit q [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) + (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) := List.countP_append (p := literal q) (l₁ := [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (l₂ := [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158])
  have hm := merge_right (literal (valuationOf q) (312)) (literal (valuationOf q) (314)) (countLit q [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (count313 q) 2 (meaning312 q) (meaning314 q) hs
  change valuationOf q 312 = false ∨ valuationOf q 314 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause942 (q : Snake 81) (h : Conditions q) : valuation q 312 = false ∨ valuation q 314 = true := counterClause942 (baseVal q)

theorem counterClause943 (q : Nat → Bool) : valuationOf q 281 = false ∨ valuationOf q 313 = true := by
  have hs : count313 q = (countLit q [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) + (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) := List.countP_append (p := literal q) (l₁ := [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (l₂ := [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158])
  have hm := merge_left (literal (valuationOf q) (281)) (literal (valuationOf q) (313)) (countLit q [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (count313 q) 1 (meaning281 q) (meaning313 q) hs
  change valuationOf q 281 = false ∨ valuationOf q 313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause943 (q : Snake 81) (h : Conditions q) : valuation q 281 = false ∨ valuation q 313 = true := counterClause943 (baseVal q)

theorem counterClause944 (q : Nat → Bool) : valuationOf q 281 = false ∨ valuationOf q 311 = false ∨ valuationOf q 314 = true := by
  have hs : count313 q = (countLit q [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) + (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) := List.countP_append (p := literal q) (l₁ := [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (l₂ := [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158])
  have hm := merge_two (literal (valuationOf q) (281)) (literal (valuationOf q) (311)) (literal (valuationOf q) (314)) (countLit q [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (count313 q) 1 1 (meaning281 q) (meaning311 q) (meaning314 q) hs
  change valuationOf q 281 = false ∨ valuationOf q 311 = false ∨ valuationOf q 314 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause944 (q : Snake 81) (h : Conditions q) : valuation q 281 = false ∨ valuation q 311 = false ∨ valuation q 314 = true := counterClause944 (baseVal q)

theorem counterClause945 (q : Nat → Bool) : valuationOf q 282 = false ∨ valuationOf q 314 = true := by
  have hs : count313 q = (countLit q [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) + (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) := List.countP_append (p := literal q) (l₁ := [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (l₂ := [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158])
  have hm := merge_left (literal (valuationOf q) (282)) (literal (valuationOf q) (314)) (countLit q [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (count313 q) 2 (meaning282 q) (meaning314 q) hs
  change valuationOf q 282 = false ∨ valuationOf q 314 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause945 (q : Snake 81) (h : Conditions q) : valuation q 282 = false ∨ valuation q 314 = true := counterClause945 (baseVal q)

theorem counterClause946 (q : Nat → Bool) : valuationOf q 159 = false ∨ valuationOf q 315 = true := by
  have hs : count315 q = (countLit q [159]) + (countLit q [160]) := List.countP_append (p := literal q) (l₁ := [159]) (l₂ := [160])
  have hm := merge_left (literal (valuationOf q) (159)) (literal (valuationOf q) (315)) (countLit q [159]) (countLit q [160]) (count315 q) 1 (meaning159 q) (meaning315 q) hs
  change valuationOf q 159 = false ∨ valuationOf q 315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause946 (q : Snake 81) (h : Conditions q) : valuation q 159 = false ∨ valuation q 315 = true := counterClause946 (baseVal q)

theorem counterClause947 (q : Nat → Bool) : valuationOf q 161 = false ∨ valuationOf q 317 = true := by
  have hs : count317 q = (countLit q [161]) + (countLit q [162]) := List.countP_append (p := literal q) (l₁ := [161]) (l₂ := [162])
  have hm := merge_left (literal (valuationOf q) (161)) (literal (valuationOf q) (317)) (countLit q [161]) (countLit q [162]) (count317 q) 1 (meaning161 q) (meaning317 q) hs
  change valuationOf q 161 = false ∨ valuationOf q 317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause947 (q : Snake 81) (h : Conditions q) : valuation q 161 = false ∨ valuation q 317 = true := counterClause947 (baseVal q)

theorem counterClause948 (q : Nat → Bool) : valuationOf q 317 = false ∨ valuationOf q 319 = true := by
  have hs : count319 q = (countLit q [159, 160]) + (countLit q [161, 162]) := List.countP_append (p := literal q) (l₁ := [159, 160]) (l₂ := [161, 162])
  have hm := merge_right (literal (valuationOf q) (317)) (literal (valuationOf q) (319)) (countLit q [159, 160]) (countLit q [161, 162]) (count319 q) 1 (meaning317 q) (meaning319 q) hs
  change valuationOf q 317 = false ∨ valuationOf q 319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause948 (q : Snake 81) (h : Conditions q) : valuation q 317 = false ∨ valuation q 319 = true := counterClause948 (baseVal q)

theorem counterClause949 (q : Nat → Bool) : valuationOf q 315 = false ∨ valuationOf q 319 = true := by
  have hs : count319 q = (countLit q [159, 160]) + (countLit q [161, 162]) := List.countP_append (p := literal q) (l₁ := [159, 160]) (l₂ := [161, 162])
  have hm := merge_left (literal (valuationOf q) (315)) (literal (valuationOf q) (319)) (countLit q [159, 160]) (countLit q [161, 162]) (count319 q) 1 (meaning315 q) (meaning319 q) hs
  change valuationOf q 315 = false ∨ valuationOf q 319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause949 (q : Snake 81) (h : Conditions q) : valuation q 315 = false ∨ valuation q 319 = true := counterClause949 (baseVal q)

theorem counterClause950 (q : Nat → Bool) : valuationOf q 315 = false ∨ valuationOf q 317 = false ∨ valuationOf q 320 = true := by
  have hs : count319 q = (countLit q [159, 160]) + (countLit q [161, 162]) := List.countP_append (p := literal q) (l₁ := [159, 160]) (l₂ := [161, 162])
  have hm := merge_two (literal (valuationOf q) (315)) (literal (valuationOf q) (317)) (literal (valuationOf q) (320)) (countLit q [159, 160]) (countLit q [161, 162]) (count319 q) 1 1 (meaning315 q) (meaning317 q) (meaning320 q) hs
  change valuationOf q 315 = false ∨ valuationOf q 317 = false ∨ valuationOf q 320 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause950 (q : Snake 81) (h : Conditions q) : valuation q 315 = false ∨ valuation q 317 = false ∨ valuation q 320 = true := counterClause950 (baseVal q)

theorem counterClause951 (q : Nat → Bool) : valuationOf q 163 = false ∨ valuationOf q 321 = true := by
  have hs : count321 q = (countLit q [163]) + (countLit q [164]) := List.countP_append (p := literal q) (l₁ := [163]) (l₂ := [164])
  have hm := merge_left (literal (valuationOf q) (163)) (literal (valuationOf q) (321)) (countLit q [163]) (countLit q [164]) (count321 q) 1 (meaning163 q) (meaning321 q) hs
  change valuationOf q 163 = false ∨ valuationOf q 321 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause951 (q : Snake 81) (h : Conditions q) : valuation q 163 = false ∨ valuation q 321 = true := counterClause951 (baseVal q)

theorem counterClause952 (q : Nat → Bool) : valuationOf q 321 = false ∨ valuationOf q 325 = true := by
  have hs : count325 q = (countLit q [163, 164]) + (countLit q [165, 166]) := List.countP_append (p := literal q) (l₁ := [163, 164]) (l₂ := [165, 166])
  have hm := merge_left (literal (valuationOf q) (321)) (literal (valuationOf q) (325)) (countLit q [163, 164]) (countLit q [165, 166]) (count325 q) 1 (meaning321 q) (meaning325 q) hs
  change valuationOf q 321 = false ∨ valuationOf q 325 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause952 (q : Snake 81) (h : Conditions q) : valuation q 321 = false ∨ valuation q 325 = true := counterClause952 (baseVal q)

theorem counterClause953 (q : Nat → Bool) : valuationOf q 325 = false ∨ valuationOf q 327 = true := by
  have hs : count327 q = (countLit q [159, 160, 161, 162]) + (countLit q [163, 164, 165, 166]) := List.countP_append (p := literal q) (l₁ := [159, 160, 161, 162]) (l₂ := [163, 164, 165, 166])
  have hm := merge_right (literal (valuationOf q) (325)) (literal (valuationOf q) (327)) (countLit q [159, 160, 161, 162]) (countLit q [163, 164, 165, 166]) (count327 q) 1 (meaning325 q) (meaning327 q) hs
  change valuationOf q 325 = false ∨ valuationOf q 327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause953 (q : Snake 81) (h : Conditions q) : valuation q 325 = false ∨ valuation q 327 = true := counterClause953 (baseVal q)

theorem counterClause954 (q : Nat → Bool) : valuationOf q 319 = false ∨ valuationOf q 327 = true := by
  have hs : count327 q = (countLit q [159, 160, 161, 162]) + (countLit q [163, 164, 165, 166]) := List.countP_append (p := literal q) (l₁ := [159, 160, 161, 162]) (l₂ := [163, 164, 165, 166])
  have hm := merge_left (literal (valuationOf q) (319)) (literal (valuationOf q) (327)) (countLit q [159, 160, 161, 162]) (countLit q [163, 164, 165, 166]) (count327 q) 1 (meaning319 q) (meaning327 q) hs
  change valuationOf q 319 = false ∨ valuationOf q 327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause954 (q : Snake 81) (h : Conditions q) : valuation q 319 = false ∨ valuation q 327 = true := counterClause954 (baseVal q)

theorem counterClause955 (q : Nat → Bool) : valuationOf q 319 = false ∨ valuationOf q 325 = false ∨ valuationOf q 328 = true := by
  have hs : count327 q = (countLit q [159, 160, 161, 162]) + (countLit q [163, 164, 165, 166]) := List.countP_append (p := literal q) (l₁ := [159, 160, 161, 162]) (l₂ := [163, 164, 165, 166])
  have hm := merge_two (literal (valuationOf q) (319)) (literal (valuationOf q) (325)) (literal (valuationOf q) (328)) (countLit q [159, 160, 161, 162]) (countLit q [163, 164, 165, 166]) (count327 q) 1 1 (meaning319 q) (meaning325 q) (meaning328 q) hs
  change valuationOf q 319 = false ∨ valuationOf q 325 = false ∨ valuationOf q 328 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause955 (q : Snake 81) (h : Conditions q) : valuation q 319 = false ∨ valuation q 325 = false ∨ valuation q 328 = true := counterClause955 (baseVal q)

theorem counterClause956 (q : Nat → Bool) : valuationOf q 320 = false ∨ valuationOf q 328 = true := by
  have hs : count327 q = (countLit q [159, 160, 161, 162]) + (countLit q [163, 164, 165, 166]) := List.countP_append (p := literal q) (l₁ := [159, 160, 161, 162]) (l₂ := [163, 164, 165, 166])
  have hm := merge_left (literal (valuationOf q) (320)) (literal (valuationOf q) (328)) (countLit q [159, 160, 161, 162]) (countLit q [163, 164, 165, 166]) (count327 q) 2 (meaning320 q) (meaning328 q) hs
  change valuationOf q 320 = false ∨ valuationOf q 328 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause956 (q : Snake 81) (h : Conditions q) : valuation q 320 = false ∨ valuation q 328 = true := counterClause956 (baseVal q)

theorem counterClause957 (q : Nat → Bool) : valuationOf q 167 = false ∨ valuationOf q 329 = true := by
  have hs : count329 q = (countLit q [167]) + (countLit q [168]) := List.countP_append (p := literal q) (l₁ := [167]) (l₂ := [168])
  have hm := merge_left (literal (valuationOf q) (167)) (literal (valuationOf q) (329)) (countLit q [167]) (countLit q [168]) (count329 q) 1 (meaning167 q) (meaning329 q) hs
  change valuationOf q 167 = false ∨ valuationOf q 329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause957 (q : Snake 81) (h : Conditions q) : valuation q 167 = false ∨ valuation q 329 = true := counterClause957 (baseVal q)

theorem counterClause958 (q : Nat → Bool) : valuationOf q 169 = false ∨ valuationOf q 331 = true := by
  have hs : count331 q = (countLit q [169]) + (countLit q [170]) := List.countP_append (p := literal q) (l₁ := [169]) (l₂ := [170])
  have hm := merge_left (literal (valuationOf q) (169)) (literal (valuationOf q) (331)) (countLit q [169]) (countLit q [170]) (count331 q) 1 (meaning169 q) (meaning331 q) hs
  change valuationOf q 169 = false ∨ valuationOf q 331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause958 (q : Snake 81) (h : Conditions q) : valuation q 169 = false ∨ valuation q 331 = true := counterClause958 (baseVal q)

theorem counterClause959 (q : Nat → Bool) : valuationOf q 331 = false ∨ valuationOf q 333 = true := by
  have hs : count333 q = (countLit q [167, 168]) + (countLit q [169, 170]) := List.countP_append (p := literal q) (l₁ := [167, 168]) (l₂ := [169, 170])
  have hm := merge_right (literal (valuationOf q) (331)) (literal (valuationOf q) (333)) (countLit q [167, 168]) (countLit q [169, 170]) (count333 q) 1 (meaning331 q) (meaning333 q) hs
  change valuationOf q 331 = false ∨ valuationOf q 333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause959 (q : Snake 81) (h : Conditions q) : valuation q 331 = false ∨ valuation q 333 = true := counterClause959 (baseVal q)

theorem counterClause960 (q : Nat → Bool) : valuationOf q 329 = false ∨ valuationOf q 333 = true := by
  have hs : count333 q = (countLit q [167, 168]) + (countLit q [169, 170]) := List.countP_append (p := literal q) (l₁ := [167, 168]) (l₂ := [169, 170])
  have hm := merge_left (literal (valuationOf q) (329)) (literal (valuationOf q) (333)) (countLit q [167, 168]) (countLit q [169, 170]) (count333 q) 1 (meaning329 q) (meaning333 q) hs
  change valuationOf q 329 = false ∨ valuationOf q 333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause960 (q : Snake 81) (h : Conditions q) : valuation q 329 = false ∨ valuation q 333 = true := counterClause960 (baseVal q)

theorem block29 (q : Snake 81) (h : Conditions q) : B112E260.Block29 (valuation q) :=
  ⟨clause929 q h, clause930 q h, clause931 q h, clause932 q h, clause933 q h, clause934 q h, clause935 q h, clause936 q h, clause937 q h, clause938 q h, clause939 q h, clause940 q h, clause941 q h, clause942 q h, clause943 q h, clause944 q h, clause945 q h, clause946 q h, clause947 q h, clause948 q h, clause949 q h, clause950 q h, clause951 q h, clause952 q h, clause953 q h, clause954 q h, clause955 q h, clause956 q h, clause957 q h, clause958 q h, clause959 q h, clause960 q h⟩

end
end Snake9.Regrowth.E112260
