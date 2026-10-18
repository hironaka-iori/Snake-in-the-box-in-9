import E112050Semantics
import B112E050Inputs
namespace Snake9.Regrowth.E112050
noncomputable section
local instance blockDec29 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause929 (q : Nat → Bool) : valuationOf q 152 = false ∨ valuationOf q 293 = true := by
  have hs : count293 q = (countLit q [151]) + (countLit q [152]) := List.countP_append (p := literal q) (l₁ := [151]) (l₂ := [152])
  have hm := merge_right (literal (valuationOf q) (152)) (literal (valuationOf q) (293)) (countLit q [151]) (countLit q [152]) (count293 q) 1 (meaning152 q) (meaning293 q) hs
  change valuationOf q 152 = false ∨ valuationOf q 293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause929 (q : Snake 81) (h : Conditions q) : valuation q 152 = false ∨ valuation q 293 = true := counterClause929 (baseVal q)

theorem counterClause930 (q : Nat → Bool) : valuationOf q 151 = false ∨ valuationOf q 293 = true := by
  have hs : count293 q = (countLit q [151]) + (countLit q [152]) := List.countP_append (p := literal q) (l₁ := [151]) (l₂ := [152])
  have hm := merge_left (literal (valuationOf q) (151)) (literal (valuationOf q) (293)) (countLit q [151]) (countLit q [152]) (count293 q) 1 (meaning151 q) (meaning293 q) hs
  change valuationOf q 151 = false ∨ valuationOf q 293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause930 (q : Snake 81) (h : Conditions q) : valuation q 151 = false ∨ valuation q 293 = true := counterClause930 (baseVal q)

theorem counterClause931 (q : Nat → Bool) : valuationOf q 293 = false ∨ valuationOf q 295 = true := by
  have hs : count295 q = (countLit q [149, 150]) + (countLit q [151, 152]) := List.countP_append (p := literal q) (l₁ := [149, 150]) (l₂ := [151, 152])
  have hm := merge_right (literal (valuationOf q) (293)) (literal (valuationOf q) (295)) (countLit q [149, 150]) (countLit q [151, 152]) (count295 q) 1 (meaning293 q) (meaning295 q) hs
  change valuationOf q 293 = false ∨ valuationOf q 295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause931 (q : Snake 81) (h : Conditions q) : valuation q 293 = false ∨ valuation q 295 = true := counterClause931 (baseVal q)

theorem counterClause932 (q : Nat → Bool) : valuationOf q 291 = false ∨ valuationOf q 295 = true := by
  have hs : count295 q = (countLit q [149, 150]) + (countLit q [151, 152]) := List.countP_append (p := literal q) (l₁ := [149, 150]) (l₂ := [151, 152])
  have hm := merge_left (literal (valuationOf q) (291)) (literal (valuationOf q) (295)) (countLit q [149, 150]) (countLit q [151, 152]) (count295 q) 1 (meaning291 q) (meaning295 q) hs
  change valuationOf q 291 = false ∨ valuationOf q 295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause932 (q : Snake 81) (h : Conditions q) : valuation q 291 = false ∨ valuation q 295 = true := counterClause932 (baseVal q)

theorem counterClause933 (q : Nat → Bool) : valuationOf q 295 = false ∨ valuationOf q 297 = true := by
  have hs : count297 q = (countLit q [145, 146, 147, 148]) + (countLit q [149, 150, 151, 152]) := List.countP_append (p := literal q) (l₁ := [145, 146, 147, 148]) (l₂ := [149, 150, 151, 152])
  have hm := merge_right (literal (valuationOf q) (295)) (literal (valuationOf q) (297)) (countLit q [145, 146, 147, 148]) (countLit q [149, 150, 151, 152]) (count297 q) 1 (meaning295 q) (meaning297 q) hs
  change valuationOf q 295 = false ∨ valuationOf q 297 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause933 (q : Snake 81) (h : Conditions q) : valuation q 295 = false ∨ valuation q 297 = true := counterClause933 (baseVal q)

theorem counterClause934 (q : Nat → Bool) : valuationOf q 289 = false ∨ valuationOf q 297 = true := by
  have hs : count297 q = (countLit q [145, 146, 147, 148]) + (countLit q [149, 150, 151, 152]) := List.countP_append (p := literal q) (l₁ := [145, 146, 147, 148]) (l₂ := [149, 150, 151, 152])
  have hm := merge_left (literal (valuationOf q) (289)) (literal (valuationOf q) (297)) (countLit q [145, 146, 147, 148]) (countLit q [149, 150, 151, 152]) (count297 q) 1 (meaning289 q) (meaning297 q) hs
  change valuationOf q 289 = false ∨ valuationOf q 297 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause934 (q : Snake 81) (h : Conditions q) : valuation q 289 = false ∨ valuation q 297 = true := counterClause934 (baseVal q)

theorem counterClause935 (q : Nat → Bool) : valuationOf q 289 = false ∨ valuationOf q 295 = false ∨ valuationOf q 298 = true := by
  have hs : count297 q = (countLit q [145, 146, 147, 148]) + (countLit q [149, 150, 151, 152]) := List.countP_append (p := literal q) (l₁ := [145, 146, 147, 148]) (l₂ := [149, 150, 151, 152])
  have hm := merge_two (literal (valuationOf q) (289)) (literal (valuationOf q) (295)) (literal (valuationOf q) (298)) (countLit q [145, 146, 147, 148]) (countLit q [149, 150, 151, 152]) (count297 q) 1 1 (meaning289 q) (meaning295 q) (meaning298 q) hs
  change valuationOf q 289 = false ∨ valuationOf q 295 = false ∨ valuationOf q 298 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause935 (q : Snake 81) (h : Conditions q) : valuation q 289 = false ∨ valuation q 295 = false ∨ valuation q 298 = true := counterClause935 (baseVal q)

theorem counterClause936 (q : Nat → Bool) : valuationOf q 290 = false ∨ valuationOf q 298 = true := by
  have hs : count297 q = (countLit q [145, 146, 147, 148]) + (countLit q [149, 150, 151, 152]) := List.countP_append (p := literal q) (l₁ := [145, 146, 147, 148]) (l₂ := [149, 150, 151, 152])
  have hm := merge_left (literal (valuationOf q) (290)) (literal (valuationOf q) (298)) (countLit q [145, 146, 147, 148]) (countLit q [149, 150, 151, 152]) (count297 q) 2 (meaning290 q) (meaning298 q) hs
  change valuationOf q 290 = false ∨ valuationOf q 298 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause936 (q : Snake 81) (h : Conditions q) : valuation q 290 = false ∨ valuation q 298 = true := counterClause936 (baseVal q)

theorem counterClause937 (q : Nat → Bool) : valuationOf q 154 = false ∨ valuationOf q 299 = true := by
  have hs : count299 q = (countLit q [153]) + (countLit q [154]) := List.countP_append (p := literal q) (l₁ := [153]) (l₂ := [154])
  have hm := merge_right (literal (valuationOf q) (154)) (literal (valuationOf q) (299)) (countLit q [153]) (countLit q [154]) (count299 q) 1 (meaning154 q) (meaning299 q) hs
  change valuationOf q 154 = false ∨ valuationOf q 299 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause937 (q : Snake 81) (h : Conditions q) : valuation q 154 = false ∨ valuation q 299 = true := counterClause937 (baseVal q)

theorem counterClause938 (q : Nat → Bool) : valuationOf q 299 = false ∨ valuationOf q 303 = true := by
  have hs : count303 q = (countLit q [153, 154]) + (countLit q [155, 156]) := List.countP_append (p := literal q) (l₁ := [153, 154]) (l₂ := [155, 156])
  have hm := merge_left (literal (valuationOf q) (299)) (literal (valuationOf q) (303)) (countLit q [153, 154]) (countLit q [155, 156]) (count303 q) 1 (meaning299 q) (meaning303 q) hs
  change valuationOf q 299 = false ∨ valuationOf q 303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause938 (q : Snake 81) (h : Conditions q) : valuation q 299 = false ∨ valuation q 303 = true := counterClause938 (baseVal q)

theorem counterClause939 (q : Nat → Bool) : valuationOf q 157 = false ∨ valuationOf q 305 = true := by
  have hs : count305 q = (countLit q [157]) + (countLit q [158]) := List.countP_append (p := literal q) (l₁ := [157]) (l₂ := [158])
  have hm := merge_left (literal (valuationOf q) (157)) (literal (valuationOf q) (305)) (countLit q [157]) (countLit q [158]) (count305 q) 1 (meaning157 q) (meaning305 q) hs
  change valuationOf q 157 = false ∨ valuationOf q 305 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause939 (q : Snake 81) (h : Conditions q) : valuation q 157 = false ∨ valuation q 305 = true := counterClause939 (baseVal q)

theorem counterClause940 (q : Nat → Bool) : valuationOf q 160 = false ∨ valuationOf q 307 = true := by
  have hs : count307 q = (countLit q [159]) + (countLit q [160]) := List.countP_append (p := literal q) (l₁ := [159]) (l₂ := [160])
  have hm := merge_right (literal (valuationOf q) (160)) (literal (valuationOf q) (307)) (countLit q [159]) (countLit q [160]) (count307 q) 1 (meaning160 q) (meaning307 q) hs
  change valuationOf q 160 = false ∨ valuationOf q 307 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause940 (q : Snake 81) (h : Conditions q) : valuation q 160 = false ∨ valuation q 307 = true := counterClause940 (baseVal q)

theorem counterClause941 (q : Nat → Bool) : valuationOf q 159 = false ∨ valuationOf q 307 = true := by
  have hs : count307 q = (countLit q [159]) + (countLit q [160]) := List.countP_append (p := literal q) (l₁ := [159]) (l₂ := [160])
  have hm := merge_left (literal (valuationOf q) (159)) (literal (valuationOf q) (307)) (countLit q [159]) (countLit q [160]) (count307 q) 1 (meaning159 q) (meaning307 q) hs
  change valuationOf q 159 = false ∨ valuationOf q 307 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause941 (q : Snake 81) (h : Conditions q) : valuation q 159 = false ∨ valuation q 307 = true := counterClause941 (baseVal q)

theorem counterClause942 (q : Nat → Bool) : valuationOf q 159 = false ∨ valuationOf q 160 = false ∨ valuationOf q 308 = true := by
  have hs : count307 q = (countLit q [159]) + (countLit q [160]) := List.countP_append (p := literal q) (l₁ := [159]) (l₂ := [160])
  have hm := merge_two (literal (valuationOf q) (159)) (literal (valuationOf q) (160)) (literal (valuationOf q) (308)) (countLit q [159]) (countLit q [160]) (count307 q) 1 1 (meaning159 q) (meaning160 q) (meaning308 q) hs
  change valuationOf q 159 = false ∨ valuationOf q 160 = false ∨ valuationOf q 308 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause942 (q : Snake 81) (h : Conditions q) : valuation q 159 = false ∨ valuation q 160 = false ∨ valuation q 308 = true := counterClause942 (baseVal q)

theorem counterClause943 (q : Nat → Bool) : valuationOf q 307 = false ∨ valuationOf q 309 = true := by
  have hs : count309 q = (countLit q [157, 158]) + (countLit q [159, 160]) := List.countP_append (p := literal q) (l₁ := [157, 158]) (l₂ := [159, 160])
  have hm := merge_right (literal (valuationOf q) (307)) (literal (valuationOf q) (309)) (countLit q [157, 158]) (countLit q [159, 160]) (count309 q) 1 (meaning307 q) (meaning309 q) hs
  change valuationOf q 307 = false ∨ valuationOf q 309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause943 (q : Snake 81) (h : Conditions q) : valuation q 307 = false ∨ valuation q 309 = true := counterClause943 (baseVal q)

theorem counterClause944 (q : Nat → Bool) : valuationOf q 308 = false ∨ valuationOf q 310 = true := by
  have hs : count309 q = (countLit q [157, 158]) + (countLit q [159, 160]) := List.countP_append (p := literal q) (l₁ := [157, 158]) (l₂ := [159, 160])
  have hm := merge_right (literal (valuationOf q) (308)) (literal (valuationOf q) (310)) (countLit q [157, 158]) (countLit q [159, 160]) (count309 q) 2 (meaning308 q) (meaning310 q) hs
  change valuationOf q 308 = false ∨ valuationOf q 310 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause944 (q : Snake 81) (h : Conditions q) : valuation q 308 = false ∨ valuation q 310 = true := counterClause944 (baseVal q)

theorem counterClause945 (q : Nat → Bool) : valuationOf q 305 = false ∨ valuationOf q 309 = true := by
  have hs : count309 q = (countLit q [157, 158]) + (countLit q [159, 160]) := List.countP_append (p := literal q) (l₁ := [157, 158]) (l₂ := [159, 160])
  have hm := merge_left (literal (valuationOf q) (305)) (literal (valuationOf q) (309)) (countLit q [157, 158]) (countLit q [159, 160]) (count309 q) 1 (meaning305 q) (meaning309 q) hs
  change valuationOf q 305 = false ∨ valuationOf q 309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause945 (q : Snake 81) (h : Conditions q) : valuation q 305 = false ∨ valuation q 309 = true := counterClause945 (baseVal q)

theorem counterClause946 (q : Nat → Bool) : valuationOf q 309 = false ∨ valuationOf q 311 = true := by
  have hs : count311 q = (countLit q [153, 154, 155, 156]) + (countLit q [157, 158, 159, 160]) := List.countP_append (p := literal q) (l₁ := [153, 154, 155, 156]) (l₂ := [157, 158, 159, 160])
  have hm := merge_right (literal (valuationOf q) (309)) (literal (valuationOf q) (311)) (countLit q [153, 154, 155, 156]) (countLit q [157, 158, 159, 160]) (count311 q) 1 (meaning309 q) (meaning311 q) hs
  change valuationOf q 309 = false ∨ valuationOf q 311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause946 (q : Snake 81) (h : Conditions q) : valuation q 309 = false ∨ valuation q 311 = true := counterClause946 (baseVal q)

theorem counterClause947 (q : Nat → Bool) : valuationOf q 310 = false ∨ valuationOf q 312 = true := by
  have hs : count311 q = (countLit q [153, 154, 155, 156]) + (countLit q [157, 158, 159, 160]) := List.countP_append (p := literal q) (l₁ := [153, 154, 155, 156]) (l₂ := [157, 158, 159, 160])
  have hm := merge_right (literal (valuationOf q) (310)) (literal (valuationOf q) (312)) (countLit q [153, 154, 155, 156]) (countLit q [157, 158, 159, 160]) (count311 q) 2 (meaning310 q) (meaning312 q) hs
  change valuationOf q 310 = false ∨ valuationOf q 312 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause947 (q : Snake 81) (h : Conditions q) : valuation q 310 = false ∨ valuation q 312 = true := counterClause947 (baseVal q)

theorem counterClause948 (q : Nat → Bool) : valuationOf q 303 = false ∨ valuationOf q 311 = true := by
  have hs : count311 q = (countLit q [153, 154, 155, 156]) + (countLit q [157, 158, 159, 160]) := List.countP_append (p := literal q) (l₁ := [153, 154, 155, 156]) (l₂ := [157, 158, 159, 160])
  have hm := merge_left (literal (valuationOf q) (303)) (literal (valuationOf q) (311)) (countLit q [153, 154, 155, 156]) (countLit q [157, 158, 159, 160]) (count311 q) 1 (meaning303 q) (meaning311 q) hs
  change valuationOf q 303 = false ∨ valuationOf q 311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause948 (q : Snake 81) (h : Conditions q) : valuation q 303 = false ∨ valuation q 311 = true := counterClause948 (baseVal q)

theorem counterClause949 (q : Nat → Bool) : valuationOf q 311 = false ∨ valuationOf q 313 = true := by
  have hs : count313 q = (countLit q [145, 146, 147, 148, 149, 150, 151, 152]) + (countLit q [153, 154, 155, 156, 157, 158, 159, 160]) := List.countP_append (p := literal q) (l₁ := [145, 146, 147, 148, 149, 150, 151, 152]) (l₂ := [153, 154, 155, 156, 157, 158, 159, 160])
  have hm := merge_right (literal (valuationOf q) (311)) (literal (valuationOf q) (313)) (countLit q [145, 146, 147, 148, 149, 150, 151, 152]) (countLit q [153, 154, 155, 156, 157, 158, 159, 160]) (count313 q) 1 (meaning311 q) (meaning313 q) hs
  change valuationOf q 311 = false ∨ valuationOf q 313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause949 (q : Snake 81) (h : Conditions q) : valuation q 311 = false ∨ valuation q 313 = true := counterClause949 (baseVal q)

theorem counterClause950 (q : Nat → Bool) : valuationOf q 312 = false ∨ valuationOf q 314 = true := by
  have hs : count313 q = (countLit q [145, 146, 147, 148, 149, 150, 151, 152]) + (countLit q [153, 154, 155, 156, 157, 158, 159, 160]) := List.countP_append (p := literal q) (l₁ := [145, 146, 147, 148, 149, 150, 151, 152]) (l₂ := [153, 154, 155, 156, 157, 158, 159, 160])
  have hm := merge_right (literal (valuationOf q) (312)) (literal (valuationOf q) (314)) (countLit q [145, 146, 147, 148, 149, 150, 151, 152]) (countLit q [153, 154, 155, 156, 157, 158, 159, 160]) (count313 q) 2 (meaning312 q) (meaning314 q) hs
  change valuationOf q 312 = false ∨ valuationOf q 314 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause950 (q : Snake 81) (h : Conditions q) : valuation q 312 = false ∨ valuation q 314 = true := counterClause950 (baseVal q)

theorem counterClause951 (q : Nat → Bool) : valuationOf q 297 = false ∨ valuationOf q 313 = true := by
  have hs : count313 q = (countLit q [145, 146, 147, 148, 149, 150, 151, 152]) + (countLit q [153, 154, 155, 156, 157, 158, 159, 160]) := List.countP_append (p := literal q) (l₁ := [145, 146, 147, 148, 149, 150, 151, 152]) (l₂ := [153, 154, 155, 156, 157, 158, 159, 160])
  have hm := merge_left (literal (valuationOf q) (297)) (literal (valuationOf q) (313)) (countLit q [145, 146, 147, 148, 149, 150, 151, 152]) (countLit q [153, 154, 155, 156, 157, 158, 159, 160]) (count313 q) 1 (meaning297 q) (meaning313 q) hs
  change valuationOf q 297 = false ∨ valuationOf q 313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause951 (q : Snake 81) (h : Conditions q) : valuation q 297 = false ∨ valuation q 313 = true := counterClause951 (baseVal q)

theorem counterClause952 (q : Nat → Bool) : valuationOf q 297 = false ∨ valuationOf q 311 = false ∨ valuationOf q 314 = true := by
  have hs : count313 q = (countLit q [145, 146, 147, 148, 149, 150, 151, 152]) + (countLit q [153, 154, 155, 156, 157, 158, 159, 160]) := List.countP_append (p := literal q) (l₁ := [145, 146, 147, 148, 149, 150, 151, 152]) (l₂ := [153, 154, 155, 156, 157, 158, 159, 160])
  have hm := merge_two (literal (valuationOf q) (297)) (literal (valuationOf q) (311)) (literal (valuationOf q) (314)) (countLit q [145, 146, 147, 148, 149, 150, 151, 152]) (countLit q [153, 154, 155, 156, 157, 158, 159, 160]) (count313 q) 1 1 (meaning297 q) (meaning311 q) (meaning314 q) hs
  change valuationOf q 297 = false ∨ valuationOf q 311 = false ∨ valuationOf q 314 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause952 (q : Snake 81) (h : Conditions q) : valuation q 297 = false ∨ valuation q 311 = false ∨ valuation q 314 = true := counterClause952 (baseVal q)

theorem counterClause953 (q : Nat → Bool) : valuationOf q 298 = false ∨ valuationOf q 314 = true := by
  have hs : count313 q = (countLit q [145, 146, 147, 148, 149, 150, 151, 152]) + (countLit q [153, 154, 155, 156, 157, 158, 159, 160]) := List.countP_append (p := literal q) (l₁ := [145, 146, 147, 148, 149, 150, 151, 152]) (l₂ := [153, 154, 155, 156, 157, 158, 159, 160])
  have hm := merge_left (literal (valuationOf q) (298)) (literal (valuationOf q) (314)) (countLit q [145, 146, 147, 148, 149, 150, 151, 152]) (countLit q [153, 154, 155, 156, 157, 158, 159, 160]) (count313 q) 2 (meaning298 q) (meaning314 q) hs
  change valuationOf q 298 = false ∨ valuationOf q 314 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause953 (q : Snake 81) (h : Conditions q) : valuation q 298 = false ∨ valuation q 314 = true := counterClause953 (baseVal q)

theorem counterClause954 (q : Nat → Bool) : valuationOf q 313 = false ∨ valuationOf q 315 = true := by
  have hs : count315 q = (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) + (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) := List.countP_append (p := literal q) (l₁ := [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) (l₂ := [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160])
  have hm := merge_right (literal (valuationOf q) (313)) (literal (valuationOf q) (315)) (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) (count315 q) 1 (meaning313 q) (meaning315 q) hs
  change valuationOf q 313 = false ∨ valuationOf q 315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause954 (q : Snake 81) (h : Conditions q) : valuation q 313 = false ∨ valuation q 315 = true := counterClause954 (baseVal q)

theorem counterClause955 (q : Nat → Bool) : valuationOf q 314 = false ∨ valuationOf q 316 = true := by
  have hs : count315 q = (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) + (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) := List.countP_append (p := literal q) (l₁ := [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) (l₂ := [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160])
  have hm := merge_right (literal (valuationOf q) (314)) (literal (valuationOf q) (316)) (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) (count315 q) 2 (meaning314 q) (meaning316 q) hs
  change valuationOf q 314 = false ∨ valuationOf q 316 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause955 (q : Snake 81) (h : Conditions q) : valuation q 314 = false ∨ valuation q 316 = true := counterClause955 (baseVal q)

theorem counterClause956 (q : Nat → Bool) : valuationOf q 283 = false ∨ valuationOf q 315 = true := by
  have hs : count315 q = (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) + (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) := List.countP_append (p := literal q) (l₁ := [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) (l₂ := [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160])
  have hm := merge_left (literal (valuationOf q) (283)) (literal (valuationOf q) (315)) (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) (count315 q) 1 (meaning283 q) (meaning315 q) hs
  change valuationOf q 283 = false ∨ valuationOf q 315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause956 (q : Snake 81) (h : Conditions q) : valuation q 283 = false ∨ valuation q 315 = true := counterClause956 (baseVal q)

theorem counterClause957 (q : Nat → Bool) : valuationOf q 283 = false ∨ valuationOf q 313 = false ∨ valuationOf q 316 = true := by
  have hs : count315 q = (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) + (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) := List.countP_append (p := literal q) (l₁ := [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) (l₂ := [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160])
  have hm := merge_two (literal (valuationOf q) (283)) (literal (valuationOf q) (313)) (literal (valuationOf q) (316)) (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) (count315 q) 1 1 (meaning283 q) (meaning313 q) (meaning316 q) hs
  change valuationOf q 283 = false ∨ valuationOf q 313 = false ∨ valuationOf q 316 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause957 (q : Snake 81) (h : Conditions q) : valuation q 283 = false ∨ valuation q 313 = false ∨ valuation q 316 = true := counterClause957 (baseVal q)

theorem counterClause958 (q : Nat → Bool) : valuationOf q 284 = false ∨ valuationOf q 316 = true := by
  have hs : count315 q = (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) + (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) := List.countP_append (p := literal q) (l₁ := [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) (l₂ := [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160])
  have hm := merge_left (literal (valuationOf q) (284)) (literal (valuationOf q) (316)) (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) (count315 q) 2 (meaning284 q) (meaning316 q) hs
  change valuationOf q 284 = false ∨ valuationOf q 316 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause958 (q : Snake 81) (h : Conditions q) : valuation q 284 = false ∨ valuation q 316 = true := counterClause958 (baseVal q)

theorem counterClause959 (q : Nat → Bool) : valuationOf q 162 = false ∨ valuationOf q 317 = true := by
  have hs : count317 q = (countLit q [161]) + (countLit q [162]) := List.countP_append (p := literal q) (l₁ := [161]) (l₂ := [162])
  have hm := merge_right (literal (valuationOf q) (162)) (literal (valuationOf q) (317)) (countLit q [161]) (countLit q [162]) (count317 q) 1 (meaning162 q) (meaning317 q) hs
  change valuationOf q 162 = false ∨ valuationOf q 317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause959 (q : Snake 81) (h : Conditions q) : valuation q 162 = false ∨ valuation q 317 = true := counterClause959 (baseVal q)

theorem counterClause960 (q : Nat → Bool) : valuationOf q 317 = false ∨ valuationOf q 321 = true := by
  have hs : count321 q = (countLit q [161, 162]) + (countLit q [163, 164]) := List.countP_append (p := literal q) (l₁ := [161, 162]) (l₂ := [163, 164])
  have hm := merge_left (literal (valuationOf q) (317)) (literal (valuationOf q) (321)) (countLit q [161, 162]) (countLit q [163, 164]) (count321 q) 1 (meaning317 q) (meaning321 q) hs
  change valuationOf q 317 = false ∨ valuationOf q 321 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause960 (q : Snake 81) (h : Conditions q) : valuation q 317 = false ∨ valuation q 321 = true := counterClause960 (baseVal q)

theorem block29 (q : Snake 81) (h : Conditions q) : B112E050.Block29 (valuation q) :=
  ⟨clause929 q h, clause930 q h, clause931 q h, clause932 q h, clause933 q h, clause934 q h, clause935 q h, clause936 q h, clause937 q h, clause938 q h, clause939 q h, clause940 q h, clause941 q h, clause942 q h, clause943 q h, clause944 q h, clause945 q h, clause946 q h, clause947 q h, clause948 q h, clause949 q h, clause950 q h, clause951 q h, clause952 q h, clause953 q h, clause954 q h, clause955 q h, clause956 q h, clause957 q h, clause958 q h, clause959 q h, clause960 q h⟩

end
end Snake9.Regrowth.E112050
