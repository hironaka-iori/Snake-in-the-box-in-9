import E112256Semantics
import B112E256Inputs
namespace Snake9.Regrowth.E112256
noncomputable section
local instance blockDec29 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause929 (q : Nat → Bool) : valuationOf q 333 = false ∨ valuationOf q 341 = true := by
  have hs : count341 q = (countLit q [167, 168, 169, 170]) + (countLit q [171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [167, 168, 169, 170]) (l₂ := [171, 172, 173, 174])
  have hm := merge_left (literal (valuationOf q) (333)) (literal (valuationOf q) (341)) (countLit q [167, 168, 169, 170]) (countLit q [171, 172, 173, 174]) (count341 q) 1 (meaning333 q) (meaning341 q) hs
  change valuationOf q 333 = false ∨ valuationOf q 341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause929 (q : Snake 81) (h : Conditions q) : valuation q 333 = false ∨ valuation q 341 = true := counterClause929 (baseVal q)

theorem counterClause930 (q : Nat → Bool) : valuationOf q 333 = false ∨ valuationOf q 339 = false ∨ valuationOf q 342 = true := by
  have hs : count341 q = (countLit q [167, 168, 169, 170]) + (countLit q [171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [167, 168, 169, 170]) (l₂ := [171, 172, 173, 174])
  have hm := merge_two (literal (valuationOf q) (333)) (literal (valuationOf q) (339)) (literal (valuationOf q) (342)) (countLit q [167, 168, 169, 170]) (countLit q [171, 172, 173, 174]) (count341 q) 1 1 (meaning333 q) (meaning339 q) (meaning342 q) hs
  change valuationOf q 333 = false ∨ valuationOf q 339 = false ∨ valuationOf q 342 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause930 (q : Snake 81) (h : Conditions q) : valuation q 333 = false ∨ valuation q 339 = false ∨ valuation q 342 = true := counterClause930 (baseVal q)

theorem counterClause931 (q : Nat → Bool) : valuationOf q 341 = false ∨ valuationOf q 343 = true := by
  have hs : count343 q = (countLit q [159, 160, 161, 162, 163, 164, 165, 166]) + (countLit q [167, 168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [159, 160, 161, 162, 163, 164, 165, 166]) (l₂ := [167, 168, 169, 170, 171, 172, 173, 174])
  have hm := merge_right (literal (valuationOf q) (341)) (literal (valuationOf q) (343)) (countLit q [159, 160, 161, 162, 163, 164, 165, 166]) (countLit q [167, 168, 169, 170, 171, 172, 173, 174]) (count343 q) 1 (meaning341 q) (meaning343 q) hs
  change valuationOf q 341 = false ∨ valuationOf q 343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause931 (q : Snake 81) (h : Conditions q) : valuation q 341 = false ∨ valuation q 343 = true := counterClause931 (baseVal q)

theorem counterClause932 (q : Nat → Bool) : valuationOf q 342 = false ∨ valuationOf q 344 = true := by
  have hs : count343 q = (countLit q [159, 160, 161, 162, 163, 164, 165, 166]) + (countLit q [167, 168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [159, 160, 161, 162, 163, 164, 165, 166]) (l₂ := [167, 168, 169, 170, 171, 172, 173, 174])
  have hm := merge_right (literal (valuationOf q) (342)) (literal (valuationOf q) (344)) (countLit q [159, 160, 161, 162, 163, 164, 165, 166]) (countLit q [167, 168, 169, 170, 171, 172, 173, 174]) (count343 q) 2 (meaning342 q) (meaning344 q) hs
  change valuationOf q 342 = false ∨ valuationOf q 344 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause932 (q : Snake 81) (h : Conditions q) : valuation q 342 = false ∨ valuation q 344 = true := counterClause932 (baseVal q)

theorem counterClause933 (q : Nat → Bool) : valuationOf q 327 = false ∨ valuationOf q 343 = true := by
  have hs : count343 q = (countLit q [159, 160, 161, 162, 163, 164, 165, 166]) + (countLit q [167, 168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [159, 160, 161, 162, 163, 164, 165, 166]) (l₂ := [167, 168, 169, 170, 171, 172, 173, 174])
  have hm := merge_left (literal (valuationOf q) (327)) (literal (valuationOf q) (343)) (countLit q [159, 160, 161, 162, 163, 164, 165, 166]) (countLit q [167, 168, 169, 170, 171, 172, 173, 174]) (count343 q) 1 (meaning327 q) (meaning343 q) hs
  change valuationOf q 327 = false ∨ valuationOf q 343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause933 (q : Snake 81) (h : Conditions q) : valuation q 327 = false ∨ valuation q 343 = true := counterClause933 (baseVal q)

theorem counterClause934 (q : Nat → Bool) : valuationOf q 327 = false ∨ valuationOf q 341 = false ∨ valuationOf q 344 = true := by
  have hs : count343 q = (countLit q [159, 160, 161, 162, 163, 164, 165, 166]) + (countLit q [167, 168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [159, 160, 161, 162, 163, 164, 165, 166]) (l₂ := [167, 168, 169, 170, 171, 172, 173, 174])
  have hm := merge_two (literal (valuationOf q) (327)) (literal (valuationOf q) (341)) (literal (valuationOf q) (344)) (countLit q [159, 160, 161, 162, 163, 164, 165, 166]) (countLit q [167, 168, 169, 170, 171, 172, 173, 174]) (count343 q) 1 1 (meaning327 q) (meaning341 q) (meaning344 q) hs
  change valuationOf q 327 = false ∨ valuationOf q 341 = false ∨ valuationOf q 344 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause934 (q : Snake 81) (h : Conditions q) : valuation q 327 = false ∨ valuation q 341 = false ∨ valuation q 344 = true := counterClause934 (baseVal q)

theorem counterClause935 (q : Nat → Bool) : valuationOf q 328 = false ∨ valuationOf q 344 = true := by
  have hs : count343 q = (countLit q [159, 160, 161, 162, 163, 164, 165, 166]) + (countLit q [167, 168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [159, 160, 161, 162, 163, 164, 165, 166]) (l₂ := [167, 168, 169, 170, 171, 172, 173, 174])
  have hm := merge_left (literal (valuationOf q) (328)) (literal (valuationOf q) (344)) (countLit q [159, 160, 161, 162, 163, 164, 165, 166]) (countLit q [167, 168, 169, 170, 171, 172, 173, 174]) (count343 q) 2 (meaning328 q) (meaning344 q) hs
  change valuationOf q 328 = false ∨ valuationOf q 344 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause935 (q : Snake 81) (h : Conditions q) : valuation q 328 = false ∨ valuation q 344 = true := counterClause935 (baseVal q)

theorem counterClause936 (q : Nat → Bool) : valuationOf q 176 = false ∨ valuationOf q 345 = true := by
  have hs : count345 q = (countLit q [175]) + (countLit q [176]) := List.countP_append (p := literal q) (l₁ := [175]) (l₂ := [176])
  have hm := merge_right (literal (valuationOf q) (176)) (literal (valuationOf q) (345)) (countLit q [175]) (countLit q [176]) (count345 q) 1 (meaning176 q) (meaning345 q) hs
  change valuationOf q 176 = false ∨ valuationOf q 345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause936 (q : Snake 81) (h : Conditions q) : valuation q 176 = false ∨ valuation q 345 = true := counterClause936 (baseVal q)

theorem counterClause937 (q : Nat → Bool) : valuationOf q 345 = false ∨ valuationOf q 349 = true := by
  have hs : count349 q = (countLit q [175, 176]) + (countLit q [177, 178]) := List.countP_append (p := literal q) (l₁ := [175, 176]) (l₂ := [177, 178])
  have hm := merge_left (literal (valuationOf q) (345)) (literal (valuationOf q) (349)) (countLit q [175, 176]) (countLit q [177, 178]) (count349 q) 1 (meaning345 q) (meaning349 q) hs
  change valuationOf q 345 = false ∨ valuationOf q 349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause937 (q : Snake 81) (h : Conditions q) : valuation q 345 = false ∨ valuation q 349 = true := counterClause937 (baseVal q)

theorem counterClause938 (q : Nat → Bool) : valuationOf q 180 = false ∨ valuationOf q 351 = true := by
  have hs : count351 q = (countLit q [179]) + (countLit q [180]) := List.countP_append (p := literal q) (l₁ := [179]) (l₂ := [180])
  have hm := merge_right (literal (valuationOf q) (180)) (literal (valuationOf q) (351)) (countLit q [179]) (countLit q [180]) (count351 q) 1 (meaning180 q) (meaning351 q) hs
  change valuationOf q 180 = false ∨ valuationOf q 351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause938 (q : Snake 81) (h : Conditions q) : valuation q 180 = false ∨ valuation q 351 = true := counterClause938 (baseVal q)

theorem counterClause939 (q : Nat → Bool) : valuationOf q 351 = false ∨ valuationOf q 355 = true := by
  have hs : count355 q = (countLit q [179, 180]) + (countLit q [181, 182]) := List.countP_append (p := literal q) (l₁ := [179, 180]) (l₂ := [181, 182])
  have hm := merge_left (literal (valuationOf q) (351)) (literal (valuationOf q) (355)) (countLit q [179, 180]) (countLit q [181, 182]) (count355 q) 1 (meaning351 q) (meaning355 q) hs
  change valuationOf q 351 = false ∨ valuationOf q 355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause939 (q : Snake 81) (h : Conditions q) : valuation q 351 = false ∨ valuation q 355 = true := counterClause939 (baseVal q)

theorem counterClause940 (q : Nat → Bool) : valuationOf q 355 = false ∨ valuationOf q 357 = true := by
  have hs : count357 q = (countLit q [175, 176, 177, 178]) + (countLit q [179, 180, 181, 182]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177, 178]) (l₂ := [179, 180, 181, 182])
  have hm := merge_right (literal (valuationOf q) (355)) (literal (valuationOf q) (357)) (countLit q [175, 176, 177, 178]) (countLit q [179, 180, 181, 182]) (count357 q) 1 (meaning355 q) (meaning357 q) hs
  change valuationOf q 355 = false ∨ valuationOf q 357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause940 (q : Snake 81) (h : Conditions q) : valuation q 355 = false ∨ valuation q 357 = true := counterClause940 (baseVal q)

theorem counterClause941 (q : Nat → Bool) : valuationOf q 349 = false ∨ valuationOf q 357 = true := by
  have hs : count357 q = (countLit q [175, 176, 177, 178]) + (countLit q [179, 180, 181, 182]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177, 178]) (l₂ := [179, 180, 181, 182])
  have hm := merge_left (literal (valuationOf q) (349)) (literal (valuationOf q) (357)) (countLit q [175, 176, 177, 178]) (countLit q [179, 180, 181, 182]) (count357 q) 1 (meaning349 q) (meaning357 q) hs
  change valuationOf q 349 = false ∨ valuationOf q 357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause941 (q : Snake 81) (h : Conditions q) : valuation q 349 = false ∨ valuation q 357 = true := counterClause941 (baseVal q)

theorem counterClause942 (q : Nat → Bool) : valuationOf q 184 = false ∨ valuationOf q 359 = true := by
  have hs : count359 q = (countLit q [183]) + (countLit q [184]) := List.countP_append (p := literal q) (l₁ := [183]) (l₂ := [184])
  have hm := merge_right (literal (valuationOf q) (184)) (literal (valuationOf q) (359)) (countLit q [183]) (countLit q [184]) (count359 q) 1 (meaning184 q) (meaning359 q) hs
  change valuationOf q 184 = false ∨ valuationOf q 359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause942 (q : Snake 81) (h : Conditions q) : valuation q 184 = false ∨ valuation q 359 = true := counterClause942 (baseVal q)

theorem counterClause943 (q : Nat → Bool) : valuationOf q 185 = false ∨ valuationOf q 361 = true := by
  have hs : count361 q = (countLit q [185]) + (countLit q [186]) := List.countP_append (p := literal q) (l₁ := [185]) (l₂ := [186])
  have hm := merge_left (literal (valuationOf q) (185)) (literal (valuationOf q) (361)) (countLit q [185]) (countLit q [186]) (count361 q) 1 (meaning185 q) (meaning361 q) hs
  change valuationOf q 185 = false ∨ valuationOf q 361 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause943 (q : Snake 81) (h : Conditions q) : valuation q 185 = false ∨ valuation q 361 = true := counterClause943 (baseVal q)

theorem counterClause944 (q : Nat → Bool) : valuationOf q 361 = false ∨ valuationOf q 363 = true := by
  have hs : count363 q = (countLit q [183, 184]) + (countLit q [185, 186]) := List.countP_append (p := literal q) (l₁ := [183, 184]) (l₂ := [185, 186])
  have hm := merge_right (literal (valuationOf q) (361)) (literal (valuationOf q) (363)) (countLit q [183, 184]) (countLit q [185, 186]) (count363 q) 1 (meaning361 q) (meaning363 q) hs
  change valuationOf q 361 = false ∨ valuationOf q 363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause944 (q : Snake 81) (h : Conditions q) : valuation q 361 = false ∨ valuation q 363 = true := counterClause944 (baseVal q)

theorem counterClause945 (q : Nat → Bool) : valuationOf q 359 = false ∨ valuationOf q 363 = true := by
  have hs : count363 q = (countLit q [183, 184]) + (countLit q [185, 186]) := List.countP_append (p := literal q) (l₁ := [183, 184]) (l₂ := [185, 186])
  have hm := merge_left (literal (valuationOf q) (359)) (literal (valuationOf q) (363)) (countLit q [183, 184]) (countLit q [185, 186]) (count363 q) 1 (meaning359 q) (meaning363 q) hs
  change valuationOf q 359 = false ∨ valuationOf q 363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause945 (q : Snake 81) (h : Conditions q) : valuation q 359 = false ∨ valuation q 363 = true := counterClause945 (baseVal q)

theorem counterClause946 (q : Nat → Bool) : valuationOf q 359 = false ∨ valuationOf q 361 = false ∨ valuationOf q 364 = true := by
  have hs : count363 q = (countLit q [183, 184]) + (countLit q [185, 186]) := List.countP_append (p := literal q) (l₁ := [183, 184]) (l₂ := [185, 186])
  have hm := merge_two (literal (valuationOf q) (359)) (literal (valuationOf q) (361)) (literal (valuationOf q) (364)) (countLit q [183, 184]) (countLit q [185, 186]) (count363 q) 1 1 (meaning359 q) (meaning361 q) (meaning364 q) hs
  change valuationOf q 359 = false ∨ valuationOf q 361 = false ∨ valuationOf q 364 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause946 (q : Snake 81) (h : Conditions q) : valuation q 359 = false ∨ valuation q 361 = false ∨ valuation q 364 = true := counterClause946 (baseVal q)

theorem counterClause947 (q : Nat → Bool) : valuationOf q 188 = false ∨ valuationOf q 365 = true := by
  have hs : count365 q = (countLit q [187]) + (countLit q [188]) := List.countP_append (p := literal q) (l₁ := [187]) (l₂ := [188])
  have hm := merge_right (literal (valuationOf q) (188)) (literal (valuationOf q) (365)) (countLit q [187]) (countLit q [188]) (count365 q) 1 (meaning188 q) (meaning365 q) hs
  change valuationOf q 188 = false ∨ valuationOf q 365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause947 (q : Snake 81) (h : Conditions q) : valuation q 188 = false ∨ valuation q 365 = true := counterClause947 (baseVal q)

theorem counterClause948 (q : Nat → Bool) : valuationOf q 187 = false ∨ valuationOf q 365 = true := by
  have hs : count365 q = (countLit q [187]) + (countLit q [188]) := List.countP_append (p := literal q) (l₁ := [187]) (l₂ := [188])
  have hm := merge_left (literal (valuationOf q) (187)) (literal (valuationOf q) (365)) (countLit q [187]) (countLit q [188]) (count365 q) 1 (meaning187 q) (meaning365 q) hs
  change valuationOf q 187 = false ∨ valuationOf q 365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause948 (q : Snake 81) (h : Conditions q) : valuation q 187 = false ∨ valuation q 365 = true := counterClause948 (baseVal q)

theorem counterClause949 (q : Nat → Bool) : valuationOf q 187 = false ∨ valuationOf q 188 = false ∨ valuationOf q 366 = true := by
  have hs : count365 q = (countLit q [187]) + (countLit q [188]) := List.countP_append (p := literal q) (l₁ := [187]) (l₂ := [188])
  have hm := merge_two (literal (valuationOf q) (187)) (literal (valuationOf q) (188)) (literal (valuationOf q) (366)) (countLit q [187]) (countLit q [188]) (count365 q) 1 1 (meaning187 q) (meaning188 q) (meaning366 q) hs
  change valuationOf q 187 = false ∨ valuationOf q 188 = false ∨ valuationOf q 366 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause949 (q : Snake 81) (h : Conditions q) : valuation q 187 = false ∨ valuation q 188 = false ∨ valuation q 366 = true := counterClause949 (baseVal q)

theorem counterClause950 (q : Nat → Bool) : valuationOf q 190 = false ∨ valuationOf q 367 = true := by
  have hs : count367 q = (countLit q [189]) + (countLit q [190]) := List.countP_append (p := literal q) (l₁ := [189]) (l₂ := [190])
  have hm := merge_right (literal (valuationOf q) (190)) (literal (valuationOf q) (367)) (countLit q [189]) (countLit q [190]) (count367 q) 1 (meaning190 q) (meaning367 q) hs
  change valuationOf q 190 = false ∨ valuationOf q 367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause950 (q : Snake 81) (h : Conditions q) : valuation q 190 = false ∨ valuation q 367 = true := counterClause950 (baseVal q)

theorem counterClause951 (q : Nat → Bool) : valuationOf q 189 = false ∨ valuationOf q 367 = true := by
  have hs : count367 q = (countLit q [189]) + (countLit q [190]) := List.countP_append (p := literal q) (l₁ := [189]) (l₂ := [190])
  have hm := merge_left (literal (valuationOf q) (189)) (literal (valuationOf q) (367)) (countLit q [189]) (countLit q [190]) (count367 q) 1 (meaning189 q) (meaning367 q) hs
  change valuationOf q 189 = false ∨ valuationOf q 367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause951 (q : Snake 81) (h : Conditions q) : valuation q 189 = false ∨ valuation q 367 = true := counterClause951 (baseVal q)

theorem counterClause952 (q : Nat → Bool) : valuationOf q 367 = false ∨ valuationOf q 369 = true := by
  have hs : count369 q = (countLit q [187, 188]) + (countLit q [189, 190]) := List.countP_append (p := literal q) (l₁ := [187, 188]) (l₂ := [189, 190])
  have hm := merge_right (literal (valuationOf q) (367)) (literal (valuationOf q) (369)) (countLit q [187, 188]) (countLit q [189, 190]) (count369 q) 1 (meaning367 q) (meaning369 q) hs
  change valuationOf q 367 = false ∨ valuationOf q 369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause952 (q : Snake 81) (h : Conditions q) : valuation q 367 = false ∨ valuation q 369 = true := counterClause952 (baseVal q)

theorem counterClause953 (q : Nat → Bool) : valuationOf q 365 = false ∨ valuationOf q 369 = true := by
  have hs : count369 q = (countLit q [187, 188]) + (countLit q [189, 190]) := List.countP_append (p := literal q) (l₁ := [187, 188]) (l₂ := [189, 190])
  have hm := merge_left (literal (valuationOf q) (365)) (literal (valuationOf q) (369)) (countLit q [187, 188]) (countLit q [189, 190]) (count369 q) 1 (meaning365 q) (meaning369 q) hs
  change valuationOf q 365 = false ∨ valuationOf q 369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause953 (q : Snake 81) (h : Conditions q) : valuation q 365 = false ∨ valuation q 369 = true := counterClause953 (baseVal q)

theorem counterClause954 (q : Nat → Bool) : valuationOf q 365 = false ∨ valuationOf q 367 = false ∨ valuationOf q 370 = true := by
  have hs : count369 q = (countLit q [187, 188]) + (countLit q [189, 190]) := List.countP_append (p := literal q) (l₁ := [187, 188]) (l₂ := [189, 190])
  have hm := merge_two (literal (valuationOf q) (365)) (literal (valuationOf q) (367)) (literal (valuationOf q) (370)) (countLit q [187, 188]) (countLit q [189, 190]) (count369 q) 1 1 (meaning365 q) (meaning367 q) (meaning370 q) hs
  change valuationOf q 365 = false ∨ valuationOf q 367 = false ∨ valuationOf q 370 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause954 (q : Snake 81) (h : Conditions q) : valuation q 365 = false ∨ valuation q 367 = false ∨ valuation q 370 = true := counterClause954 (baseVal q)

theorem counterClause955 (q : Nat → Bool) : valuationOf q 366 = false ∨ valuationOf q 370 = true := by
  have hs : count369 q = (countLit q [187, 188]) + (countLit q [189, 190]) := List.countP_append (p := literal q) (l₁ := [187, 188]) (l₂ := [189, 190])
  have hm := merge_left (literal (valuationOf q) (366)) (literal (valuationOf q) (370)) (countLit q [187, 188]) (countLit q [189, 190]) (count369 q) 2 (meaning366 q) (meaning370 q) hs
  change valuationOf q 366 = false ∨ valuationOf q 370 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause955 (q : Snake 81) (h : Conditions q) : valuation q 366 = false ∨ valuation q 370 = true := counterClause955 (baseVal q)

theorem counterClause956 (q : Nat → Bool) : valuationOf q 369 = false ∨ valuationOf q 371 = true := by
  have hs : count371 q = (countLit q [183, 184, 185, 186]) + (countLit q [187, 188, 189, 190]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186]) (l₂ := [187, 188, 189, 190])
  have hm := merge_right (literal (valuationOf q) (369)) (literal (valuationOf q) (371)) (countLit q [183, 184, 185, 186]) (countLit q [187, 188, 189, 190]) (count371 q) 1 (meaning369 q) (meaning371 q) hs
  change valuationOf q 369 = false ∨ valuationOf q 371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause956 (q : Snake 81) (h : Conditions q) : valuation q 369 = false ∨ valuation q 371 = true := counterClause956 (baseVal q)

theorem counterClause957 (q : Nat → Bool) : valuationOf q 370 = false ∨ valuationOf q 372 = true := by
  have hs : count371 q = (countLit q [183, 184, 185, 186]) + (countLit q [187, 188, 189, 190]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186]) (l₂ := [187, 188, 189, 190])
  have hm := merge_right (literal (valuationOf q) (370)) (literal (valuationOf q) (372)) (countLit q [183, 184, 185, 186]) (countLit q [187, 188, 189, 190]) (count371 q) 2 (meaning370 q) (meaning372 q) hs
  change valuationOf q 370 = false ∨ valuationOf q 372 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause957 (q : Snake 81) (h : Conditions q) : valuation q 370 = false ∨ valuation q 372 = true := counterClause957 (baseVal q)

theorem counterClause958 (q : Nat → Bool) : valuationOf q 363 = false ∨ valuationOf q 371 = true := by
  have hs : count371 q = (countLit q [183, 184, 185, 186]) + (countLit q [187, 188, 189, 190]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186]) (l₂ := [187, 188, 189, 190])
  have hm := merge_left (literal (valuationOf q) (363)) (literal (valuationOf q) (371)) (countLit q [183, 184, 185, 186]) (countLit q [187, 188, 189, 190]) (count371 q) 1 (meaning363 q) (meaning371 q) hs
  change valuationOf q 363 = false ∨ valuationOf q 371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause958 (q : Snake 81) (h : Conditions q) : valuation q 363 = false ∨ valuation q 371 = true := counterClause958 (baseVal q)

theorem counterClause959 (q : Nat → Bool) : valuationOf q 363 = false ∨ valuationOf q 369 = false ∨ valuationOf q 372 = true := by
  have hs : count371 q = (countLit q [183, 184, 185, 186]) + (countLit q [187, 188, 189, 190]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186]) (l₂ := [187, 188, 189, 190])
  have hm := merge_two (literal (valuationOf q) (363)) (literal (valuationOf q) (369)) (literal (valuationOf q) (372)) (countLit q [183, 184, 185, 186]) (countLit q [187, 188, 189, 190]) (count371 q) 1 1 (meaning363 q) (meaning369 q) (meaning372 q) hs
  change valuationOf q 363 = false ∨ valuationOf q 369 = false ∨ valuationOf q 372 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause959 (q : Snake 81) (h : Conditions q) : valuation q 363 = false ∨ valuation q 369 = false ∨ valuation q 372 = true := counterClause959 (baseVal q)

theorem counterClause960 (q : Nat → Bool) : valuationOf q 364 = false ∨ valuationOf q 372 = true := by
  have hs : count371 q = (countLit q [183, 184, 185, 186]) + (countLit q [187, 188, 189, 190]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186]) (l₂ := [187, 188, 189, 190])
  have hm := merge_left (literal (valuationOf q) (364)) (literal (valuationOf q) (372)) (countLit q [183, 184, 185, 186]) (countLit q [187, 188, 189, 190]) (count371 q) 2 (meaning364 q) (meaning372 q) hs
  change valuationOf q 364 = false ∨ valuationOf q 372 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause960 (q : Snake 81) (h : Conditions q) : valuation q 364 = false ∨ valuation q 372 = true := counterClause960 (baseVal q)

theorem block29 (q : Snake 81) (h : Conditions q) : B112E256.Block29 (valuation q) :=
  ⟨clause929 q h, clause930 q h, clause931 q h, clause932 q h, clause933 q h, clause934 q h, clause935 q h, clause936 q h, clause937 q h, clause938 q h, clause939 q h, clause940 q h, clause941 q h, clause942 q h, clause943 q h, clause944 q h, clause945 q h, clause946 q h, clause947 q h, clause948 q h, clause949 q h, clause950 q h, clause951 q h, clause952 q h, clause953 q h, clause954 q h, clause955 q h, clause956 q h, clause957 q h, clause958 q h, clause959 q h, clause960 q h⟩

end
end Snake9.Regrowth.E112256
