import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec30 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause961 (q : Nat → Bool) : valuationOf q 171 = false ∨ valuationOf q 335 = true := by
  have hs : count335 q = (countLit q [171]) + (countLit q [172]) := List.countP_append (p := literal q) (l₁ := [171]) (l₂ := [172])
  have hm := merge_left (literal (valuationOf q) (171)) (literal (valuationOf q) (335)) (countLit q [171]) (countLit q [172]) (count335 q) 1 (meaning171 q) (meaning335 q) hs
  change valuationOf q 171 = false ∨ valuationOf q 335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause961 (q : Snake 81) (h : Conditions q) : valuation q 171 = false ∨ valuation q 335 = true := counterClause961 (baseVal q)

theorem counterClause962 (q : Nat → Bool) : valuationOf q 173 = false ∨ valuationOf q 337 = true := by
  have hs : count337 q = (countLit q [173]) + (countLit q [174]) := List.countP_append (p := literal q) (l₁ := [173]) (l₂ := [174])
  have hm := merge_left (literal (valuationOf q) (173)) (literal (valuationOf q) (337)) (countLit q [173]) (countLit q [174]) (count337 q) 1 (meaning173 q) (meaning337 q) hs
  change valuationOf q 173 = false ∨ valuationOf q 337 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause962 (q : Snake 81) (h : Conditions q) : valuation q 173 = false ∨ valuation q 337 = true := counterClause962 (baseVal q)

theorem counterClause963 (q : Nat → Bool) : valuationOf q 337 = false ∨ valuationOf q 339 = true := by
  have hs : count339 q = (countLit q [171, 172]) + (countLit q [173, 174]) := List.countP_append (p := literal q) (l₁ := [171, 172]) (l₂ := [173, 174])
  have hm := merge_right (literal (valuationOf q) (337)) (literal (valuationOf q) (339)) (countLit q [171, 172]) (countLit q [173, 174]) (count339 q) 1 (meaning337 q) (meaning339 q) hs
  change valuationOf q 337 = false ∨ valuationOf q 339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause963 (q : Snake 81) (h : Conditions q) : valuation q 337 = false ∨ valuation q 339 = true := counterClause963 (baseVal q)

theorem counterClause964 (q : Nat → Bool) : valuationOf q 335 = false ∨ valuationOf q 339 = true := by
  have hs : count339 q = (countLit q [171, 172]) + (countLit q [173, 174]) := List.countP_append (p := literal q) (l₁ := [171, 172]) (l₂ := [173, 174])
  have hm := merge_left (literal (valuationOf q) (335)) (literal (valuationOf q) (339)) (countLit q [171, 172]) (countLit q [173, 174]) (count339 q) 1 (meaning335 q) (meaning339 q) hs
  change valuationOf q 335 = false ∨ valuationOf q 339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause964 (q : Snake 81) (h : Conditions q) : valuation q 335 = false ∨ valuation q 339 = true := counterClause964 (baseVal q)

theorem counterClause965 (q : Nat → Bool) : valuationOf q 335 = false ∨ valuationOf q 337 = false ∨ valuationOf q 340 = true := by
  have hs : count339 q = (countLit q [171, 172]) + (countLit q [173, 174]) := List.countP_append (p := literal q) (l₁ := [171, 172]) (l₂ := [173, 174])
  have hm := merge_two (literal (valuationOf q) (335)) (literal (valuationOf q) (337)) (literal (valuationOf q) (340)) (countLit q [171, 172]) (countLit q [173, 174]) (count339 q) 1 1 (meaning335 q) (meaning337 q) (meaning340 q) hs
  change valuationOf q 335 = false ∨ valuationOf q 337 = false ∨ valuationOf q 340 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause965 (q : Snake 81) (h : Conditions q) : valuation q 335 = false ∨ valuation q 337 = false ∨ valuation q 340 = true := counterClause965 (baseVal q)

theorem counterClause966 (q : Nat → Bool) : valuationOf q 339 = false ∨ valuationOf q 341 = true := by
  have hs : count341 q = (countLit q [167, 168, 169, 170]) + (countLit q [171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [167, 168, 169, 170]) (l₂ := [171, 172, 173, 174])
  have hm := merge_right (literal (valuationOf q) (339)) (literal (valuationOf q) (341)) (countLit q [167, 168, 169, 170]) (countLit q [171, 172, 173, 174]) (count341 q) 1 (meaning339 q) (meaning341 q) hs
  change valuationOf q 339 = false ∨ valuationOf q 341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause966 (q : Snake 81) (h : Conditions q) : valuation q 339 = false ∨ valuation q 341 = true := counterClause966 (baseVal q)

theorem counterClause967 (q : Nat → Bool) : valuationOf q 340 = false ∨ valuationOf q 342 = true := by
  have hs : count341 q = (countLit q [167, 168, 169, 170]) + (countLit q [171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [167, 168, 169, 170]) (l₂ := [171, 172, 173, 174])
  have hm := merge_right (literal (valuationOf q) (340)) (literal (valuationOf q) (342)) (countLit q [167, 168, 169, 170]) (countLit q [171, 172, 173, 174]) (count341 q) 2 (meaning340 q) (meaning342 q) hs
  change valuationOf q 340 = false ∨ valuationOf q 342 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause967 (q : Snake 81) (h : Conditions q) : valuation q 340 = false ∨ valuation q 342 = true := counterClause967 (baseVal q)

theorem counterClause968 (q : Nat → Bool) : valuationOf q 333 = false ∨ valuationOf q 341 = true := by
  have hs : count341 q = (countLit q [167, 168, 169, 170]) + (countLit q [171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [167, 168, 169, 170]) (l₂ := [171, 172, 173, 174])
  have hm := merge_left (literal (valuationOf q) (333)) (literal (valuationOf q) (341)) (countLit q [167, 168, 169, 170]) (countLit q [171, 172, 173, 174]) (count341 q) 1 (meaning333 q) (meaning341 q) hs
  change valuationOf q 333 = false ∨ valuationOf q 341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause968 (q : Snake 81) (h : Conditions q) : valuation q 333 = false ∨ valuation q 341 = true := counterClause968 (baseVal q)

theorem counterClause969 (q : Nat → Bool) : valuationOf q 333 = false ∨ valuationOf q 339 = false ∨ valuationOf q 342 = true := by
  have hs : count341 q = (countLit q [167, 168, 169, 170]) + (countLit q [171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [167, 168, 169, 170]) (l₂ := [171, 172, 173, 174])
  have hm := merge_two (literal (valuationOf q) (333)) (literal (valuationOf q) (339)) (literal (valuationOf q) (342)) (countLit q [167, 168, 169, 170]) (countLit q [171, 172, 173, 174]) (count341 q) 1 1 (meaning333 q) (meaning339 q) (meaning342 q) hs
  change valuationOf q 333 = false ∨ valuationOf q 339 = false ∨ valuationOf q 342 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause969 (q : Snake 81) (h : Conditions q) : valuation q 333 = false ∨ valuation q 339 = false ∨ valuation q 342 = true := counterClause969 (baseVal q)

theorem counterClause970 (q : Nat → Bool) : valuationOf q 341 = false ∨ valuationOf q 343 = true := by
  have hs : count343 q = (countLit q [159, 160, 161, 162, 163, 164, 165, 166]) + (countLit q [167, 168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [159, 160, 161, 162, 163, 164, 165, 166]) (l₂ := [167, 168, 169, 170, 171, 172, 173, 174])
  have hm := merge_right (literal (valuationOf q) (341)) (literal (valuationOf q) (343)) (countLit q [159, 160, 161, 162, 163, 164, 165, 166]) (countLit q [167, 168, 169, 170, 171, 172, 173, 174]) (count343 q) 1 (meaning341 q) (meaning343 q) hs
  change valuationOf q 341 = false ∨ valuationOf q 343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause970 (q : Snake 81) (h : Conditions q) : valuation q 341 = false ∨ valuation q 343 = true := counterClause970 (baseVal q)

theorem counterClause971 (q : Nat → Bool) : valuationOf q 342 = false ∨ valuationOf q 344 = true := by
  have hs : count343 q = (countLit q [159, 160, 161, 162, 163, 164, 165, 166]) + (countLit q [167, 168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [159, 160, 161, 162, 163, 164, 165, 166]) (l₂ := [167, 168, 169, 170, 171, 172, 173, 174])
  have hm := merge_right (literal (valuationOf q) (342)) (literal (valuationOf q) (344)) (countLit q [159, 160, 161, 162, 163, 164, 165, 166]) (countLit q [167, 168, 169, 170, 171, 172, 173, 174]) (count343 q) 2 (meaning342 q) (meaning344 q) hs
  change valuationOf q 342 = false ∨ valuationOf q 344 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause971 (q : Snake 81) (h : Conditions q) : valuation q 342 = false ∨ valuation q 344 = true := counterClause971 (baseVal q)

theorem counterClause972 (q : Nat → Bool) : valuationOf q 327 = false ∨ valuationOf q 343 = true := by
  have hs : count343 q = (countLit q [159, 160, 161, 162, 163, 164, 165, 166]) + (countLit q [167, 168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [159, 160, 161, 162, 163, 164, 165, 166]) (l₂ := [167, 168, 169, 170, 171, 172, 173, 174])
  have hm := merge_left (literal (valuationOf q) (327)) (literal (valuationOf q) (343)) (countLit q [159, 160, 161, 162, 163, 164, 165, 166]) (countLit q [167, 168, 169, 170, 171, 172, 173, 174]) (count343 q) 1 (meaning327 q) (meaning343 q) hs
  change valuationOf q 327 = false ∨ valuationOf q 343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause972 (q : Snake 81) (h : Conditions q) : valuation q 327 = false ∨ valuation q 343 = true := counterClause972 (baseVal q)

theorem counterClause973 (q : Nat → Bool) : valuationOf q 327 = false ∨ valuationOf q 341 = false ∨ valuationOf q 344 = true := by
  have hs : count343 q = (countLit q [159, 160, 161, 162, 163, 164, 165, 166]) + (countLit q [167, 168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [159, 160, 161, 162, 163, 164, 165, 166]) (l₂ := [167, 168, 169, 170, 171, 172, 173, 174])
  have hm := merge_two (literal (valuationOf q) (327)) (literal (valuationOf q) (341)) (literal (valuationOf q) (344)) (countLit q [159, 160, 161, 162, 163, 164, 165, 166]) (countLit q [167, 168, 169, 170, 171, 172, 173, 174]) (count343 q) 1 1 (meaning327 q) (meaning341 q) (meaning344 q) hs
  change valuationOf q 327 = false ∨ valuationOf q 341 = false ∨ valuationOf q 344 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause973 (q : Snake 81) (h : Conditions q) : valuation q 327 = false ∨ valuation q 341 = false ∨ valuation q 344 = true := counterClause973 (baseVal q)

theorem counterClause974 (q : Nat → Bool) : valuationOf q 328 = false ∨ valuationOf q 344 = true := by
  have hs : count343 q = (countLit q [159, 160, 161, 162, 163, 164, 165, 166]) + (countLit q [167, 168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [159, 160, 161, 162, 163, 164, 165, 166]) (l₂ := [167, 168, 169, 170, 171, 172, 173, 174])
  have hm := merge_left (literal (valuationOf q) (328)) (literal (valuationOf q) (344)) (countLit q [159, 160, 161, 162, 163, 164, 165, 166]) (countLit q [167, 168, 169, 170, 171, 172, 173, 174]) (count343 q) 2 (meaning328 q) (meaning344 q) hs
  change valuationOf q 328 = false ∨ valuationOf q 344 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause974 (q : Snake 81) (h : Conditions q) : valuation q 328 = false ∨ valuation q 344 = true := counterClause974 (baseVal q)

theorem counterClause975 (q : Nat → Bool) : valuationOf q 176 = false ∨ valuationOf q 345 = true := by
  have hs : count345 q = (countLit q [175]) + (countLit q [176]) := List.countP_append (p := literal q) (l₁ := [175]) (l₂ := [176])
  have hm := merge_right (literal (valuationOf q) (176)) (literal (valuationOf q) (345)) (countLit q [175]) (countLit q [176]) (count345 q) 1 (meaning176 q) (meaning345 q) hs
  change valuationOf q 176 = false ∨ valuationOf q 345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause975 (q : Snake 81) (h : Conditions q) : valuation q 176 = false ∨ valuation q 345 = true := counterClause975 (baseVal q)

theorem counterClause976 (q : Nat → Bool) : valuationOf q 175 = false ∨ valuationOf q 345 = true := by
  have hs : count345 q = (countLit q [175]) + (countLit q [176]) := List.countP_append (p := literal q) (l₁ := [175]) (l₂ := [176])
  have hm := merge_left (literal (valuationOf q) (175)) (literal (valuationOf q) (345)) (countLit q [175]) (countLit q [176]) (count345 q) 1 (meaning175 q) (meaning345 q) hs
  change valuationOf q 175 = false ∨ valuationOf q 345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause976 (q : Snake 81) (h : Conditions q) : valuation q 175 = false ∨ valuation q 345 = true := counterClause976 (baseVal q)

theorem counterClause977 (q : Nat → Bool) : valuationOf q 178 = false ∨ valuationOf q 347 = true := by
  have hs : count347 q = (countLit q [177]) + (countLit q [178]) := List.countP_append (p := literal q) (l₁ := [177]) (l₂ := [178])
  have hm := merge_right (literal (valuationOf q) (178)) (literal (valuationOf q) (347)) (countLit q [177]) (countLit q [178]) (count347 q) 1 (meaning178 q) (meaning347 q) hs
  change valuationOf q 178 = false ∨ valuationOf q 347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause977 (q : Snake 81) (h : Conditions q) : valuation q 178 = false ∨ valuation q 347 = true := counterClause977 (baseVal q)

theorem counterClause978 (q : Nat → Bool) : valuationOf q 177 = false ∨ valuationOf q 347 = true := by
  have hs : count347 q = (countLit q [177]) + (countLit q [178]) := List.countP_append (p := literal q) (l₁ := [177]) (l₂ := [178])
  have hm := merge_left (literal (valuationOf q) (177)) (literal (valuationOf q) (347)) (countLit q [177]) (countLit q [178]) (count347 q) 1 (meaning177 q) (meaning347 q) hs
  change valuationOf q 177 = false ∨ valuationOf q 347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause978 (q : Snake 81) (h : Conditions q) : valuation q 177 = false ∨ valuation q 347 = true := counterClause978 (baseVal q)

theorem counterClause979 (q : Nat → Bool) : valuationOf q 347 = false ∨ valuationOf q 349 = true := by
  have hs : count349 q = (countLit q [175, 176]) + (countLit q [177, 178]) := List.countP_append (p := literal q) (l₁ := [175, 176]) (l₂ := [177, 178])
  have hm := merge_right (literal (valuationOf q) (347)) (literal (valuationOf q) (349)) (countLit q [175, 176]) (countLit q [177, 178]) (count349 q) 1 (meaning347 q) (meaning349 q) hs
  change valuationOf q 347 = false ∨ valuationOf q 349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause979 (q : Snake 81) (h : Conditions q) : valuation q 347 = false ∨ valuation q 349 = true := counterClause979 (baseVal q)

theorem counterClause980 (q : Nat → Bool) : valuationOf q 345 = false ∨ valuationOf q 349 = true := by
  have hs : count349 q = (countLit q [175, 176]) + (countLit q [177, 178]) := List.countP_append (p := literal q) (l₁ := [175, 176]) (l₂ := [177, 178])
  have hm := merge_left (literal (valuationOf q) (345)) (literal (valuationOf q) (349)) (countLit q [175, 176]) (countLit q [177, 178]) (count349 q) 1 (meaning345 q) (meaning349 q) hs
  change valuationOf q 345 = false ∨ valuationOf q 349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause980 (q : Snake 81) (h : Conditions q) : valuation q 345 = false ∨ valuation q 349 = true := counterClause980 (baseVal q)

theorem counterClause981 (q : Nat → Bool) : valuationOf q 345 = false ∨ valuationOf q 347 = false ∨ valuationOf q 350 = true := by
  have hs : count349 q = (countLit q [175, 176]) + (countLit q [177, 178]) := List.countP_append (p := literal q) (l₁ := [175, 176]) (l₂ := [177, 178])
  have hm := merge_two (literal (valuationOf q) (345)) (literal (valuationOf q) (347)) (literal (valuationOf q) (350)) (countLit q [175, 176]) (countLit q [177, 178]) (count349 q) 1 1 (meaning345 q) (meaning347 q) (meaning350 q) hs
  change valuationOf q 345 = false ∨ valuationOf q 347 = false ∨ valuationOf q 350 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause981 (q : Snake 81) (h : Conditions q) : valuation q 345 = false ∨ valuation q 347 = false ∨ valuation q 350 = true := counterClause981 (baseVal q)

theorem counterClause982 (q : Nat → Bool) : valuationOf q 349 = false ∨ valuationOf q 357 = true := by
  have hs : count357 q = (countLit q [175, 176, 177, 178]) + (countLit q [179, 180, 181, 182]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177, 178]) (l₂ := [179, 180, 181, 182])
  have hm := merge_left (literal (valuationOf q) (349)) (literal (valuationOf q) (357)) (countLit q [175, 176, 177, 178]) (countLit q [179, 180, 181, 182]) (count357 q) 1 (meaning349 q) (meaning357 q) hs
  change valuationOf q 349 = false ∨ valuationOf q 357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause982 (q : Snake 81) (h : Conditions q) : valuation q 349 = false ∨ valuation q 357 = true := counterClause982 (baseVal q)

theorem counterClause983 (q : Nat → Bool) : valuationOf q 350 = false ∨ valuationOf q 358 = true := by
  have hs : count357 q = (countLit q [175, 176, 177, 178]) + (countLit q [179, 180, 181, 182]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177, 178]) (l₂ := [179, 180, 181, 182])
  have hm := merge_left (literal (valuationOf q) (350)) (literal (valuationOf q) (358)) (countLit q [175, 176, 177, 178]) (countLit q [179, 180, 181, 182]) (count357 q) 2 (meaning350 q) (meaning358 q) hs
  change valuationOf q 350 = false ∨ valuationOf q 358 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause983 (q : Snake 81) (h : Conditions q) : valuation q 350 = false ∨ valuation q 358 = true := counterClause983 (baseVal q)

theorem counterClause984 (q : Nat → Bool) : valuationOf q 183 = false ∨ valuationOf q 359 = true := by
  have hs : count359 q = (countLit q [183]) + (countLit q [184]) := List.countP_append (p := literal q) (l₁ := [183]) (l₂ := [184])
  have hm := merge_left (literal (valuationOf q) (183)) (literal (valuationOf q) (359)) (countLit q [183]) (countLit q [184]) (count359 q) 1 (meaning183 q) (meaning359 q) hs
  change valuationOf q 183 = false ∨ valuationOf q 359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause984 (q : Snake 81) (h : Conditions q) : valuation q 183 = false ∨ valuation q 359 = true := counterClause984 (baseVal q)

theorem counterClause985 (q : Nat → Bool) : valuationOf q 359 = false ∨ valuationOf q 363 = true := by
  have hs : count363 q = (countLit q [183, 184]) + (countLit q [185, 186]) := List.countP_append (p := literal q) (l₁ := [183, 184]) (l₂ := [185, 186])
  have hm := merge_left (literal (valuationOf q) (359)) (literal (valuationOf q) (363)) (countLit q [183, 184]) (countLit q [185, 186]) (count363 q) 1 (meaning359 q) (meaning363 q) hs
  change valuationOf q 359 = false ∨ valuationOf q 363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause985 (q : Snake 81) (h : Conditions q) : valuation q 359 = false ∨ valuation q 363 = true := counterClause985 (baseVal q)

theorem counterClause986 (q : Nat → Bool) : valuationOf q 187 = false ∨ valuationOf q 365 = true := by
  have hs : count365 q = (countLit q [187]) + (countLit q [188]) := List.countP_append (p := literal q) (l₁ := [187]) (l₂ := [188])
  have hm := merge_left (literal (valuationOf q) (187)) (literal (valuationOf q) (365)) (countLit q [187]) (countLit q [188]) (count365 q) 1 (meaning187 q) (meaning365 q) hs
  change valuationOf q 187 = false ∨ valuationOf q 365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause986 (q : Snake 81) (h : Conditions q) : valuation q 187 = false ∨ valuation q 365 = true := counterClause986 (baseVal q)

theorem counterClause987 (q : Nat → Bool) : valuationOf q 189 = false ∨ valuationOf q 367 = true := by
  have hs : count367 q = (countLit q [189]) + (countLit q [190]) := List.countP_append (p := literal q) (l₁ := [189]) (l₂ := [190])
  have hm := merge_left (literal (valuationOf q) (189)) (literal (valuationOf q) (367)) (countLit q [189]) (countLit q [190]) (count367 q) 1 (meaning189 q) (meaning367 q) hs
  change valuationOf q 189 = false ∨ valuationOf q 367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause987 (q : Snake 81) (h : Conditions q) : valuation q 189 = false ∨ valuation q 367 = true := counterClause987 (baseVal q)

theorem counterClause988 (q : Nat → Bool) : valuationOf q 367 = false ∨ valuationOf q 369 = true := by
  have hs : count369 q = (countLit q [187, 188]) + (countLit q [189, 190]) := List.countP_append (p := literal q) (l₁ := [187, 188]) (l₂ := [189, 190])
  have hm := merge_right (literal (valuationOf q) (367)) (literal (valuationOf q) (369)) (countLit q [187, 188]) (countLit q [189, 190]) (count369 q) 1 (meaning367 q) (meaning369 q) hs
  change valuationOf q 367 = false ∨ valuationOf q 369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause988 (q : Snake 81) (h : Conditions q) : valuation q 367 = false ∨ valuation q 369 = true := counterClause988 (baseVal q)

theorem counterClause989 (q : Nat → Bool) : valuationOf q 365 = false ∨ valuationOf q 369 = true := by
  have hs : count369 q = (countLit q [187, 188]) + (countLit q [189, 190]) := List.countP_append (p := literal q) (l₁ := [187, 188]) (l₂ := [189, 190])
  have hm := merge_left (literal (valuationOf q) (365)) (literal (valuationOf q) (369)) (countLit q [187, 188]) (countLit q [189, 190]) (count369 q) 1 (meaning365 q) (meaning369 q) hs
  change valuationOf q 365 = false ∨ valuationOf q 369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause989 (q : Snake 81) (h : Conditions q) : valuation q 365 = false ∨ valuation q 369 = true := counterClause989 (baseVal q)

theorem counterClause990 (q : Nat → Bool) : valuationOf q 369 = false ∨ valuationOf q 371 = true := by
  have hs : count371 q = (countLit q [183, 184, 185, 186]) + (countLit q [187, 188, 189, 190]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186]) (l₂ := [187, 188, 189, 190])
  have hm := merge_right (literal (valuationOf q) (369)) (literal (valuationOf q) (371)) (countLit q [183, 184, 185, 186]) (countLit q [187, 188, 189, 190]) (count371 q) 1 (meaning369 q) (meaning371 q) hs
  change valuationOf q 369 = false ∨ valuationOf q 371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause990 (q : Snake 81) (h : Conditions q) : valuation q 369 = false ∨ valuation q 371 = true := counterClause990 (baseVal q)

theorem counterClause991 (q : Nat → Bool) : valuationOf q 363 = false ∨ valuationOf q 371 = true := by
  have hs : count371 q = (countLit q [183, 184, 185, 186]) + (countLit q [187, 188, 189, 190]) := List.countP_append (p := literal q) (l₁ := [183, 184, 185, 186]) (l₂ := [187, 188, 189, 190])
  have hm := merge_left (literal (valuationOf q) (363)) (literal (valuationOf q) (371)) (countLit q [183, 184, 185, 186]) (countLit q [187, 188, 189, 190]) (count371 q) 1 (meaning363 q) (meaning371 q) hs
  change valuationOf q 363 = false ∨ valuationOf q 371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause991 (q : Snake 81) (h : Conditions q) : valuation q 363 = false ∨ valuation q 371 = true := counterClause991 (baseVal q)

theorem counterClause992 (q : Nat → Bool) : valuationOf q 371 = false ∨ valuationOf q 373 = true := by
  have hs : count373 q = (countLit q [175, 176, 177, 178, 179, 180, 181, 182]) + (countLit q [183, 184, 185, 186, 187, 188, 189, 190]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177, 178, 179, 180, 181, 182]) (l₂ := [183, 184, 185, 186, 187, 188, 189, 190])
  have hm := merge_right (literal (valuationOf q) (371)) (literal (valuationOf q) (373)) (countLit q [175, 176, 177, 178, 179, 180, 181, 182]) (countLit q [183, 184, 185, 186, 187, 188, 189, 190]) (count373 q) 1 (meaning371 q) (meaning373 q) hs
  change valuationOf q 371 = false ∨ valuationOf q 373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause992 (q : Snake 81) (h : Conditions q) : valuation q 371 = false ∨ valuation q 373 = true := counterClause992 (baseVal q)

theorem block30 (q : Snake 81) (h : Conditions q) : B112E260.Block30 (valuation q) :=
  ⟨clause961 q h, clause962 q h, clause963 q h, clause964 q h, clause965 q h, clause966 q h, clause967 q h, clause968 q h, clause969 q h, clause970 q h, clause971 q h, clause972 q h, clause973 q h, clause974 q h, clause975 q h, clause976 q h, clause977 q h, clause978 q h, clause979 q h, clause980 q h, clause981 q h, clause982 q h, clause983 q h, clause984 q h, clause985 q h, clause986 q h, clause987 q h, clause988 q h, clause989 q h, clause990 q h, clause991 q h, clause992 q h⟩

end
end Snake9.Regrowth.E112260
