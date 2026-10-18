import E112034Semantics
import B112E034Inputs
namespace Snake9.Regrowth.E112034
noncomputable section
local instance blockDec30 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause961 (q : Nat → Bool) : valuationOf q 335 = false ∨ valuationOf q 343 = true := by
  have hs : count343 q = (countLit q [169, 170, 171, 172]) + (countLit q [173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [169, 170, 171, 172]) (l₂ := [173, 174, 175, 176])
  have hm := merge_left (literal (valuationOf q) (335)) (literal (valuationOf q) (343)) (countLit q [169, 170, 171, 172]) (countLit q [173, 174, 175, 176]) (count343 q) 1 (meaning335 q) (meaning343 q) hs
  change valuationOf q 335 = false ∨ valuationOf q 343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause961 (q : Snake 81) (h : Conditions q) : valuation q 335 = false ∨ valuation q 343 = true := counterClause961 (baseVal q)

theorem counterClause962 (q : Nat → Bool) : valuationOf q 335 = false ∨ valuationOf q 341 = false ∨ valuationOf q 344 = true := by
  have hs : count343 q = (countLit q [169, 170, 171, 172]) + (countLit q [173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [169, 170, 171, 172]) (l₂ := [173, 174, 175, 176])
  have hm := merge_two (literal (valuationOf q) (335)) (literal (valuationOf q) (341)) (literal (valuationOf q) (344)) (countLit q [169, 170, 171, 172]) (countLit q [173, 174, 175, 176]) (count343 q) 1 1 (meaning335 q) (meaning341 q) (meaning344 q) hs
  change valuationOf q 335 = false ∨ valuationOf q 341 = false ∨ valuationOf q 344 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause962 (q : Snake 81) (h : Conditions q) : valuation q 335 = false ∨ valuation q 341 = false ∨ valuation q 344 = true := counterClause962 (baseVal q)

theorem counterClause963 (q : Nat → Bool) : valuationOf q 336 = false ∨ valuationOf q 344 = true := by
  have hs : count343 q = (countLit q [169, 170, 171, 172]) + (countLit q [173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [169, 170, 171, 172]) (l₂ := [173, 174, 175, 176])
  have hm := merge_left (literal (valuationOf q) (336)) (literal (valuationOf q) (344)) (countLit q [169, 170, 171, 172]) (countLit q [173, 174, 175, 176]) (count343 q) 2 (meaning336 q) (meaning344 q) hs
  change valuationOf q 336 = false ∨ valuationOf q 344 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause963 (q : Snake 81) (h : Conditions q) : valuation q 336 = false ∨ valuation q 344 = true := counterClause963 (baseVal q)

theorem counterClause964 (q : Nat → Bool) : valuationOf q 343 = false ∨ valuationOf q 345 = true := by
  have hs : count345 q = (countLit q [161, 162, 163, 164, 165, 166, 167, 168]) + (countLit q [169, 170, 171, 172, 173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [161, 162, 163, 164, 165, 166, 167, 168]) (l₂ := [169, 170, 171, 172, 173, 174, 175, 176])
  have hm := merge_right (literal (valuationOf q) (343)) (literal (valuationOf q) (345)) (countLit q [161, 162, 163, 164, 165, 166, 167, 168]) (countLit q [169, 170, 171, 172, 173, 174, 175, 176]) (count345 q) 1 (meaning343 q) (meaning345 q) hs
  change valuationOf q 343 = false ∨ valuationOf q 345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause964 (q : Snake 81) (h : Conditions q) : valuation q 343 = false ∨ valuation q 345 = true := counterClause964 (baseVal q)

theorem counterClause965 (q : Nat → Bool) : valuationOf q 344 = false ∨ valuationOf q 346 = true := by
  have hs : count345 q = (countLit q [161, 162, 163, 164, 165, 166, 167, 168]) + (countLit q [169, 170, 171, 172, 173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [161, 162, 163, 164, 165, 166, 167, 168]) (l₂ := [169, 170, 171, 172, 173, 174, 175, 176])
  have hm := merge_right (literal (valuationOf q) (344)) (literal (valuationOf q) (346)) (countLit q [161, 162, 163, 164, 165, 166, 167, 168]) (countLit q [169, 170, 171, 172, 173, 174, 175, 176]) (count345 q) 2 (meaning344 q) (meaning346 q) hs
  change valuationOf q 344 = false ∨ valuationOf q 346 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause965 (q : Snake 81) (h : Conditions q) : valuation q 344 = false ∨ valuation q 346 = true := counterClause965 (baseVal q)

theorem counterClause966 (q : Nat → Bool) : valuationOf q 329 = false ∨ valuationOf q 345 = true := by
  have hs : count345 q = (countLit q [161, 162, 163, 164, 165, 166, 167, 168]) + (countLit q [169, 170, 171, 172, 173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [161, 162, 163, 164, 165, 166, 167, 168]) (l₂ := [169, 170, 171, 172, 173, 174, 175, 176])
  have hm := merge_left (literal (valuationOf q) (329)) (literal (valuationOf q) (345)) (countLit q [161, 162, 163, 164, 165, 166, 167, 168]) (countLit q [169, 170, 171, 172, 173, 174, 175, 176]) (count345 q) 1 (meaning329 q) (meaning345 q) hs
  change valuationOf q 329 = false ∨ valuationOf q 345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause966 (q : Snake 81) (h : Conditions q) : valuation q 329 = false ∨ valuation q 345 = true := counterClause966 (baseVal q)

theorem counterClause967 (q : Nat → Bool) : valuationOf q 177 = false ∨ valuationOf q 347 = true := by
  have hs : count347 q = (countLit q [177]) + (countLit q [178]) := List.countP_append (p := literal q) (l₁ := [177]) (l₂ := [178])
  have hm := merge_left (literal (valuationOf q) (177)) (literal (valuationOf q) (347)) (countLit q [177]) (countLit q [178]) (count347 q) 1 (meaning177 q) (meaning347 q) hs
  change valuationOf q 177 = false ∨ valuationOf q 347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause967 (q : Snake 81) (h : Conditions q) : valuation q 177 = false ∨ valuation q 347 = true := counterClause967 (baseVal q)

theorem counterClause968 (q : Nat → Bool) : valuationOf q 347 = false ∨ valuationOf q 351 = true := by
  have hs : count351 q = (countLit q [177, 178]) + (countLit q [179, 180]) := List.countP_append (p := literal q) (l₁ := [177, 178]) (l₂ := [179, 180])
  have hm := merge_left (literal (valuationOf q) (347)) (literal (valuationOf q) (351)) (countLit q [177, 178]) (countLit q [179, 180]) (count351 q) 1 (meaning347 q) (meaning351 q) hs
  change valuationOf q 347 = false ∨ valuationOf q 351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause968 (q : Snake 81) (h : Conditions q) : valuation q 347 = false ∨ valuation q 351 = true := counterClause968 (baseVal q)

theorem counterClause969 (q : Nat → Bool) : valuationOf q 183 = false ∨ valuationOf q 355 = true := by
  have hs : count355 q = (countLit q [183]) + (countLit q [184]) := List.countP_append (p := literal q) (l₁ := [183]) (l₂ := [184])
  have hm := merge_left (literal (valuationOf q) (183)) (literal (valuationOf q) (355)) (countLit q [183]) (countLit q [184]) (count355 q) 1 (meaning183 q) (meaning355 q) hs
  change valuationOf q 183 = false ∨ valuationOf q 355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause969 (q : Snake 81) (h : Conditions q) : valuation q 183 = false ∨ valuation q 355 = true := counterClause969 (baseVal q)

theorem counterClause970 (q : Nat → Bool) : valuationOf q 355 = false ∨ valuationOf q 357 = true := by
  have hs : count357 q = (countLit q [181, 182]) + (countLit q [183, 184]) := List.countP_append (p := literal q) (l₁ := [181, 182]) (l₂ := [183, 184])
  have hm := merge_right (literal (valuationOf q) (355)) (literal (valuationOf q) (357)) (countLit q [181, 182]) (countLit q [183, 184]) (count357 q) 1 (meaning355 q) (meaning357 q) hs
  change valuationOf q 355 = false ∨ valuationOf q 357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause970 (q : Snake 81) (h : Conditions q) : valuation q 355 = false ∨ valuation q 357 = true := counterClause970 (baseVal q)

theorem counterClause971 (q : Nat → Bool) : valuationOf q 357 = false ∨ valuationOf q 359 = true := by
  have hs : count359 q = (countLit q [177, 178, 179, 180]) + (countLit q [181, 182, 183, 184]) := List.countP_append (p := literal q) (l₁ := [177, 178, 179, 180]) (l₂ := [181, 182, 183, 184])
  have hm := merge_right (literal (valuationOf q) (357)) (literal (valuationOf q) (359)) (countLit q [177, 178, 179, 180]) (countLit q [181, 182, 183, 184]) (count359 q) 1 (meaning357 q) (meaning359 q) hs
  change valuationOf q 357 = false ∨ valuationOf q 359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause971 (q : Snake 81) (h : Conditions q) : valuation q 357 = false ∨ valuation q 359 = true := counterClause971 (baseVal q)

theorem counterClause972 (q : Nat → Bool) : valuationOf q 351 = false ∨ valuationOf q 359 = true := by
  have hs : count359 q = (countLit q [177, 178, 179, 180]) + (countLit q [181, 182, 183, 184]) := List.countP_append (p := literal q) (l₁ := [177, 178, 179, 180]) (l₂ := [181, 182, 183, 184])
  have hm := merge_left (literal (valuationOf q) (351)) (literal (valuationOf q) (359)) (countLit q [177, 178, 179, 180]) (countLit q [181, 182, 183, 184]) (count359 q) 1 (meaning351 q) (meaning359 q) hs
  change valuationOf q 351 = false ∨ valuationOf q 359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause972 (q : Snake 81) (h : Conditions q) : valuation q 351 = false ∨ valuation q 359 = true := counterClause972 (baseVal q)

theorem counterClause973 (q : Nat → Bool) : valuationOf q 187 = false ∨ valuationOf q 363 = true := by
  have hs : count363 q = (countLit q [187]) + (countLit q [188]) := List.countP_append (p := literal q) (l₁ := [187]) (l₂ := [188])
  have hm := merge_left (literal (valuationOf q) (187)) (literal (valuationOf q) (363)) (countLit q [187]) (countLit q [188]) (count363 q) 1 (meaning187 q) (meaning363 q) hs
  change valuationOf q 187 = false ∨ valuationOf q 363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause973 (q : Snake 81) (h : Conditions q) : valuation q 187 = false ∨ valuation q 363 = true := counterClause973 (baseVal q)

theorem counterClause974 (q : Nat → Bool) : valuationOf q 363 = false ∨ valuationOf q 365 = true := by
  have hs : count365 q = (countLit q [185, 186]) + (countLit q [187, 188]) := List.countP_append (p := literal q) (l₁ := [185, 186]) (l₂ := [187, 188])
  have hm := merge_right (literal (valuationOf q) (363)) (literal (valuationOf q) (365)) (countLit q [185, 186]) (countLit q [187, 188]) (count365 q) 1 (meaning363 q) (meaning365 q) hs
  change valuationOf q 363 = false ∨ valuationOf q 365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause974 (q : Snake 81) (h : Conditions q) : valuation q 363 = false ∨ valuation q 365 = true := counterClause974 (baseVal q)

theorem counterClause975 (q : Nat → Bool) : valuationOf q 191 = false ∨ valuationOf q 369 = true := by
  have hs : count369 q = (countLit q [191]) + (countLit q [192]) := List.countP_append (p := literal q) (l₁ := [191]) (l₂ := [192])
  have hm := merge_left (literal (valuationOf q) (191)) (literal (valuationOf q) (369)) (countLit q [191]) (countLit q [192]) (count369 q) 1 (meaning191 q) (meaning369 q) hs
  change valuationOf q 191 = false ∨ valuationOf q 369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause975 (q : Snake 81) (h : Conditions q) : valuation q 191 = false ∨ valuation q 369 = true := counterClause975 (baseVal q)

theorem counterClause976 (q : Nat → Bool) : valuationOf q 369 = false ∨ valuationOf q 371 = true := by
  have hs : count371 q = (countLit q [189, 190]) + (countLit q [191, 192]) := List.countP_append (p := literal q) (l₁ := [189, 190]) (l₂ := [191, 192])
  have hm := merge_right (literal (valuationOf q) (369)) (literal (valuationOf q) (371)) (countLit q [189, 190]) (countLit q [191, 192]) (count371 q) 1 (meaning369 q) (meaning371 q) hs
  change valuationOf q 369 = false ∨ valuationOf q 371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause976 (q : Snake 81) (h : Conditions q) : valuation q 369 = false ∨ valuation q 371 = true := counterClause976 (baseVal q)

theorem counterClause977 (q : Nat → Bool) : valuationOf q 371 = false ∨ valuationOf q 373 = true := by
  have hs : count373 q = (countLit q [185, 186, 187, 188]) + (countLit q [189, 190, 191, 192]) := List.countP_append (p := literal q) (l₁ := [185, 186, 187, 188]) (l₂ := [189, 190, 191, 192])
  have hm := merge_right (literal (valuationOf q) (371)) (literal (valuationOf q) (373)) (countLit q [185, 186, 187, 188]) (countLit q [189, 190, 191, 192]) (count373 q) 1 (meaning371 q) (meaning373 q) hs
  change valuationOf q 371 = false ∨ valuationOf q 373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause977 (q : Snake 81) (h : Conditions q) : valuation q 371 = false ∨ valuation q 373 = true := counterClause977 (baseVal q)

theorem counterClause978 (q : Nat → Bool) : valuationOf q 365 = false ∨ valuationOf q 373 = true := by
  have hs : count373 q = (countLit q [185, 186, 187, 188]) + (countLit q [189, 190, 191, 192]) := List.countP_append (p := literal q) (l₁ := [185, 186, 187, 188]) (l₂ := [189, 190, 191, 192])
  have hm := merge_left (literal (valuationOf q) (365)) (literal (valuationOf q) (373)) (countLit q [185, 186, 187, 188]) (countLit q [189, 190, 191, 192]) (count373 q) 1 (meaning365 q) (meaning373 q) hs
  change valuationOf q 365 = false ∨ valuationOf q 373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause978 (q : Snake 81) (h : Conditions q) : valuation q 365 = false ∨ valuation q 373 = true := counterClause978 (baseVal q)

theorem counterClause979 (q : Nat → Bool) : valuationOf q 373 = false ∨ valuationOf q 375 = true := by
  have hs : count375 q = (countLit q [177, 178, 179, 180, 181, 182, 183, 184]) + (countLit q [185, 186, 187, 188, 189, 190, 191, 192]) := List.countP_append (p := literal q) (l₁ := [177, 178, 179, 180, 181, 182, 183, 184]) (l₂ := [185, 186, 187, 188, 189, 190, 191, 192])
  have hm := merge_right (literal (valuationOf q) (373)) (literal (valuationOf q) (375)) (countLit q [177, 178, 179, 180, 181, 182, 183, 184]) (countLit q [185, 186, 187, 188, 189, 190, 191, 192]) (count375 q) 1 (meaning373 q) (meaning375 q) hs
  change valuationOf q 373 = false ∨ valuationOf q 375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause979 (q : Snake 81) (h : Conditions q) : valuation q 373 = false ∨ valuation q 375 = true := counterClause979 (baseVal q)

theorem counterClause980 (q : Nat → Bool) : valuationOf q 359 = false ∨ valuationOf q 375 = true := by
  have hs : count375 q = (countLit q [177, 178, 179, 180, 181, 182, 183, 184]) + (countLit q [185, 186, 187, 188, 189, 190, 191, 192]) := List.countP_append (p := literal q) (l₁ := [177, 178, 179, 180, 181, 182, 183, 184]) (l₂ := [185, 186, 187, 188, 189, 190, 191, 192])
  have hm := merge_left (literal (valuationOf q) (359)) (literal (valuationOf q) (375)) (countLit q [177, 178, 179, 180, 181, 182, 183, 184]) (countLit q [185, 186, 187, 188, 189, 190, 191, 192]) (count375 q) 1 (meaning359 q) (meaning375 q) hs
  change valuationOf q 359 = false ∨ valuationOf q 375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause980 (q : Snake 81) (h : Conditions q) : valuation q 359 = false ∨ valuation q 375 = true := counterClause980 (baseVal q)

theorem counterClause981 (q : Nat → Bool) : valuationOf q 375 = false ∨ valuationOf q 377 = true := by
  have hs : count377 q = (countLit q [161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) + (countLit q [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) := List.countP_append (p := literal q) (l₁ := [161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) (l₂ := [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192])
  have hm := merge_right (literal (valuationOf q) (375)) (literal (valuationOf q) (377)) (countLit q [161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) (countLit q [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (count377 q) 1 (meaning375 q) (meaning377 q) hs
  change valuationOf q 375 = false ∨ valuationOf q 377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause981 (q : Snake 81) (h : Conditions q) : valuation q 375 = false ∨ valuation q 377 = true := counterClause981 (baseVal q)

theorem counterClause982 (q : Nat → Bool) : valuationOf q 345 = false ∨ valuationOf q 377 = true := by
  have hs : count377 q = (countLit q [161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) + (countLit q [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) := List.countP_append (p := literal q) (l₁ := [161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) (l₂ := [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192])
  have hm := merge_left (literal (valuationOf q) (345)) (literal (valuationOf q) (377)) (countLit q [161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) (countLit q [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (count377 q) 1 (meaning345 q) (meaning377 q) hs
  change valuationOf q 345 = false ∨ valuationOf q 377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause982 (q : Snake 81) (h : Conditions q) : valuation q 345 = false ∨ valuation q 377 = true := counterClause982 (baseVal q)

theorem counterClause983 (q : Nat → Bool) : valuationOf q 345 = false ∨ valuationOf q 375 = false ∨ valuationOf q 378 = true := by
  have hs : count377 q = (countLit q [161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) + (countLit q [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) := List.countP_append (p := literal q) (l₁ := [161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) (l₂ := [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192])
  have hm := merge_two (literal (valuationOf q) (345)) (literal (valuationOf q) (375)) (literal (valuationOf q) (378)) (countLit q [161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) (countLit q [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (count377 q) 1 1 (meaning345 q) (meaning375 q) (meaning378 q) hs
  change valuationOf q 345 = false ∨ valuationOf q 375 = false ∨ valuationOf q 378 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause983 (q : Snake 81) (h : Conditions q) : valuation q 345 = false ∨ valuation q 375 = false ∨ valuation q 378 = true := counterClause983 (baseVal q)

theorem counterClause984 (q : Nat → Bool) : valuationOf q 346 = false ∨ valuationOf q 378 = true := by
  have hs : count377 q = (countLit q [161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) + (countLit q [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) := List.countP_append (p := literal q) (l₁ := [161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) (l₂ := [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192])
  have hm := merge_left (literal (valuationOf q) (346)) (literal (valuationOf q) (378)) (countLit q [161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) (countLit q [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (count377 q) 2 (meaning346 q) (meaning378 q) hs
  change valuationOf q 346 = false ∨ valuationOf q 378 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause984 (q : Snake 81) (h : Conditions q) : valuation q 346 = false ∨ valuation q 378 = true := counterClause984 (baseVal q)

theorem counterClause985 (q : Nat → Bool) : valuationOf q 377 = false ∨ valuationOf q 379 = true := by
  have hs : count379 q = (countLit q [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) + (countLit q [161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) := List.countP_append (p := literal q) (l₁ := [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) (l₂ := [161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192])
  have hm := merge_right (literal (valuationOf q) (377)) (literal (valuationOf q) (379)) (countLit q [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) (countLit q [161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (count379 q) 1 (meaning377 q) (meaning379 q) hs
  change valuationOf q 377 = false ∨ valuationOf q 379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause985 (q : Snake 81) (h : Conditions q) : valuation q 377 = false ∨ valuation q 379 = true := counterClause985 (baseVal q)

theorem counterClause986 (q : Nat → Bool) : valuationOf q 378 = false ∨ valuationOf q 380 = true := by
  have hs : count379 q = (countLit q [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) + (countLit q [161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) := List.countP_append (p := literal q) (l₁ := [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) (l₂ := [161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192])
  have hm := merge_right (literal (valuationOf q) (378)) (literal (valuationOf q) (380)) (countLit q [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) (countLit q [161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (count379 q) 2 (meaning378 q) (meaning380 q) hs
  change valuationOf q 378 = false ∨ valuationOf q 380 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause986 (q : Snake 81) (h : Conditions q) : valuation q 378 = false ∨ valuation q 380 = true := counterClause986 (baseVal q)

theorem counterClause987 (q : Nat → Bool) : valuationOf q 315 = false ∨ valuationOf q 379 = true := by
  have hs : count379 q = (countLit q [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) + (countLit q [161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) := List.countP_append (p := literal q) (l₁ := [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) (l₂ := [161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192])
  have hm := merge_left (literal (valuationOf q) (315)) (literal (valuationOf q) (379)) (countLit q [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) (countLit q [161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (count379 q) 1 (meaning315 q) (meaning379 q) hs
  change valuationOf q 315 = false ∨ valuationOf q 379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause987 (q : Snake 81) (h : Conditions q) : valuation q 315 = false ∨ valuation q 379 = true := counterClause987 (baseVal q)

theorem counterClause988 (q : Nat → Bool) : valuationOf q 315 = false ∨ valuationOf q 377 = false ∨ valuationOf q 380 = true := by
  have hs : count379 q = (countLit q [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) + (countLit q [161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) := List.countP_append (p := literal q) (l₁ := [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) (l₂ := [161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192])
  have hm := merge_two (literal (valuationOf q) (315)) (literal (valuationOf q) (377)) (literal (valuationOf q) (380)) (countLit q [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) (countLit q [161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (count379 q) 1 1 (meaning315 q) (meaning377 q) (meaning380 q) hs
  change valuationOf q 315 = false ∨ valuationOf q 377 = false ∨ valuationOf q 380 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause988 (q : Snake 81) (h : Conditions q) : valuation q 315 = false ∨ valuation q 377 = false ∨ valuation q 380 = true := counterClause988 (baseVal q)

theorem counterClause989 (q : Nat → Bool) : valuationOf q 316 = false ∨ valuationOf q 380 = true := by
  have hs : count379 q = (countLit q [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) + (countLit q [161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) := List.countP_append (p := literal q) (l₁ := [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) (l₂ := [161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192])
  have hm := merge_left (literal (valuationOf q) (316)) (literal (valuationOf q) (380)) (countLit q [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]) (countLit q [161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (count379 q) 2 (meaning316 q) (meaning380 q) hs
  change valuationOf q 316 = false ∨ valuationOf q 380 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause989 (q : Snake 81) (h : Conditions q) : valuation q 316 = false ∨ valuation q 380 = true := counterClause989 (baseVal q)

theorem counterClause990 (q : Nat → Bool) : valuationOf q 194 = false ∨ valuationOf q 381 = true := by
  have hs : count381 q = (countLit q [193]) + (countLit q [194]) := List.countP_append (p := literal q) (l₁ := [193]) (l₂ := [194])
  have hm := merge_right (literal (valuationOf q) (194)) (literal (valuationOf q) (381)) (countLit q [193]) (countLit q [194]) (count381 q) 1 (meaning194 q) (meaning381 q) hs
  change valuationOf q 194 = false ∨ valuationOf q 381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause990 (q : Snake 81) (h : Conditions q) : valuation q 194 = false ∨ valuation q 381 = true := counterClause990 (baseVal q)

theorem counterClause991 (q : Nat → Bool) : valuationOf q 381 = false ∨ valuationOf q 385 = true := by
  have hs : count385 q = (countLit q [193, 194]) + (countLit q [195, 196]) := List.countP_append (p := literal q) (l₁ := [193, 194]) (l₂ := [195, 196])
  have hm := merge_left (literal (valuationOf q) (381)) (literal (valuationOf q) (385)) (countLit q [193, 194]) (countLit q [195, 196]) (count385 q) 1 (meaning381 q) (meaning385 q) hs
  change valuationOf q 381 = false ∨ valuationOf q 385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause991 (q : Snake 81) (h : Conditions q) : valuation q 381 = false ∨ valuation q 385 = true := counterClause991 (baseVal q)

theorem counterClause992 (q : Nat → Bool) : valuationOf q 197 = false ∨ valuationOf q 387 = true := by
  have hs : count387 q = (countLit q [197]) + (countLit q [198]) := List.countP_append (p := literal q) (l₁ := [197]) (l₂ := [198])
  have hm := merge_left (literal (valuationOf q) (197)) (literal (valuationOf q) (387)) (countLit q [197]) (countLit q [198]) (count387 q) 1 (meaning197 q) (meaning387 q) hs
  change valuationOf q 197 = false ∨ valuationOf q 387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause992 (q : Snake 81) (h : Conditions q) : valuation q 197 = false ∨ valuation q 387 = true := counterClause992 (baseVal q)

theorem block30 (q : Snake 81) (h : Conditions q) : B112E034.Block30 (valuation q) :=
  ⟨clause961 q h, clause962 q h, clause963 q h, clause964 q h, clause965 q h, clause966 q h, clause967 q h, clause968 q h, clause969 q h, clause970 q h, clause971 q h, clause972 q h, clause973 q h, clause974 q h, clause975 q h, clause976 q h, clause977 q h, clause978 q h, clause979 q h, clause980 q h, clause981 q h, clause982 q h, clause983 q h, clause984 q h, clause985 q h, clause986 q h, clause987 q h, clause988 q h, clause989 q h, clause990 q h, clause991 q h, clause992 q h⟩

end
end Snake9.Regrowth.E112034
