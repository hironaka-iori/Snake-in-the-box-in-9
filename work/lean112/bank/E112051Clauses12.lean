import E112051Semantics
import B112E051Inputs
namespace Snake9.Regrowth.E112051
noncomputable section
local instance blockDec12 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause385 (q : Nat → Bool) : valuationOf q 282 = false ∨ valuationOf q 284 = true := by
  have hs : count283 q = (countLit q [131, 132, 133, 134, 135, 136, 137]) + (countLit q [138, 139, 140, 141, 142, 143, 144]) := List.countP_append (p := literal q) (l₁ := [131, 132, 133, 134, 135, 136, 137]) (l₂ := [138, 139, 140, 141, 142, 143, 144])
  have hm := merge_right (literal (valuationOf q) (282)) (literal (valuationOf q) (284)) (countLit q [131, 132, 133, 134, 135, 136, 137]) (countLit q [138, 139, 140, 141, 142, 143, 144]) (count283 q) 2 (meaning282 q) (meaning284 q) hs
  change valuationOf q 282 = false ∨ valuationOf q 284 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause385 (q : Snake 81) (h : Conditions q) : valuation q 282 = false ∨ valuation q 284 = true := counterClause385 (baseVal q)

theorem counterClause386 (q : Nat → Bool) : valuationOf q 269 = false ∨ valuationOf q 283 = true := by
  have hs : count283 q = (countLit q [131, 132, 133, 134, 135, 136, 137]) + (countLit q [138, 139, 140, 141, 142, 143, 144]) := List.countP_append (p := literal q) (l₁ := [131, 132, 133, 134, 135, 136, 137]) (l₂ := [138, 139, 140, 141, 142, 143, 144])
  have hm := merge_left (literal (valuationOf q) (269)) (literal (valuationOf q) (283)) (countLit q [131, 132, 133, 134, 135, 136, 137]) (countLit q [138, 139, 140, 141, 142, 143, 144]) (count283 q) 1 (meaning269 q) (meaning283 q) hs
  change valuationOf q 269 = false ∨ valuationOf q 283 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause386 (q : Snake 81) (h : Conditions q) : valuation q 269 = false ∨ valuation q 283 = true := counterClause386 (baseVal q)

theorem counterClause387 (q : Nat → Bool) : valuationOf q 269 = false ∨ valuationOf q 281 = false ∨ valuationOf q 284 = true := by
  have hs : count283 q = (countLit q [131, 132, 133, 134, 135, 136, 137]) + (countLit q [138, 139, 140, 141, 142, 143, 144]) := List.countP_append (p := literal q) (l₁ := [131, 132, 133, 134, 135, 136, 137]) (l₂ := [138, 139, 140, 141, 142, 143, 144])
  have hm := merge_two (literal (valuationOf q) (269)) (literal (valuationOf q) (281)) (literal (valuationOf q) (284)) (countLit q [131, 132, 133, 134, 135, 136, 137]) (countLit q [138, 139, 140, 141, 142, 143, 144]) (count283 q) 1 1 (meaning269 q) (meaning281 q) (meaning284 q) hs
  change valuationOf q 269 = false ∨ valuationOf q 281 = false ∨ valuationOf q 284 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause387 (q : Snake 81) (h : Conditions q) : valuation q 269 = false ∨ valuation q 281 = false ∨ valuation q 284 = true := counterClause387 (baseVal q)

theorem counterClause388 (q : Nat → Bool) : valuationOf q 270 = false ∨ valuationOf q 284 = true := by
  have hs : count283 q = (countLit q [131, 132, 133, 134, 135, 136, 137]) + (countLit q [138, 139, 140, 141, 142, 143, 144]) := List.countP_append (p := literal q) (l₁ := [131, 132, 133, 134, 135, 136, 137]) (l₂ := [138, 139, 140, 141, 142, 143, 144])
  have hm := merge_left (literal (valuationOf q) (270)) (literal (valuationOf q) (284)) (countLit q [131, 132, 133, 134, 135, 136, 137]) (countLit q [138, 139, 140, 141, 142, 143, 144]) (count283 q) 2 (meaning270 q) (meaning284 q) hs
  change valuationOf q 270 = false ∨ valuationOf q 284 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause388 (q : Snake 81) (h : Conditions q) : valuation q 270 = false ∨ valuation q 284 = true := counterClause388 (baseVal q)

theorem counterClause389 (q : Nat → Bool) : valuationOf q 283 = false ∨ valuationOf q 285 = true := by
  have hs : count285 q = (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130]) + (countLit q [131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130]) (l₂ := [131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144])
  have hm := merge_right (literal (valuationOf q) (283)) (literal (valuationOf q) (285)) (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130]) (countLit q [131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) (count285 q) 1 (meaning283 q) (meaning285 q) hs
  change valuationOf q 283 = false ∨ valuationOf q 285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause389 (q : Snake 81) (h : Conditions q) : valuation q 283 = false ∨ valuation q 285 = true := counterClause389 (baseVal q)

theorem counterClause390 (q : Nat → Bool) : valuationOf q 284 = false ∨ valuationOf q 286 = true := by
  have hs : count285 q = (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130]) + (countLit q [131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130]) (l₂ := [131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144])
  have hm := merge_right (literal (valuationOf q) (284)) (literal (valuationOf q) (286)) (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130]) (countLit q [131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) (count285 q) 2 (meaning284 q) (meaning286 q) hs
  change valuationOf q 284 = false ∨ valuationOf q 286 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause390 (q : Snake 81) (h : Conditions q) : valuation q 284 = false ∨ valuation q 286 = true := counterClause390 (baseVal q)

theorem counterClause391 (q : Nat → Bool) : valuationOf q 257 = false ∨ valuationOf q 285 = true := by
  have hs : count285 q = (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130]) + (countLit q [131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130]) (l₂ := [131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144])
  have hm := merge_left (literal (valuationOf q) (257)) (literal (valuationOf q) (285)) (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130]) (countLit q [131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) (count285 q) 1 (meaning257 q) (meaning285 q) hs
  change valuationOf q 257 = false ∨ valuationOf q 285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause391 (q : Snake 81) (h : Conditions q) : valuation q 257 = false ∨ valuation q 285 = true := counterClause391 (baseVal q)

theorem counterClause392 (q : Nat → Bool) : valuationOf q 257 = false ∨ valuationOf q 283 = false ∨ valuationOf q 286 = true := by
  have hs : count285 q = (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130]) + (countLit q [131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130]) (l₂ := [131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144])
  have hm := merge_two (literal (valuationOf q) (257)) (literal (valuationOf q) (283)) (literal (valuationOf q) (286)) (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130]) (countLit q [131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) (count285 q) 1 1 (meaning257 q) (meaning283 q) (meaning286 q) hs
  change valuationOf q 257 = false ∨ valuationOf q 283 = false ∨ valuationOf q 286 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause392 (q : Snake 81) (h : Conditions q) : valuation q 257 = false ∨ valuation q 283 = false ∨ valuation q 286 = true := counterClause392 (baseVal q)

theorem counterClause393 (q : Nat → Bool) : valuationOf q 258 = false ∨ valuationOf q 286 = true := by
  have hs : count285 q = (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130]) + (countLit q [131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130]) (l₂ := [131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144])
  have hm := merge_left (literal (valuationOf q) (258)) (literal (valuationOf q) (286)) (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130]) (countLit q [131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]) (count285 q) 2 (meaning258 q) (meaning286 q) hs
  change valuationOf q 258 = false ∨ valuationOf q 286 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause393 (q : Snake 81) (h : Conditions q) : valuation q 258 = false ∨ valuation q 286 = true := counterClause393 (baseVal q)

theorem counterClause394 (q : Nat → Bool) : valuationOf q 145 = false ∨ valuationOf q 289 = true := by
  have hs : count289 q = (countLit q [145]) + (countLit q [146, 147]) := List.countP_append (p := literal q) (l₁ := [145]) (l₂ := [146, 147])
  have hm := merge_left (literal (valuationOf q) (145)) (literal (valuationOf q) (289)) (countLit q [145]) (countLit q [146, 147]) (count289 q) 1 (meaning145 q) (meaning289 q) hs
  change valuationOf q 145 = false ∨ valuationOf q 289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause394 (q : Snake 81) (h : Conditions q) : valuation q 145 = false ∨ valuation q 289 = true := counterClause394 (baseVal q)

theorem counterClause395 (q : Nat → Bool) : valuationOf q 149 = false ∨ valuationOf q 291 = true := by
  have hs : count291 q = (countLit q [148]) + (countLit q [149]) := List.countP_append (p := literal q) (l₁ := [148]) (l₂ := [149])
  have hm := merge_right (literal (valuationOf q) (149)) (literal (valuationOf q) (291)) (countLit q [148]) (countLit q [149]) (count291 q) 1 (meaning149 q) (meaning291 q) hs
  change valuationOf q 149 = false ∨ valuationOf q 291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause395 (q : Snake 81) (h : Conditions q) : valuation q 149 = false ∨ valuation q 291 = true := counterClause395 (baseVal q)

theorem counterClause396 (q : Nat → Bool) : valuationOf q 151 = false ∨ valuationOf q 293 = true := by
  have hs : count293 q = (countLit q [150]) + (countLit q [151]) := List.countP_append (p := literal q) (l₁ := [150]) (l₂ := [151])
  have hm := merge_right (literal (valuationOf q) (151)) (literal (valuationOf q) (293)) (countLit q [150]) (countLit q [151]) (count293 q) 1 (meaning151 q) (meaning293 q) hs
  change valuationOf q 151 = false ∨ valuationOf q 293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause396 (q : Snake 81) (h : Conditions q) : valuation q 151 = false ∨ valuation q 293 = true := counterClause396 (baseVal q)

theorem counterClause397 (q : Nat → Bool) : valuationOf q 293 = false ∨ valuationOf q 295 = true := by
  have hs : count295 q = (countLit q [148, 149]) + (countLit q [150, 151]) := List.countP_append (p := literal q) (l₁ := [148, 149]) (l₂ := [150, 151])
  have hm := merge_right (literal (valuationOf q) (293)) (literal (valuationOf q) (295)) (countLit q [148, 149]) (countLit q [150, 151]) (count295 q) 1 (meaning293 q) (meaning295 q) hs
  change valuationOf q 293 = false ∨ valuationOf q 295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause397 (q : Snake 81) (h : Conditions q) : valuation q 293 = false ∨ valuation q 295 = true := counterClause397 (baseVal q)

theorem counterClause398 (q : Nat → Bool) : valuationOf q 291 = false ∨ valuationOf q 295 = true := by
  have hs : count295 q = (countLit q [148, 149]) + (countLit q [150, 151]) := List.countP_append (p := literal q) (l₁ := [148, 149]) (l₂ := [150, 151])
  have hm := merge_left (literal (valuationOf q) (291)) (literal (valuationOf q) (295)) (countLit q [148, 149]) (countLit q [150, 151]) (count295 q) 1 (meaning291 q) (meaning295 q) hs
  change valuationOf q 291 = false ∨ valuationOf q 295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause398 (q : Snake 81) (h : Conditions q) : valuation q 291 = false ∨ valuation q 295 = true := counterClause398 (baseVal q)

theorem counterClause399 (q : Nat → Bool) : valuationOf q 295 = false ∨ valuationOf q 297 = true := by
  have hs : count297 q = (countLit q [145, 146, 147]) + (countLit q [148, 149, 150, 151]) := List.countP_append (p := literal q) (l₁ := [145, 146, 147]) (l₂ := [148, 149, 150, 151])
  have hm := merge_right (literal (valuationOf q) (295)) (literal (valuationOf q) (297)) (countLit q [145, 146, 147]) (countLit q [148, 149, 150, 151]) (count297 q) 1 (meaning295 q) (meaning297 q) hs
  change valuationOf q 295 = false ∨ valuationOf q 297 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause399 (q : Snake 81) (h : Conditions q) : valuation q 295 = false ∨ valuation q 297 = true := counterClause399 (baseVal q)

theorem counterClause400 (q : Nat → Bool) : valuationOf q 289 = false ∨ valuationOf q 297 = true := by
  have hs : count297 q = (countLit q [145, 146, 147]) + (countLit q [148, 149, 150, 151]) := List.countP_append (p := literal q) (l₁ := [145, 146, 147]) (l₂ := [148, 149, 150, 151])
  have hm := merge_left (literal (valuationOf q) (289)) (literal (valuationOf q) (297)) (countLit q [145, 146, 147]) (countLit q [148, 149, 150, 151]) (count297 q) 1 (meaning289 q) (meaning297 q) hs
  change valuationOf q 289 = false ∨ valuationOf q 297 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause400 (q : Snake 81) (h : Conditions q) : valuation q 289 = false ∨ valuation q 297 = true := counterClause400 (baseVal q)

theorem counterClause401 (q : Nat → Bool) : valuationOf q 297 = false ∨ valuationOf q 311 = true := by
  have hs : count311 q = (countLit q [145, 146, 147, 148, 149, 150, 151]) + (countLit q [152, 153, 154, 155, 156, 157, 158]) := List.countP_append (p := literal q) (l₁ := [145, 146, 147, 148, 149, 150, 151]) (l₂ := [152, 153, 154, 155, 156, 157, 158])
  have hm := merge_left (literal (valuationOf q) (297)) (literal (valuationOf q) (311)) (countLit q [145, 146, 147, 148, 149, 150, 151]) (countLit q [152, 153, 154, 155, 156, 157, 158]) (count311 q) 1 (meaning297 q) (meaning311 q) hs
  change valuationOf q 297 = false ∨ valuationOf q 311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause401 (q : Snake 81) (h : Conditions q) : valuation q 297 = false ∨ valuation q 311 = true := counterClause401 (baseVal q)

theorem counterClause402 (q : Nat → Bool) : valuationOf q 160 = false ∨ valuationOf q 313 = true := by
  have hs : count313 q = (countLit q [160]) + (countLit q [161]) := List.countP_append (p := literal q) (l₁ := [160]) (l₂ := [161])
  have hm := merge_left (literal (valuationOf q) (160)) (literal (valuationOf q) (313)) (countLit q [160]) (countLit q [161]) (count313 q) 1 (meaning160 q) (meaning313 q) hs
  change valuationOf q 160 = false ∨ valuationOf q 313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause402 (q : Snake 81) (h : Conditions q) : valuation q 160 = false ∨ valuation q 313 = true := counterClause402 (baseVal q)

theorem counterClause403 (q : Nat → Bool) : valuationOf q 313 = false ∨ valuationOf q 315 = true := by
  have hs : count315 q = (countLit q [159]) + (countLit q [160, 161]) := List.countP_append (p := literal q) (l₁ := [159]) (l₂ := [160, 161])
  have hm := merge_right (literal (valuationOf q) (313)) (literal (valuationOf q) (315)) (countLit q [159]) (countLit q [160, 161]) (count315 q) 1 (meaning313 q) (meaning315 q) hs
  change valuationOf q 313 = false ∨ valuationOf q 315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause403 (q : Snake 81) (h : Conditions q) : valuation q 313 = false ∨ valuation q 315 = true := counterClause403 (baseVal q)

theorem counterClause404 (q : Nat → Bool) : valuationOf q 162 = false ∨ valuationOf q 317 = true := by
  have hs : count317 q = (countLit q [162]) + (countLit q [163]) := List.countP_append (p := literal q) (l₁ := [162]) (l₂ := [163])
  have hm := merge_left (literal (valuationOf q) (162)) (literal (valuationOf q) (317)) (countLit q [162]) (countLit q [163]) (count317 q) 1 (meaning162 q) (meaning317 q) hs
  change valuationOf q 162 = false ∨ valuationOf q 317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause404 (q : Snake 81) (h : Conditions q) : valuation q 162 = false ∨ valuation q 317 = true := counterClause404 (baseVal q)

theorem counterClause405 (q : Nat → Bool) : valuationOf q 317 = false ∨ valuationOf q 321 = true := by
  have hs : count321 q = (countLit q [162, 163]) + (countLit q [164, 165]) := List.countP_append (p := literal q) (l₁ := [162, 163]) (l₂ := [164, 165])
  have hm := merge_left (literal (valuationOf q) (317)) (literal (valuationOf q) (321)) (countLit q [162, 163]) (countLit q [164, 165]) (count321 q) 1 (meaning317 q) (meaning321 q) hs
  change valuationOf q 317 = false ∨ valuationOf q 321 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause405 (q : Snake 81) (h : Conditions q) : valuation q 317 = false ∨ valuation q 321 = true := counterClause405 (baseVal q)

theorem counterClause406 (q : Nat → Bool) : valuationOf q 321 = false ∨ valuationOf q 323 = true := by
  have hs : count323 q = (countLit q [159, 160, 161]) + (countLit q [162, 163, 164, 165]) := List.countP_append (p := literal q) (l₁ := [159, 160, 161]) (l₂ := [162, 163, 164, 165])
  have hm := merge_right (literal (valuationOf q) (321)) (literal (valuationOf q) (323)) (countLit q [159, 160, 161]) (countLit q [162, 163, 164, 165]) (count323 q) 1 (meaning321 q) (meaning323 q) hs
  change valuationOf q 321 = false ∨ valuationOf q 323 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause406 (q : Snake 81) (h : Conditions q) : valuation q 321 = false ∨ valuation q 323 = true := counterClause406 (baseVal q)

theorem counterClause407 (q : Nat → Bool) : valuationOf q 315 = false ∨ valuationOf q 323 = true := by
  have hs : count323 q = (countLit q [159, 160, 161]) + (countLit q [162, 163, 164, 165]) := List.countP_append (p := literal q) (l₁ := [159, 160, 161]) (l₂ := [162, 163, 164, 165])
  have hm := merge_left (literal (valuationOf q) (315)) (literal (valuationOf q) (323)) (countLit q [159, 160, 161]) (countLit q [162, 163, 164, 165]) (count323 q) 1 (meaning315 q) (meaning323 q) hs
  change valuationOf q 315 = false ∨ valuationOf q 323 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause407 (q : Snake 81) (h : Conditions q) : valuation q 315 = false ∨ valuation q 323 = true := counterClause407 (baseVal q)

theorem counterClause408 (q : Nat → Bool) : valuationOf q 169 = false ∨ valuationOf q 327 = true := by
  have hs : count327 q = (countLit q [168]) + (countLit q [169]) := List.countP_append (p := literal q) (l₁ := [168]) (l₂ := [169])
  have hm := merge_right (literal (valuationOf q) (169)) (literal (valuationOf q) (327)) (countLit q [168]) (countLit q [169]) (count327 q) 1 (meaning169 q) (meaning327 q) hs
  change valuationOf q 169 = false ∨ valuationOf q 327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause408 (q : Snake 81) (h : Conditions q) : valuation q 169 = false ∨ valuation q 327 = true := counterClause408 (baseVal q)

theorem counterClause409 (q : Nat → Bool) : valuationOf q 168 = false ∨ valuationOf q 327 = true := by
  have hs : count327 q = (countLit q [168]) + (countLit q [169]) := List.countP_append (p := literal q) (l₁ := [168]) (l₂ := [169])
  have hm := merge_left (literal (valuationOf q) (168)) (literal (valuationOf q) (327)) (countLit q [168]) (countLit q [169]) (count327 q) 1 (meaning168 q) (meaning327 q) hs
  change valuationOf q 168 = false ∨ valuationOf q 327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause409 (q : Snake 81) (h : Conditions q) : valuation q 168 = false ∨ valuation q 327 = true := counterClause409 (baseVal q)

theorem counterClause410 (q : Nat → Bool) : valuationOf q 327 = false ∨ valuationOf q 329 = true := by
  have hs : count329 q = (countLit q [166, 167]) + (countLit q [168, 169]) := List.countP_append (p := literal q) (l₁ := [166, 167]) (l₂ := [168, 169])
  have hm := merge_right (literal (valuationOf q) (327)) (literal (valuationOf q) (329)) (countLit q [166, 167]) (countLit q [168, 169]) (count329 q) 1 (meaning327 q) (meaning329 q) hs
  change valuationOf q 327 = false ∨ valuationOf q 329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause410 (q : Snake 81) (h : Conditions q) : valuation q 327 = false ∨ valuation q 329 = true := counterClause410 (baseVal q)

theorem counterClause411 (q : Nat → Bool) : valuationOf q 329 = false ∨ valuationOf q 337 = true := by
  have hs : count337 q = (countLit q [166, 167, 168, 169]) + (countLit q [170, 171, 172, 173]) := List.countP_append (p := literal q) (l₁ := [166, 167, 168, 169]) (l₂ := [170, 171, 172, 173])
  have hm := merge_left (literal (valuationOf q) (329)) (literal (valuationOf q) (337)) (countLit q [166, 167, 168, 169]) (countLit q [170, 171, 172, 173]) (count337 q) 1 (meaning329 q) (meaning337 q) hs
  change valuationOf q 329 = false ∨ valuationOf q 337 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause411 (q : Snake 81) (h : Conditions q) : valuation q 329 = false ∨ valuation q 337 = true := counterClause411 (baseVal q)

theorem counterClause412 (q : Nat → Bool) : valuationOf q 337 = false ∨ valuationOf q 339 = true := by
  have hs : count339 q = (countLit q [159, 160, 161, 162, 163, 164, 165]) + (countLit q [166, 167, 168, 169, 170, 171, 172, 173]) := List.countP_append (p := literal q) (l₁ := [159, 160, 161, 162, 163, 164, 165]) (l₂ := [166, 167, 168, 169, 170, 171, 172, 173])
  have hm := merge_right (literal (valuationOf q) (337)) (literal (valuationOf q) (339)) (countLit q [159, 160, 161, 162, 163, 164, 165]) (countLit q [166, 167, 168, 169, 170, 171, 172, 173]) (count339 q) 1 (meaning337 q) (meaning339 q) hs
  change valuationOf q 337 = false ∨ valuationOf q 339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause412 (q : Snake 81) (h : Conditions q) : valuation q 337 = false ∨ valuation q 339 = true := counterClause412 (baseVal q)

theorem counterClause413 (q : Nat → Bool) : valuationOf q 323 = false ∨ valuationOf q 339 = true := by
  have hs : count339 q = (countLit q [159, 160, 161, 162, 163, 164, 165]) + (countLit q [166, 167, 168, 169, 170, 171, 172, 173]) := List.countP_append (p := literal q) (l₁ := [159, 160, 161, 162, 163, 164, 165]) (l₂ := [166, 167, 168, 169, 170, 171, 172, 173])
  have hm := merge_left (literal (valuationOf q) (323)) (literal (valuationOf q) (339)) (countLit q [159, 160, 161, 162, 163, 164, 165]) (countLit q [166, 167, 168, 169, 170, 171, 172, 173]) (count339 q) 1 (meaning323 q) (meaning339 q) hs
  change valuationOf q 323 = false ∨ valuationOf q 339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause413 (q : Snake 81) (h : Conditions q) : valuation q 323 = false ∨ valuation q 339 = true := counterClause413 (baseVal q)

theorem counterClause414 (q : Nat → Bool) : valuationOf q 323 = false ∨ valuationOf q 337 = false ∨ valuationOf q 340 = true := by
  have hs : count339 q = (countLit q [159, 160, 161, 162, 163, 164, 165]) + (countLit q [166, 167, 168, 169, 170, 171, 172, 173]) := List.countP_append (p := literal q) (l₁ := [159, 160, 161, 162, 163, 164, 165]) (l₂ := [166, 167, 168, 169, 170, 171, 172, 173])
  have hm := merge_two (literal (valuationOf q) (323)) (literal (valuationOf q) (337)) (literal (valuationOf q) (340)) (countLit q [159, 160, 161, 162, 163, 164, 165]) (countLit q [166, 167, 168, 169, 170, 171, 172, 173]) (count339 q) 1 1 (meaning323 q) (meaning337 q) (meaning340 q) hs
  change valuationOf q 323 = false ∨ valuationOf q 337 = false ∨ valuationOf q 340 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause414 (q : Snake 81) (h : Conditions q) : valuation q 323 = false ∨ valuation q 337 = false ∨ valuation q 340 = true := counterClause414 (baseVal q)

theorem counterClause415 (q : Nat → Bool) : valuationOf q 339 = false ∨ valuationOf q 341 = true := by
  have hs : count341 q = (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) + (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173]) := List.countP_append (p := literal q) (l₁ := [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (l₂ := [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173])
  have hm := merge_right (literal (valuationOf q) (339)) (literal (valuationOf q) (341)) (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173]) (count341 q) 1 (meaning339 q) (meaning341 q) hs
  change valuationOf q 339 = false ∨ valuationOf q 341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause415 (q : Snake 81) (h : Conditions q) : valuation q 339 = false ∨ valuation q 341 = true := counterClause415 (baseVal q)

theorem counterClause416 (q : Nat → Bool) : valuationOf q 340 = false ∨ valuationOf q 342 = true := by
  have hs : count341 q = (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) + (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173]) := List.countP_append (p := literal q) (l₁ := [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (l₂ := [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173])
  have hm := merge_right (literal (valuationOf q) (340)) (literal (valuationOf q) (342)) (countLit q [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173]) (count341 q) 2 (meaning340 q) (meaning342 q) hs
  change valuationOf q 340 = false ∨ valuationOf q 342 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause416 (q : Snake 81) (h : Conditions q) : valuation q 340 = false ∨ valuation q 342 = true := counterClause416 (baseVal q)

theorem block12 (q : Snake 81) (h : Conditions q) : B112E051.Block12 (valuation q) :=
  ⟨clause385 q h, clause386 q h, clause387 q h, clause388 q h, clause389 q h, clause390 q h, clause391 q h, clause392 q h, clause393 q h, clause394 q h, clause395 q h, clause396 q h, clause397 q h, clause398 q h, clause399 q h, clause400 q h, clause401 q h, clause402 q h, clause403 q h, clause404 q h, clause405 q h, clause406 q h, clause407 q h, clause408 q h, clause409 q h, clause410 q h, clause411 q h, clause412 q h, clause413 q h, clause414 q h, clause415 q h, clause416 q h⟩

end
end Snake9.Regrowth.E112051
