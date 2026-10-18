import E112254Semantics
import B112E254Inputs
namespace Snake9.Regrowth.E112254
noncomputable section
local instance blockDec24 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause769 (q : Nat → Bool) : valuationOf q 341 = false ∨ valuationOf q 357 = true := by
  have hs : count357 q = (countLit q [168, 170, 171, 172, 173, 174, 175]) + (countLit q [176, 177, 178, 179, 180, 181, 182, 183]) := List.countP_append (p := literal q) (l₁ := [168, 170, 171, 172, 173, 174, 175]) (l₂ := [176, 177, 178, 179, 180, 181, 182, 183])
  have hm := merge_left (literal (valuationOf q) (341)) (literal (valuationOf q) (357)) (countLit q [168, 170, 171, 172, 173, 174, 175]) (countLit q [176, 177, 178, 179, 180, 181, 182, 183]) (count357 q) 1 (meaning341 q) (meaning357 q) hs
  change valuationOf q 341 = false ∨ valuationOf q 357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause769 (q : Snake 81) (h : Conditions q) : valuation q 341 = false ∨ valuation q 357 = true := counterClause769 (baseVal q)

theorem counterClause770 (q : Nat → Bool) : valuationOf q 357 = false ∨ valuationOf q 359 = true := by
  have hs : count359 q = (countLit q [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167]) + (countLit q [168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183]) := List.countP_append (p := literal q) (l₁ := [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167]) (l₂ := [168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183])
  have hm := merge_right (literal (valuationOf q) (357)) (literal (valuationOf q) (359)) (countLit q [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167]) (countLit q [168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183]) (count359 q) 1 (meaning357 q) (meaning359 q) hs
  change valuationOf q 357 = false ∨ valuationOf q 359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause770 (q : Snake 81) (h : Conditions q) : valuation q 357 = false ∨ valuation q 359 = true := counterClause770 (baseVal q)

theorem counterClause771 (q : Nat → Bool) : valuationOf q 329 = false ∨ valuationOf q 359 = true := by
  have hs : count359 q = (countLit q [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167]) + (countLit q [168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183]) := List.countP_append (p := literal q) (l₁ := [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167]) (l₂ := [168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183])
  have hm := merge_left (literal (valuationOf q) (329)) (literal (valuationOf q) (359)) (countLit q [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167]) (countLit q [168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183]) (count359 q) 1 (meaning329 q) (meaning359 q) hs
  change valuationOf q 329 = false ∨ valuationOf q 359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause771 (q : Snake 81) (h : Conditions q) : valuation q 329 = false ∨ valuation q 359 = true := counterClause771 (baseVal q)

theorem counterClause772 (q : Nat → Bool) : valuationOf q 329 = false ∨ valuationOf q 357 = false ∨ valuationOf q 360 = true := by
  have hs : count359 q = (countLit q [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167]) + (countLit q [168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183]) := List.countP_append (p := literal q) (l₁ := [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167]) (l₂ := [168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183])
  have hm := merge_two (literal (valuationOf q) (329)) (literal (valuationOf q) (357)) (literal (valuationOf q) (360)) (countLit q [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167]) (countLit q [168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183]) (count359 q) 1 1 (meaning329 q) (meaning357 q) (meaning360 q) hs
  change valuationOf q 329 = false ∨ valuationOf q 357 = false ∨ valuationOf q 360 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause772 (q : Snake 81) (h : Conditions q) : valuation q 329 = false ∨ valuation q 357 = false ∨ valuation q 360 = true := counterClause772 (baseVal q)

theorem counterClause773 (q : Nat → Bool) : valuationOf q 330 = false ∨ valuationOf q 360 = true := by
  have hs : count359 q = (countLit q [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167]) + (countLit q [168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183]) := List.countP_append (p := literal q) (l₁ := [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167]) (l₂ := [168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183])
  have hm := merge_left (literal (valuationOf q) (330)) (literal (valuationOf q) (360)) (countLit q [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167]) (countLit q [168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183]) (count359 q) 2 (meaning330 q) (meaning360 q) hs
  change valuationOf q 330 = false ∨ valuationOf q 360 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause773 (q : Snake 81) (h : Conditions q) : valuation q 330 = false ∨ valuation q 360 = true := counterClause773 (baseVal q)

theorem counterClause774 (q : Nat → Bool) : valuationOf q 359 = false ∨ valuationOf q 361 = true := by
  have hs : count361 q = (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) + (countLit q [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183]) := List.countP_append (p := literal q) (l₁ := [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) (l₂ := [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183])
  have hm := merge_right (literal (valuationOf q) (359)) (literal (valuationOf q) (361)) (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) (countLit q [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183]) (count361 q) 1 (meaning359 q) (meaning361 q) hs
  change valuationOf q 359 = false ∨ valuationOf q 361 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause774 (q : Snake 81) (h : Conditions q) : valuation q 359 = false ∨ valuation q 361 = true := counterClause774 (baseVal q)

theorem counterClause775 (q : Nat → Bool) : valuationOf q 360 = false ∨ valuationOf q 362 = true := by
  have hs : count361 q = (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) + (countLit q [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183]) := List.countP_append (p := literal q) (l₁ := [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) (l₂ := [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183])
  have hm := merge_right (literal (valuationOf q) (360)) (literal (valuationOf q) (362)) (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) (countLit q [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183]) (count361 q) 2 (meaning360 q) (meaning362 q) hs
  change valuationOf q 360 = false ∨ valuationOf q 362 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause775 (q : Snake 81) (h : Conditions q) : valuation q 360 = false ∨ valuation q 362 = true := counterClause775 (baseVal q)

theorem counterClause776 (q : Nat → Bool) : valuationOf q 301 = false ∨ valuationOf q 361 = true := by
  have hs : count361 q = (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) + (countLit q [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183]) := List.countP_append (p := literal q) (l₁ := [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) (l₂ := [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183])
  have hm := merge_left (literal (valuationOf q) (301)) (literal (valuationOf q) (361)) (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) (countLit q [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183]) (count361 q) 1 (meaning301 q) (meaning361 q) hs
  change valuationOf q 301 = false ∨ valuationOf q 361 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause776 (q : Snake 81) (h : Conditions q) : valuation q 301 = false ∨ valuation q 361 = true := counterClause776 (baseVal q)

theorem counterClause777 (q : Nat → Bool) : valuationOf q 301 = false ∨ valuationOf q 359 = false ∨ valuationOf q 362 = true := by
  have hs : count361 q = (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) + (countLit q [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183]) := List.countP_append (p := literal q) (l₁ := [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) (l₂ := [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183])
  have hm := merge_two (literal (valuationOf q) (301)) (literal (valuationOf q) (359)) (literal (valuationOf q) (362)) (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) (countLit q [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183]) (count361 q) 1 1 (meaning301 q) (meaning359 q) (meaning362 q) hs
  change valuationOf q 301 = false ∨ valuationOf q 359 = false ∨ valuationOf q 362 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause777 (q : Snake 81) (h : Conditions q) : valuation q 301 = false ∨ valuation q 359 = false ∨ valuation q 362 = true := counterClause777 (baseVal q)

theorem counterClause778 (q : Nat → Bool) : valuationOf q 302 = false ∨ valuationOf q 362 = true := by
  have hs : count361 q = (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) + (countLit q [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183]) := List.countP_append (p := literal q) (l₁ := [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) (l₂ := [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183])
  have hm := merge_left (literal (valuationOf q) (302)) (literal (valuationOf q) (362)) (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) (countLit q [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183]) (count361 q) 2 (meaning302 q) (meaning362 q) hs
  change valuationOf q 302 = false ∨ valuationOf q 362 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause778 (q : Snake 81) (h : Conditions q) : valuation q 302 = false ∨ valuation q 362 = true := counterClause778 (baseVal q)

theorem counterClause779 (q : Nat → Bool) : valuationOf q 186 = false ∨ valuationOf q 363 = true := by
  have hs : count363 q = (countLit q [185]) + (countLit q [186]) := List.countP_append (p := literal q) (l₁ := [185]) (l₂ := [186])
  have hm := merge_right (literal (valuationOf q) (186)) (literal (valuationOf q) (363)) (countLit q [185]) (countLit q [186]) (count363 q) 1 (meaning186 q) (meaning363 q) hs
  change valuationOf q 186 = false ∨ valuationOf q 363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause779 (q : Snake 81) (h : Conditions q) : valuation q 186 = false ∨ valuation q 363 = true := counterClause779 (baseVal q)

theorem counterClause780 (q : Nat → Bool) : valuationOf q 185 = false ∨ valuationOf q 363 = true := by
  have hs : count363 q = (countLit q [185]) + (countLit q [186]) := List.countP_append (p := literal q) (l₁ := [185]) (l₂ := [186])
  have hm := merge_left (literal (valuationOf q) (185)) (literal (valuationOf q) (363)) (countLit q [185]) (countLit q [186]) (count363 q) 1 (meaning185 q) (meaning363 q) hs
  change valuationOf q 185 = false ∨ valuationOf q 363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause780 (q : Snake 81) (h : Conditions q) : valuation q 185 = false ∨ valuation q 363 = true := counterClause780 (baseVal q)

theorem counterClause781 (q : Nat → Bool) : valuationOf q 363 = false ∨ valuationOf q 365 = true := by
  have hs : count365 q = (countLit q [184]) + (countLit q [185, 186]) := List.countP_append (p := literal q) (l₁ := [184]) (l₂ := [185, 186])
  have hm := merge_right (literal (valuationOf q) (363)) (literal (valuationOf q) (365)) (countLit q [184]) (countLit q [185, 186]) (count365 q) 1 (meaning363 q) (meaning365 q) hs
  change valuationOf q 363 = false ∨ valuationOf q 365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause781 (q : Snake 81) (h : Conditions q) : valuation q 363 = false ∨ valuation q 365 = true := counterClause781 (baseVal q)

theorem counterClause782 (q : Nat → Bool) : valuationOf q 190 = false ∨ valuationOf q 369 = true := by
  have hs : count369 q = (countLit q [189]) + (countLit q [190]) := List.countP_append (p := literal q) (l₁ := [189]) (l₂ := [190])
  have hm := merge_right (literal (valuationOf q) (190)) (literal (valuationOf q) (369)) (countLit q [189]) (countLit q [190]) (count369 q) 1 (meaning190 q) (meaning369 q) hs
  change valuationOf q 190 = false ∨ valuationOf q 369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause782 (q : Snake 81) (h : Conditions q) : valuation q 190 = false ∨ valuation q 369 = true := counterClause782 (baseVal q)

theorem counterClause783 (q : Nat → Bool) : valuationOf q 369 = false ∨ valuationOf q 371 = true := by
  have hs : count371 q = (countLit q [187, 188]) + (countLit q [189, 190]) := List.countP_append (p := literal q) (l₁ := [187, 188]) (l₂ := [189, 190])
  have hm := merge_right (literal (valuationOf q) (369)) (literal (valuationOf q) (371)) (countLit q [187, 188]) (countLit q [189, 190]) (count371 q) 1 (meaning369 q) (meaning371 q) hs
  change valuationOf q 369 = false ∨ valuationOf q 371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause783 (q : Snake 81) (h : Conditions q) : valuation q 369 = false ∨ valuation q 371 = true := counterClause783 (baseVal q)

theorem counterClause784 (q : Nat → Bool) : valuationOf q 371 = false ∨ valuationOf q 373 = true := by
  have hs : count373 q = (countLit q [184, 185, 186]) + (countLit q [187, 188, 189, 190]) := List.countP_append (p := literal q) (l₁ := [184, 185, 186]) (l₂ := [187, 188, 189, 190])
  have hm := merge_right (literal (valuationOf q) (371)) (literal (valuationOf q) (373)) (countLit q [184, 185, 186]) (countLit q [187, 188, 189, 190]) (count373 q) 1 (meaning371 q) (meaning373 q) hs
  change valuationOf q 371 = false ∨ valuationOf q 373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause784 (q : Snake 81) (h : Conditions q) : valuation q 371 = false ∨ valuation q 373 = true := counterClause784 (baseVal q)

theorem counterClause785 (q : Nat → Bool) : valuationOf q 365 = false ∨ valuationOf q 373 = true := by
  have hs : count373 q = (countLit q [184, 185, 186]) + (countLit q [187, 188, 189, 190]) := List.countP_append (p := literal q) (l₁ := [184, 185, 186]) (l₂ := [187, 188, 189, 190])
  have hm := merge_left (literal (valuationOf q) (365)) (literal (valuationOf q) (373)) (countLit q [184, 185, 186]) (countLit q [187, 188, 189, 190]) (count373 q) 1 (meaning365 q) (meaning373 q) hs
  change valuationOf q 365 = false ∨ valuationOf q 373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause785 (q : Snake 81) (h : Conditions q) : valuation q 365 = false ∨ valuation q 373 = true := counterClause785 (baseVal q)

theorem counterClause786 (q : Nat → Bool) : valuationOf q 194 = false ∨ valuationOf q 377 = true := by
  have hs : count377 q = (countLit q [193]) + (countLit q [194]) := List.countP_append (p := literal q) (l₁ := [193]) (l₂ := [194])
  have hm := merge_right (literal (valuationOf q) (194)) (literal (valuationOf q) (377)) (countLit q [193]) (countLit q [194]) (count377 q) 1 (meaning194 q) (meaning377 q) hs
  change valuationOf q 194 = false ∨ valuationOf q 377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause786 (q : Snake 81) (h : Conditions q) : valuation q 194 = false ∨ valuation q 377 = true := counterClause786 (baseVal q)

theorem counterClause787 (q : Nat → Bool) : valuationOf q 193 = false ∨ valuationOf q 377 = true := by
  have hs : count377 q = (countLit q [193]) + (countLit q [194]) := List.countP_append (p := literal q) (l₁ := [193]) (l₂ := [194])
  have hm := merge_left (literal (valuationOf q) (193)) (literal (valuationOf q) (377)) (countLit q [193]) (countLit q [194]) (count377 q) 1 (meaning193 q) (meaning377 q) hs
  change valuationOf q 193 = false ∨ valuationOf q 377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause787 (q : Snake 81) (h : Conditions q) : valuation q 193 = false ∨ valuation q 377 = true := counterClause787 (baseVal q)

theorem counterClause788 (q : Nat → Bool) : valuationOf q 377 = false ∨ valuationOf q 379 = true := by
  have hs : count379 q = (countLit q [191, 192]) + (countLit q [193, 194]) := List.countP_append (p := literal q) (l₁ := [191, 192]) (l₂ := [193, 194])
  have hm := merge_right (literal (valuationOf q) (377)) (literal (valuationOf q) (379)) (countLit q [191, 192]) (countLit q [193, 194]) (count379 q) 1 (meaning377 q) (meaning379 q) hs
  change valuationOf q 377 = false ∨ valuationOf q 379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause788 (q : Snake 81) (h : Conditions q) : valuation q 377 = false ∨ valuation q 379 = true := counterClause788 (baseVal q)

theorem counterClause789 (q : Nat → Bool) : valuationOf q 196 = false ∨ valuationOf q 381 = true := by
  have hs : count381 q = (countLit q [195]) + (countLit q [196]) := List.countP_append (p := literal q) (l₁ := [195]) (l₂ := [196])
  have hm := merge_right (literal (valuationOf q) (196)) (literal (valuationOf q) (381)) (countLit q [195]) (countLit q [196]) (count381 q) 1 (meaning196 q) (meaning381 q) hs
  change valuationOf q 196 = false ∨ valuationOf q 381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause789 (q : Snake 81) (h : Conditions q) : valuation q 196 = false ∨ valuation q 381 = true := counterClause789 (baseVal q)

theorem counterClause790 (q : Nat → Bool) : valuationOf q 195 = false ∨ valuationOf q 381 = true := by
  have hs : count381 q = (countLit q [195]) + (countLit q [196]) := List.countP_append (p := literal q) (l₁ := [195]) (l₂ := [196])
  have hm := merge_left (literal (valuationOf q) (195)) (literal (valuationOf q) (381)) (countLit q [195]) (countLit q [196]) (count381 q) 1 (meaning195 q) (meaning381 q) hs
  change valuationOf q 195 = false ∨ valuationOf q 381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause790 (q : Snake 81) (h : Conditions q) : valuation q 195 = false ∨ valuation q 381 = true := counterClause790 (baseVal q)

theorem counterClause791 (q : Nat → Bool) : valuationOf q 195 = false ∨ valuationOf q 196 = false ∨ valuationOf q 382 = true := by
  have hs : count381 q = (countLit q [195]) + (countLit q [196]) := List.countP_append (p := literal q) (l₁ := [195]) (l₂ := [196])
  have hm := merge_two (literal (valuationOf q) (195)) (literal (valuationOf q) (196)) (literal (valuationOf q) (382)) (countLit q [195]) (countLit q [196]) (count381 q) 1 1 (meaning195 q) (meaning196 q) (meaning382 q) hs
  change valuationOf q 195 = false ∨ valuationOf q 196 = false ∨ valuationOf q 382 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause791 (q : Snake 81) (h : Conditions q) : valuation q 195 = false ∨ valuation q 196 = false ∨ valuation q 382 = true := counterClause791 (baseVal q)

theorem counterClause792 (q : Nat → Bool) : valuationOf q 198 = false ∨ valuationOf q 383 = true := by
  have hs : count383 q = (countLit q [197]) + (countLit q [198]) := List.countP_append (p := literal q) (l₁ := [197]) (l₂ := [198])
  have hm := merge_right (literal (valuationOf q) (198)) (literal (valuationOf q) (383)) (countLit q [197]) (countLit q [198]) (count383 q) 1 (meaning198 q) (meaning383 q) hs
  change valuationOf q 198 = false ∨ valuationOf q 383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause792 (q : Snake 81) (h : Conditions q) : valuation q 198 = false ∨ valuation q 383 = true := counterClause792 (baseVal q)

theorem counterClause793 (q : Nat → Bool) : valuationOf q 197 = false ∨ valuationOf q 383 = true := by
  have hs : count383 q = (countLit q [197]) + (countLit q [198]) := List.countP_append (p := literal q) (l₁ := [197]) (l₂ := [198])
  have hm := merge_left (literal (valuationOf q) (197)) (literal (valuationOf q) (383)) (countLit q [197]) (countLit q [198]) (count383 q) 1 (meaning197 q) (meaning383 q) hs
  change valuationOf q 197 = false ∨ valuationOf q 383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause793 (q : Snake 81) (h : Conditions q) : valuation q 197 = false ∨ valuation q 383 = true := counterClause793 (baseVal q)

theorem counterClause794 (q : Nat → Bool) : valuationOf q 383 = false ∨ valuationOf q 385 = true := by
  have hs : count385 q = (countLit q [195, 196]) + (countLit q [197, 198]) := List.countP_append (p := literal q) (l₁ := [195, 196]) (l₂ := [197, 198])
  have hm := merge_right (literal (valuationOf q) (383)) (literal (valuationOf q) (385)) (countLit q [195, 196]) (countLit q [197, 198]) (count385 q) 1 (meaning383 q) (meaning385 q) hs
  change valuationOf q 383 = false ∨ valuationOf q 385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause794 (q : Snake 81) (h : Conditions q) : valuation q 383 = false ∨ valuation q 385 = true := counterClause794 (baseVal q)

theorem counterClause795 (q : Nat → Bool) : valuationOf q 381 = false ∨ valuationOf q 385 = true := by
  have hs : count385 q = (countLit q [195, 196]) + (countLit q [197, 198]) := List.countP_append (p := literal q) (l₁ := [195, 196]) (l₂ := [197, 198])
  have hm := merge_left (literal (valuationOf q) (381)) (literal (valuationOf q) (385)) (countLit q [195, 196]) (countLit q [197, 198]) (count385 q) 1 (meaning381 q) (meaning385 q) hs
  change valuationOf q 381 = false ∨ valuationOf q 385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause795 (q : Snake 81) (h : Conditions q) : valuation q 381 = false ∨ valuation q 385 = true := counterClause795 (baseVal q)

theorem counterClause796 (q : Nat → Bool) : valuationOf q 381 = false ∨ valuationOf q 383 = false ∨ valuationOf q 386 = true := by
  have hs : count385 q = (countLit q [195, 196]) + (countLit q [197, 198]) := List.countP_append (p := literal q) (l₁ := [195, 196]) (l₂ := [197, 198])
  have hm := merge_two (literal (valuationOf q) (381)) (literal (valuationOf q) (383)) (literal (valuationOf q) (386)) (countLit q [195, 196]) (countLit q [197, 198]) (count385 q) 1 1 (meaning381 q) (meaning383 q) (meaning386 q) hs
  change valuationOf q 381 = false ∨ valuationOf q 383 = false ∨ valuationOf q 386 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause796 (q : Snake 81) (h : Conditions q) : valuation q 381 = false ∨ valuation q 383 = false ∨ valuation q 386 = true := counterClause796 (baseVal q)

theorem counterClause797 (q : Nat → Bool) : valuationOf q 382 = false ∨ valuationOf q 386 = true := by
  have hs : count385 q = (countLit q [195, 196]) + (countLit q [197, 198]) := List.countP_append (p := literal q) (l₁ := [195, 196]) (l₂ := [197, 198])
  have hm := merge_left (literal (valuationOf q) (382)) (literal (valuationOf q) (386)) (countLit q [195, 196]) (countLit q [197, 198]) (count385 q) 2 (meaning382 q) (meaning386 q) hs
  change valuationOf q 382 = false ∨ valuationOf q 386 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause797 (q : Snake 81) (h : Conditions q) : valuation q 382 = false ∨ valuation q 386 = true := counterClause797 (baseVal q)

theorem counterClause798 (q : Nat → Bool) : valuationOf q 385 = false ∨ valuationOf q 387 = true := by
  have hs : count387 q = (countLit q [191, 192, 193, 194]) + (countLit q [195, 196, 197, 198]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193, 194]) (l₂ := [195, 196, 197, 198])
  have hm := merge_right (literal (valuationOf q) (385)) (literal (valuationOf q) (387)) (countLit q [191, 192, 193, 194]) (countLit q [195, 196, 197, 198]) (count387 q) 1 (meaning385 q) (meaning387 q) hs
  change valuationOf q 385 = false ∨ valuationOf q 387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause798 (q : Snake 81) (h : Conditions q) : valuation q 385 = false ∨ valuation q 387 = true := counterClause798 (baseVal q)

theorem counterClause799 (q : Nat → Bool) : valuationOf q 386 = false ∨ valuationOf q 388 = true := by
  have hs : count387 q = (countLit q [191, 192, 193, 194]) + (countLit q [195, 196, 197, 198]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193, 194]) (l₂ := [195, 196, 197, 198])
  have hm := merge_right (literal (valuationOf q) (386)) (literal (valuationOf q) (388)) (countLit q [191, 192, 193, 194]) (countLit q [195, 196, 197, 198]) (count387 q) 2 (meaning386 q) (meaning388 q) hs
  change valuationOf q 386 = false ∨ valuationOf q 388 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause799 (q : Snake 81) (h : Conditions q) : valuation q 386 = false ∨ valuation q 388 = true := counterClause799 (baseVal q)

theorem counterClause800 (q : Nat → Bool) : valuationOf q 379 = false ∨ valuationOf q 387 = true := by
  have hs : count387 q = (countLit q [191, 192, 193, 194]) + (countLit q [195, 196, 197, 198]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193, 194]) (l₂ := [195, 196, 197, 198])
  have hm := merge_left (literal (valuationOf q) (379)) (literal (valuationOf q) (387)) (countLit q [191, 192, 193, 194]) (countLit q [195, 196, 197, 198]) (count387 q) 1 (meaning379 q) (meaning387 q) hs
  change valuationOf q 379 = false ∨ valuationOf q 387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause800 (q : Snake 81) (h : Conditions q) : valuation q 379 = false ∨ valuation q 387 = true := counterClause800 (baseVal q)

theorem block24 (q : Snake 81) (h : Conditions q) : B112E254.Block24 (valuation q) :=
  ⟨clause769 q h, clause770 q h, clause771 q h, clause772 q h, clause773 q h, clause774 q h, clause775 q h, clause776 q h, clause777 q h, clause778 q h, clause779 q h, clause780 q h, clause781 q h, clause782 q h, clause783 q h, clause784 q h, clause785 q h, clause786 q h, clause787 q h, clause788 q h, clause789 q h, clause790 q h, clause791 q h, clause792 q h, clause793 q h, clause794 q h, clause795 q h, clause796 q h, clause797 q h, clause798 q h, clause799 q h, clause800 q h⟩

end
end Snake9.Regrowth.E112254
