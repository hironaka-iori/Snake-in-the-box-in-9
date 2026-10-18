import E112256Semantics
import B112E256Inputs
namespace Snake9.Regrowth.E112256
noncomputable section
local instance blockDec30 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause961 (q : Nat → Bool) : valuationOf q 371 = false ∨ valuationOf q 373 = true := by
  have hs : count373 q = (countLit q [175, 176, 177, 178, 179, 180, 181, 182]) + (countLit q [183, 184, 185, 186, 187, 188, 189, 190]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177, 178, 179, 180, 181, 182]) (l₂ := [183, 184, 185, 186, 187, 188, 189, 190])
  have hm := merge_right (literal (valuationOf q) (371)) (literal (valuationOf q) (373)) (countLit q [175, 176, 177, 178, 179, 180, 181, 182]) (countLit q [183, 184, 185, 186, 187, 188, 189, 190]) (count373 q) 1 (meaning371 q) (meaning373 q) hs
  change valuationOf q 371 = false ∨ valuationOf q 373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause961 (q : Snake 81) (h : Conditions q) : valuation q 371 = false ∨ valuation q 373 = true := counterClause961 (baseVal q)

theorem counterClause962 (q : Nat → Bool) : valuationOf q 372 = false ∨ valuationOf q 374 = true := by
  have hs : count373 q = (countLit q [175, 176, 177, 178, 179, 180, 181, 182]) + (countLit q [183, 184, 185, 186, 187, 188, 189, 190]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177, 178, 179, 180, 181, 182]) (l₂ := [183, 184, 185, 186, 187, 188, 189, 190])
  have hm := merge_right (literal (valuationOf q) (372)) (literal (valuationOf q) (374)) (countLit q [175, 176, 177, 178, 179, 180, 181, 182]) (countLit q [183, 184, 185, 186, 187, 188, 189, 190]) (count373 q) 2 (meaning372 q) (meaning374 q) hs
  change valuationOf q 372 = false ∨ valuationOf q 374 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause962 (q : Snake 81) (h : Conditions q) : valuation q 372 = false ∨ valuation q 374 = true := counterClause962 (baseVal q)

theorem counterClause963 (q : Nat → Bool) : valuationOf q 357 = false ∨ valuationOf q 373 = true := by
  have hs : count373 q = (countLit q [175, 176, 177, 178, 179, 180, 181, 182]) + (countLit q [183, 184, 185, 186, 187, 188, 189, 190]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177, 178, 179, 180, 181, 182]) (l₂ := [183, 184, 185, 186, 187, 188, 189, 190])
  have hm := merge_left (literal (valuationOf q) (357)) (literal (valuationOf q) (373)) (countLit q [175, 176, 177, 178, 179, 180, 181, 182]) (countLit q [183, 184, 185, 186, 187, 188, 189, 190]) (count373 q) 1 (meaning357 q) (meaning373 q) hs
  change valuationOf q 357 = false ∨ valuationOf q 373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause963 (q : Snake 81) (h : Conditions q) : valuation q 357 = false ∨ valuation q 373 = true := counterClause963 (baseVal q)

theorem counterClause964 (q : Nat → Bool) : valuationOf q 357 = false ∨ valuationOf q 371 = false ∨ valuationOf q 374 = true := by
  have hs : count373 q = (countLit q [175, 176, 177, 178, 179, 180, 181, 182]) + (countLit q [183, 184, 185, 186, 187, 188, 189, 190]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177, 178, 179, 180, 181, 182]) (l₂ := [183, 184, 185, 186, 187, 188, 189, 190])
  have hm := merge_two (literal (valuationOf q) (357)) (literal (valuationOf q) (371)) (literal (valuationOf q) (374)) (countLit q [175, 176, 177, 178, 179, 180, 181, 182]) (countLit q [183, 184, 185, 186, 187, 188, 189, 190]) (count373 q) 1 1 (meaning357 q) (meaning371 q) (meaning374 q) hs
  change valuationOf q 357 = false ∨ valuationOf q 371 = false ∨ valuationOf q 374 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause964 (q : Snake 81) (h : Conditions q) : valuation q 357 = false ∨ valuation q 371 = false ∨ valuation q 374 = true := counterClause964 (baseVal q)

theorem counterClause965 (q : Nat → Bool) : valuationOf q 373 = false ∨ valuationOf q 375 = true := by
  have hs : count375 q = (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) + (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) := List.countP_append (p := literal q) (l₁ := [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (l₂ := [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190])
  have hm := merge_right (literal (valuationOf q) (373)) (literal (valuationOf q) (375)) (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) (count375 q) 1 (meaning373 q) (meaning375 q) hs
  change valuationOf q 373 = false ∨ valuationOf q 375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause965 (q : Snake 81) (h : Conditions q) : valuation q 373 = false ∨ valuation q 375 = true := counterClause965 (baseVal q)

theorem counterClause966 (q : Nat → Bool) : valuationOf q 374 = false ∨ valuationOf q 376 = true := by
  have hs : count375 q = (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) + (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) := List.countP_append (p := literal q) (l₁ := [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (l₂ := [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190])
  have hm := merge_right (literal (valuationOf q) (374)) (literal (valuationOf q) (376)) (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) (count375 q) 2 (meaning374 q) (meaning376 q) hs
  change valuationOf q 374 = false ∨ valuationOf q 376 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause966 (q : Snake 81) (h : Conditions q) : valuation q 374 = false ∨ valuation q 376 = true := counterClause966 (baseVal q)

theorem counterClause967 (q : Nat → Bool) : valuationOf q 343 = false ∨ valuationOf q 375 = true := by
  have hs : count375 q = (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) + (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) := List.countP_append (p := literal q) (l₁ := [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (l₂ := [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190])
  have hm := merge_left (literal (valuationOf q) (343)) (literal (valuationOf q) (375)) (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) (count375 q) 1 (meaning343 q) (meaning375 q) hs
  change valuationOf q 343 = false ∨ valuationOf q 375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause967 (q : Snake 81) (h : Conditions q) : valuation q 343 = false ∨ valuation q 375 = true := counterClause967 (baseVal q)

theorem counterClause968 (q : Nat → Bool) : valuationOf q 343 = false ∨ valuationOf q 373 = false ∨ valuationOf q 376 = true := by
  have hs : count375 q = (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) + (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) := List.countP_append (p := literal q) (l₁ := [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (l₂ := [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190])
  have hm := merge_two (literal (valuationOf q) (343)) (literal (valuationOf q) (373)) (literal (valuationOf q) (376)) (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) (count375 q) 1 1 (meaning343 q) (meaning373 q) (meaning376 q) hs
  change valuationOf q 343 = false ∨ valuationOf q 373 = false ∨ valuationOf q 376 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause968 (q : Snake 81) (h : Conditions q) : valuation q 343 = false ∨ valuation q 373 = false ∨ valuation q 376 = true := counterClause968 (baseVal q)

theorem counterClause969 (q : Nat → Bool) : valuationOf q 344 = false ∨ valuationOf q 376 = true := by
  have hs : count375 q = (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) + (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) := List.countP_append (p := literal q) (l₁ := [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (l₂ := [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190])
  have hm := merge_left (literal (valuationOf q) (344)) (literal (valuationOf q) (376)) (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (countLit q [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) (count375 q) 2 (meaning344 q) (meaning376 q) hs
  change valuationOf q 344 = false ∨ valuationOf q 376 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause969 (q : Snake 81) (h : Conditions q) : valuation q 344 = false ∨ valuation q 376 = true := counterClause969 (baseVal q)

theorem counterClause970 (q : Nat → Bool) : valuationOf q 375 = false ∨ valuationOf q 377 = true := by
  have hs : count377 q = (countLit q [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) + (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) := List.countP_append (p := literal q) (l₁ := [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (l₂ := [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190])
  have hm := merge_right (literal (valuationOf q) (375)) (literal (valuationOf q) (377)) (countLit q [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) (count377 q) 1 (meaning375 q) (meaning377 q) hs
  change valuationOf q 375 = false ∨ valuationOf q 377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause970 (q : Snake 81) (h : Conditions q) : valuation q 375 = false ∨ valuation q 377 = true := counterClause970 (baseVal q)

theorem counterClause971 (q : Nat → Bool) : valuationOf q 376 = false ∨ valuationOf q 378 = true := by
  have hs : count377 q = (countLit q [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) + (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) := List.countP_append (p := literal q) (l₁ := [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (l₂ := [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190])
  have hm := merge_right (literal (valuationOf q) (376)) (literal (valuationOf q) (378)) (countLit q [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) (count377 q) 2 (meaning376 q) (meaning378 q) hs
  change valuationOf q 376 = false ∨ valuationOf q 378 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause971 (q : Snake 81) (h : Conditions q) : valuation q 376 = false ∨ valuation q 378 = true := counterClause971 (baseVal q)

theorem counterClause972 (q : Nat → Bool) : valuationOf q 313 = false ∨ valuationOf q 377 = true := by
  have hs : count377 q = (countLit q [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) + (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) := List.countP_append (p := literal q) (l₁ := [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (l₂ := [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190])
  have hm := merge_left (literal (valuationOf q) (313)) (literal (valuationOf q) (377)) (countLit q [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) (count377 q) 1 (meaning313 q) (meaning377 q) hs
  change valuationOf q 313 = false ∨ valuationOf q 377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause972 (q : Snake 81) (h : Conditions q) : valuation q 313 = false ∨ valuation q 377 = true := counterClause972 (baseVal q)

theorem counterClause973 (q : Nat → Bool) : valuationOf q 313 = false ∨ valuationOf q 375 = false ∨ valuationOf q 378 = true := by
  have hs : count377 q = (countLit q [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) + (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) := List.countP_append (p := literal q) (l₁ := [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (l₂ := [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190])
  have hm := merge_two (literal (valuationOf q) (313)) (literal (valuationOf q) (375)) (literal (valuationOf q) (378)) (countLit q [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) (count377 q) 1 1 (meaning313 q) (meaning375 q) (meaning378 q) hs
  change valuationOf q 313 = false ∨ valuationOf q 375 = false ∨ valuationOf q 378 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause973 (q : Snake 81) (h : Conditions q) : valuation q 313 = false ∨ valuation q 375 = false ∨ valuation q 378 = true := counterClause973 (baseVal q)

theorem counterClause974 (q : Nat → Bool) : valuationOf q 314 = false ∨ valuationOf q 378 = true := by
  have hs : count377 q = (countLit q [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) + (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) := List.countP_append (p := literal q) (l₁ := [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (l₂ := [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190])
  have hm := merge_left (literal (valuationOf q) (314)) (literal (valuationOf q) (378)) (countLit q [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]) (countLit q [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) (count377 q) 2 (meaning314 q) (meaning378 q) hs
  change valuationOf q 314 = false ∨ valuationOf q 378 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause974 (q : Snake 81) (h : Conditions q) : valuation q 314 = false ∨ valuation q 378 = true := counterClause974 (baseVal q)

theorem counterClause975 (q : Nat → Bool) : valuationOf q 192 = false ∨ valuationOf q 379 = true := by
  have hs : count379 q = (countLit q [192]) + (countLit q [193]) := List.countP_append (p := literal q) (l₁ := [192]) (l₂ := [193])
  have hm := merge_left (literal (valuationOf q) (192)) (literal (valuationOf q) (379)) (countLit q [192]) (countLit q [193]) (count379 q) 1 (meaning192 q) (meaning379 q) hs
  change valuationOf q 192 = false ∨ valuationOf q 379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause975 (q : Snake 81) (h : Conditions q) : valuation q 192 = false ∨ valuation q 379 = true := counterClause975 (baseVal q)

theorem counterClause976 (q : Nat → Bool) : valuationOf q 379 = false ∨ valuationOf q 381 = true := by
  have hs : count381 q = (countLit q [191]) + (countLit q [192, 193]) := List.countP_append (p := literal q) (l₁ := [191]) (l₂ := [192, 193])
  have hm := merge_right (literal (valuationOf q) (379)) (literal (valuationOf q) (381)) (countLit q [191]) (countLit q [192, 193]) (count381 q) 1 (meaning379 q) (meaning381 q) hs
  change valuationOf q 379 = false ∨ valuationOf q 381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause976 (q : Snake 81) (h : Conditions q) : valuation q 379 = false ∨ valuation q 381 = true := counterClause976 (baseVal q)

theorem counterClause977 (q : Nat → Bool) : valuationOf q 195 = false ∨ valuationOf q 383 = true := by
  have hs : count383 q = (countLit q [194]) + (countLit q [195]) := List.countP_append (p := literal q) (l₁ := [194]) (l₂ := [195])
  have hm := merge_right (literal (valuationOf q) (195)) (literal (valuationOf q) (383)) (countLit q [194]) (countLit q [195]) (count383 q) 1 (meaning195 q) (meaning383 q) hs
  change valuationOf q 195 = false ∨ valuationOf q 383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause977 (q : Snake 81) (h : Conditions q) : valuation q 195 = false ∨ valuation q 383 = true := counterClause977 (baseVal q)

theorem counterClause978 (q : Nat → Bool) : valuationOf q 194 = false ∨ valuationOf q 383 = true := by
  have hs : count383 q = (countLit q [194]) + (countLit q [195]) := List.countP_append (p := literal q) (l₁ := [194]) (l₂ := [195])
  have hm := merge_left (literal (valuationOf q) (194)) (literal (valuationOf q) (383)) (countLit q [194]) (countLit q [195]) (count383 q) 1 (meaning194 q) (meaning383 q) hs
  change valuationOf q 194 = false ∨ valuationOf q 383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause978 (q : Snake 81) (h : Conditions q) : valuation q 194 = false ∨ valuation q 383 = true := counterClause978 (baseVal q)

theorem counterClause979 (q : Nat → Bool) : valuationOf q 194 = false ∨ valuationOf q 195 = false ∨ valuationOf q 384 = true := by
  have hs : count383 q = (countLit q [194]) + (countLit q [195]) := List.countP_append (p := literal q) (l₁ := [194]) (l₂ := [195])
  have hm := merge_two (literal (valuationOf q) (194)) (literal (valuationOf q) (195)) (literal (valuationOf q) (384)) (countLit q [194]) (countLit q [195]) (count383 q) 1 1 (meaning194 q) (meaning195 q) (meaning384 q) hs
  change valuationOf q 194 = false ∨ valuationOf q 195 = false ∨ valuationOf q 384 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause979 (q : Snake 81) (h : Conditions q) : valuation q 194 = false ∨ valuation q 195 = false ∨ valuation q 384 = true := counterClause979 (baseVal q)

theorem counterClause980 (q : Nat → Bool) : valuationOf q 197 = false ∨ valuationOf q 385 = true := by
  have hs : count385 q = (countLit q [196]) + (countLit q [197]) := List.countP_append (p := literal q) (l₁ := [196]) (l₂ := [197])
  have hm := merge_right (literal (valuationOf q) (197)) (literal (valuationOf q) (385)) (countLit q [196]) (countLit q [197]) (count385 q) 1 (meaning197 q) (meaning385 q) hs
  change valuationOf q 197 = false ∨ valuationOf q 385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause980 (q : Snake 81) (h : Conditions q) : valuation q 197 = false ∨ valuation q 385 = true := counterClause980 (baseVal q)

theorem counterClause981 (q : Nat → Bool) : valuationOf q 385 = false ∨ valuationOf q 387 = true := by
  have hs : count387 q = (countLit q [194, 195]) + (countLit q [196, 197]) := List.countP_append (p := literal q) (l₁ := [194, 195]) (l₂ := [196, 197])
  have hm := merge_right (literal (valuationOf q) (385)) (literal (valuationOf q) (387)) (countLit q [194, 195]) (countLit q [196, 197]) (count387 q) 1 (meaning385 q) (meaning387 q) hs
  change valuationOf q 385 = false ∨ valuationOf q 387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause981 (q : Snake 81) (h : Conditions q) : valuation q 385 = false ∨ valuation q 387 = true := counterClause981 (baseVal q)

theorem counterClause982 (q : Nat → Bool) : valuationOf q 383 = false ∨ valuationOf q 387 = true := by
  have hs : count387 q = (countLit q [194, 195]) + (countLit q [196, 197]) := List.countP_append (p := literal q) (l₁ := [194, 195]) (l₂ := [196, 197])
  have hm := merge_left (literal (valuationOf q) (383)) (literal (valuationOf q) (387)) (countLit q [194, 195]) (countLit q [196, 197]) (count387 q) 1 (meaning383 q) (meaning387 q) hs
  change valuationOf q 383 = false ∨ valuationOf q 387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause982 (q : Snake 81) (h : Conditions q) : valuation q 383 = false ∨ valuation q 387 = true := counterClause982 (baseVal q)

theorem counterClause983 (q : Nat → Bool) : valuationOf q 383 = false ∨ valuationOf q 385 = false ∨ valuationOf q 388 = true := by
  have hs : count387 q = (countLit q [194, 195]) + (countLit q [196, 197]) := List.countP_append (p := literal q) (l₁ := [194, 195]) (l₂ := [196, 197])
  have hm := merge_two (literal (valuationOf q) (383)) (literal (valuationOf q) (385)) (literal (valuationOf q) (388)) (countLit q [194, 195]) (countLit q [196, 197]) (count387 q) 1 1 (meaning383 q) (meaning385 q) (meaning388 q) hs
  change valuationOf q 383 = false ∨ valuationOf q 385 = false ∨ valuationOf q 388 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause983 (q : Snake 81) (h : Conditions q) : valuation q 383 = false ∨ valuation q 385 = false ∨ valuation q 388 = true := counterClause983 (baseVal q)

theorem counterClause984 (q : Nat → Bool) : valuationOf q 384 = false ∨ valuationOf q 388 = true := by
  have hs : count387 q = (countLit q [194, 195]) + (countLit q [196, 197]) := List.countP_append (p := literal q) (l₁ := [194, 195]) (l₂ := [196, 197])
  have hm := merge_left (literal (valuationOf q) (384)) (literal (valuationOf q) (388)) (countLit q [194, 195]) (countLit q [196, 197]) (count387 q) 2 (meaning384 q) (meaning388 q) hs
  change valuationOf q 384 = false ∨ valuationOf q 388 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause984 (q : Snake 81) (h : Conditions q) : valuation q 384 = false ∨ valuation q 388 = true := counterClause984 (baseVal q)

theorem counterClause985 (q : Nat → Bool) : valuationOf q 387 = false ∨ valuationOf q 389 = true := by
  have hs : count389 q = (countLit q [191, 192, 193]) + (countLit q [194, 195, 196, 197]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193]) (l₂ := [194, 195, 196, 197])
  have hm := merge_right (literal (valuationOf q) (387)) (literal (valuationOf q) (389)) (countLit q [191, 192, 193]) (countLit q [194, 195, 196, 197]) (count389 q) 1 (meaning387 q) (meaning389 q) hs
  change valuationOf q 387 = false ∨ valuationOf q 389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause985 (q : Snake 81) (h : Conditions q) : valuation q 387 = false ∨ valuation q 389 = true := counterClause985 (baseVal q)

theorem counterClause986 (q : Nat → Bool) : valuationOf q 388 = false ∨ valuationOf q 390 = true := by
  have hs : count389 q = (countLit q [191, 192, 193]) + (countLit q [194, 195, 196, 197]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193]) (l₂ := [194, 195, 196, 197])
  have hm := merge_right (literal (valuationOf q) (388)) (literal (valuationOf q) (390)) (countLit q [191, 192, 193]) (countLit q [194, 195, 196, 197]) (count389 q) 2 (meaning388 q) (meaning390 q) hs
  change valuationOf q 388 = false ∨ valuationOf q 390 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause986 (q : Snake 81) (h : Conditions q) : valuation q 388 = false ∨ valuation q 390 = true := counterClause986 (baseVal q)

theorem counterClause987 (q : Nat → Bool) : valuationOf q 381 = false ∨ valuationOf q 389 = true := by
  have hs : count389 q = (countLit q [191, 192, 193]) + (countLit q [194, 195, 196, 197]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193]) (l₂ := [194, 195, 196, 197])
  have hm := merge_left (literal (valuationOf q) (381)) (literal (valuationOf q) (389)) (countLit q [191, 192, 193]) (countLit q [194, 195, 196, 197]) (count389 q) 1 (meaning381 q) (meaning389 q) hs
  change valuationOf q 381 = false ∨ valuationOf q 389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause987 (q : Snake 81) (h : Conditions q) : valuation q 381 = false ∨ valuation q 389 = true := counterClause987 (baseVal q)

theorem counterClause988 (q : Nat → Bool) : valuationOf q 201 = false ∨ valuationOf q 393 = true := by
  have hs : count393 q = (countLit q [200]) + (countLit q [201]) := List.countP_append (p := literal q) (l₁ := [200]) (l₂ := [201])
  have hm := merge_right (literal (valuationOf q) (201)) (literal (valuationOf q) (393)) (countLit q [200]) (countLit q [201]) (count393 q) 1 (meaning201 q) (meaning393 q) hs
  change valuationOf q 201 = false ∨ valuationOf q 393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause988 (q : Snake 81) (h : Conditions q) : valuation q 201 = false ∨ valuation q 393 = true := counterClause988 (baseVal q)

theorem counterClause989 (q : Nat → Bool) : valuationOf q 393 = false ∨ valuationOf q 395 = true := by
  have hs : count395 q = (countLit q [198, 199]) + (countLit q [200, 201]) := List.countP_append (p := literal q) (l₁ := [198, 199]) (l₂ := [200, 201])
  have hm := merge_right (literal (valuationOf q) (393)) (literal (valuationOf q) (395)) (countLit q [198, 199]) (countLit q [200, 201]) (count395 q) 1 (meaning393 q) (meaning395 q) hs
  change valuationOf q 393 = false ∨ valuationOf q 395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause989 (q : Snake 81) (h : Conditions q) : valuation q 393 = false ∨ valuation q 395 = true := counterClause989 (baseVal q)

theorem counterClause990 (q : Nat → Bool) : valuationOf q 203 = false ∨ valuationOf q 397 = true := by
  have hs : count397 q = (countLit q [202]) + (countLit q [203]) := List.countP_append (p := literal q) (l₁ := [202]) (l₂ := [203])
  have hm := merge_right (literal (valuationOf q) (203)) (literal (valuationOf q) (397)) (countLit q [202]) (countLit q [203]) (count397 q) 1 (meaning203 q) (meaning397 q) hs
  change valuationOf q 203 = false ∨ valuationOf q 397 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause990 (q : Snake 81) (h : Conditions q) : valuation q 203 = false ∨ valuation q 397 = true := counterClause990 (baseVal q)

theorem counterClause991 (q : Nat → Bool) : valuationOf q 205 = false ∨ valuationOf q 399 = true := by
  have hs : count399 q = (countLit q [204]) + (countLit q [205]) := List.countP_append (p := literal q) (l₁ := [204]) (l₂ := [205])
  have hm := merge_right (literal (valuationOf q) (205)) (literal (valuationOf q) (399)) (countLit q [204]) (countLit q [205]) (count399 q) 1 (meaning205 q) (meaning399 q) hs
  change valuationOf q 205 = false ∨ valuationOf q 399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause991 (q : Snake 81) (h : Conditions q) : valuation q 205 = false ∨ valuation q 399 = true := counterClause991 (baseVal q)

theorem counterClause992 (q : Nat → Bool) : valuationOf q 399 = false ∨ valuationOf q 401 = true := by
  have hs : count401 q = (countLit q [202, 203]) + (countLit q [204, 205]) := List.countP_append (p := literal q) (l₁ := [202, 203]) (l₂ := [204, 205])
  have hm := merge_right (literal (valuationOf q) (399)) (literal (valuationOf q) (401)) (countLit q [202, 203]) (countLit q [204, 205]) (count401 q) 1 (meaning399 q) (meaning401 q) hs
  change valuationOf q 399 = false ∨ valuationOf q 401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause992 (q : Snake 81) (h : Conditions q) : valuation q 399 = false ∨ valuation q 401 = true := counterClause992 (baseVal q)

theorem block30 (q : Snake 81) (h : Conditions q) : B112E256.Block30 (valuation q) :=
  ⟨clause961 q h, clause962 q h, clause963 q h, clause964 q h, clause965 q h, clause966 q h, clause967 q h, clause968 q h, clause969 q h, clause970 q h, clause971 q h, clause972 q h, clause973 q h, clause974 q h, clause975 q h, clause976 q h, clause977 q h, clause978 q h, clause979 q h, clause980 q h, clause981 q h, clause982 q h, clause983 q h, clause984 q h, clause985 q h, clause986 q h, clause987 q h, clause988 q h, clause989 q h, clause990 q h, clause991 q h, clause992 q h⟩

end
end Snake9.Regrowth.E112256
