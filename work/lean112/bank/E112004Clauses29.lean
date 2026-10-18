import E112004Semantics
import B112E004Inputs
namespace Snake9.Regrowth.E112004
noncomputable section
local instance blockDec29 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause929 (q : Nat → Bool) : valuationOf q 349 = false ∨ valuationOf q 351 = true := by
  have hs : count351 q = (countLit q [165, 166, 167, 168, 169, 170, 171]) + (countLit q [172, 173, 174, 175, 176, 177, 178, 179]) := List.countP_append (p := literal q) (l₁ := [165, 166, 167, 168, 169, 170, 171]) (l₂ := [172, 173, 174, 175, 176, 177, 178, 179])
  have hm := merge_right (literal (valuationOf q) (349)) (literal (valuationOf q) (351)) (countLit q [165, 166, 167, 168, 169, 170, 171]) (countLit q [172, 173, 174, 175, 176, 177, 178, 179]) (count351 q) 1 (meaning349 q) (meaning351 q) hs
  change valuationOf q 349 = false ∨ valuationOf q 351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause929 (q : Snake 81) (h : Conditions q) : valuation q 349 = false ∨ valuation q 351 = true := counterClause929 (baseVal q)

theorem counterClause930 (q : Nat → Bool) : valuationOf q 335 = false ∨ valuationOf q 351 = true := by
  have hs : count351 q = (countLit q [165, 166, 167, 168, 169, 170, 171]) + (countLit q [172, 173, 174, 175, 176, 177, 178, 179]) := List.countP_append (p := literal q) (l₁ := [165, 166, 167, 168, 169, 170, 171]) (l₂ := [172, 173, 174, 175, 176, 177, 178, 179])
  have hm := merge_left (literal (valuationOf q) (335)) (literal (valuationOf q) (351)) (countLit q [165, 166, 167, 168, 169, 170, 171]) (countLit q [172, 173, 174, 175, 176, 177, 178, 179]) (count351 q) 1 (meaning335 q) (meaning351 q) hs
  change valuationOf q 335 = false ∨ valuationOf q 351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause930 (q : Snake 81) (h : Conditions q) : valuation q 335 = false ∨ valuation q 351 = true := counterClause930 (baseVal q)

theorem counterClause931 (q : Nat → Bool) : valuationOf q 335 = false ∨ valuationOf q 349 = false ∨ valuationOf q 352 = true := by
  have hs : count351 q = (countLit q [165, 166, 167, 168, 169, 170, 171]) + (countLit q [172, 173, 174, 175, 176, 177, 178, 179]) := List.countP_append (p := literal q) (l₁ := [165, 166, 167, 168, 169, 170, 171]) (l₂ := [172, 173, 174, 175, 176, 177, 178, 179])
  have hm := merge_two (literal (valuationOf q) (335)) (literal (valuationOf q) (349)) (literal (valuationOf q) (352)) (countLit q [165, 166, 167, 168, 169, 170, 171]) (countLit q [172, 173, 174, 175, 176, 177, 178, 179]) (count351 q) 1 1 (meaning335 q) (meaning349 q) (meaning352 q) hs
  change valuationOf q 335 = false ∨ valuationOf q 349 = false ∨ valuationOf q 352 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause931 (q : Snake 81) (h : Conditions q) : valuation q 335 = false ∨ valuation q 349 = false ∨ valuation q 352 = true := counterClause931 (baseVal q)

theorem counterClause932 (q : Nat → Bool) : valuationOf q 351 = false ∨ valuationOf q 353 = true := by
  have hs : count353 q = (countLit q [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) + (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179]) := List.countP_append (p := literal q) (l₁ := [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) (l₂ := [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179])
  have hm := merge_right (literal (valuationOf q) (351)) (literal (valuationOf q) (353)) (countLit q [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179]) (count353 q) 1 (meaning351 q) (meaning353 q) hs
  change valuationOf q 351 = false ∨ valuationOf q 353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause932 (q : Snake 81) (h : Conditions q) : valuation q 351 = false ∨ valuation q 353 = true := counterClause932 (baseVal q)

theorem counterClause933 (q : Nat → Bool) : valuationOf q 352 = false ∨ valuationOf q 354 = true := by
  have hs : count353 q = (countLit q [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) + (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179]) := List.countP_append (p := literal q) (l₁ := [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) (l₂ := [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179])
  have hm := merge_right (literal (valuationOf q) (352)) (literal (valuationOf q) (354)) (countLit q [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179]) (count353 q) 2 (meaning352 q) (meaning354 q) hs
  change valuationOf q 352 = false ∨ valuationOf q 354 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause933 (q : Snake 81) (h : Conditions q) : valuation q 352 = false ∨ valuation q 354 = true := counterClause933 (baseVal q)

theorem counterClause934 (q : Nat → Bool) : valuationOf q 323 = false ∨ valuationOf q 353 = true := by
  have hs : count353 q = (countLit q [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) + (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179]) := List.countP_append (p := literal q) (l₁ := [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) (l₂ := [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179])
  have hm := merge_left (literal (valuationOf q) (323)) (literal (valuationOf q) (353)) (countLit q [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179]) (count353 q) 1 (meaning323 q) (meaning353 q) hs
  change valuationOf q 323 = false ∨ valuationOf q 353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause934 (q : Snake 81) (h : Conditions q) : valuation q 323 = false ∨ valuation q 353 = true := counterClause934 (baseVal q)

theorem counterClause935 (q : Nat → Bool) : valuationOf q 323 = false ∨ valuationOf q 351 = false ∨ valuationOf q 354 = true := by
  have hs : count353 q = (countLit q [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) + (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179]) := List.countP_append (p := literal q) (l₁ := [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) (l₂ := [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179])
  have hm := merge_two (literal (valuationOf q) (323)) (literal (valuationOf q) (351)) (literal (valuationOf q) (354)) (countLit q [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179]) (count353 q) 1 1 (meaning323 q) (meaning351 q) (meaning354 q) hs
  change valuationOf q 323 = false ∨ valuationOf q 351 = false ∨ valuationOf q 354 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause935 (q : Snake 81) (h : Conditions q) : valuation q 323 = false ∨ valuation q 351 = false ∨ valuation q 354 = true := counterClause935 (baseVal q)

theorem counterClause936 (q : Nat → Bool) : valuationOf q 324 = false ∨ valuationOf q 354 = true := by
  have hs : count353 q = (countLit q [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) + (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179]) := List.countP_append (p := literal q) (l₁ := [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) (l₂ := [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179])
  have hm := merge_left (literal (valuationOf q) (324)) (literal (valuationOf q) (354)) (countLit q [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]) (countLit q [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179]) (count353 q) 2 (meaning324 q) (meaning354 q) hs
  change valuationOf q 324 = false ∨ valuationOf q 354 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause936 (q : Snake 81) (h : Conditions q) : valuation q 324 = false ∨ valuation q 354 = true := counterClause936 (baseVal q)

theorem counterClause937 (q : Nat → Bool) : valuationOf q 353 = false ∨ valuationOf q 355 = true := by
  have hs : count355 q = (countLit q [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) + (countLit q [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179]) := List.countP_append (p := literal q) (l₁ := [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) (l₂ := [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179])
  have hm := merge_right (literal (valuationOf q) (353)) (literal (valuationOf q) (355)) (countLit q [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) (countLit q [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179]) (count355 q) 1 (meaning353 q) (meaning355 q) hs
  change valuationOf q 353 = false ∨ valuationOf q 355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause937 (q : Snake 81) (h : Conditions q) : valuation q 353 = false ∨ valuation q 355 = true := counterClause937 (baseVal q)

theorem counterClause938 (q : Nat → Bool) : valuationOf q 354 = false ∨ valuationOf q 356 = true := by
  have hs : count355 q = (countLit q [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) + (countLit q [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179]) := List.countP_append (p := literal q) (l₁ := [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) (l₂ := [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179])
  have hm := merge_right (literal (valuationOf q) (354)) (literal (valuationOf q) (356)) (countLit q [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) (countLit q [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179]) (count355 q) 2 (meaning354 q) (meaning356 q) hs
  change valuationOf q 354 = false ∨ valuationOf q 356 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause938 (q : Snake 81) (h : Conditions q) : valuation q 354 = false ∨ valuation q 356 = true := counterClause938 (baseVal q)

theorem counterClause939 (q : Nat → Bool) : valuationOf q 295 = false ∨ valuationOf q 355 = true := by
  have hs : count355 q = (countLit q [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) + (countLit q [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179]) := List.countP_append (p := literal q) (l₁ := [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) (l₂ := [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179])
  have hm := merge_left (literal (valuationOf q) (295)) (literal (valuationOf q) (355)) (countLit q [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) (countLit q [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179]) (count355 q) 1 (meaning295 q) (meaning355 q) hs
  change valuationOf q 295 = false ∨ valuationOf q 355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause939 (q : Snake 81) (h : Conditions q) : valuation q 295 = false ∨ valuation q 355 = true := counterClause939 (baseVal q)

theorem counterClause940 (q : Nat → Bool) : valuationOf q 295 = false ∨ valuationOf q 353 = false ∨ valuationOf q 356 = true := by
  have hs : count355 q = (countLit q [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) + (countLit q [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179]) := List.countP_append (p := literal q) (l₁ := [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) (l₂ := [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179])
  have hm := merge_two (literal (valuationOf q) (295)) (literal (valuationOf q) (353)) (literal (valuationOf q) (356)) (countLit q [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) (countLit q [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179]) (count355 q) 1 1 (meaning295 q) (meaning353 q) (meaning356 q) hs
  change valuationOf q 295 = false ∨ valuationOf q 353 = false ∨ valuationOf q 356 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause940 (q : Snake 81) (h : Conditions q) : valuation q 295 = false ∨ valuation q 353 = false ∨ valuation q 356 = true := counterClause940 (baseVal q)

theorem counterClause941 (q : Nat → Bool) : valuationOf q 296 = false ∨ valuationOf q 356 = true := by
  have hs : count355 q = (countLit q [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) + (countLit q [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179]) := List.countP_append (p := literal q) (l₁ := [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) (l₂ := [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179])
  have hm := merge_left (literal (valuationOf q) (296)) (literal (valuationOf q) (356)) (countLit q [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) (countLit q [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179]) (count355 q) 2 (meaning296 q) (meaning356 q) hs
  change valuationOf q 296 = false ∨ valuationOf q 356 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause941 (q : Snake 81) (h : Conditions q) : valuation q 296 = false ∨ valuation q 356 = true := counterClause941 (baseVal q)

theorem counterClause942 (q : Nat → Bool) : valuationOf q 183 = false ∨ valuationOf q 361 = true := by
  have hs : count361 q = (countLit q [183]) + (countLit q [184]) := List.countP_append (p := literal q) (l₁ := [183]) (l₂ := [184])
  have hm := merge_left (literal (valuationOf q) (183)) (literal (valuationOf q) (361)) (countLit q [183]) (countLit q [184]) (count361 q) 1 (meaning183 q) (meaning361 q) hs
  change valuationOf q 183 = false ∨ valuationOf q 361 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause942 (q : Snake 81) (h : Conditions q) : valuation q 183 = false ∨ valuation q 361 = true := counterClause942 (baseVal q)

theorem counterClause943 (q : Nat → Bool) : valuationOf q 186 = false ∨ valuationOf q 363 = true := by
  have hs : count363 q = (countLit q [185]) + (countLit q [186]) := List.countP_append (p := literal q) (l₁ := [185]) (l₂ := [186])
  have hm := merge_right (literal (valuationOf q) (186)) (literal (valuationOf q) (363)) (countLit q [185]) (countLit q [186]) (count363 q) 1 (meaning186 q) (meaning363 q) hs
  change valuationOf q 186 = false ∨ valuationOf q 363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause943 (q : Snake 81) (h : Conditions q) : valuation q 186 = false ∨ valuation q 363 = true := counterClause943 (baseVal q)

theorem counterClause944 (q : Nat → Bool) : valuationOf q 185 = false ∨ valuationOf q 363 = true := by
  have hs : count363 q = (countLit q [185]) + (countLit q [186]) := List.countP_append (p := literal q) (l₁ := [185]) (l₂ := [186])
  have hm := merge_left (literal (valuationOf q) (185)) (literal (valuationOf q) (363)) (countLit q [185]) (countLit q [186]) (count363 q) 1 (meaning185 q) (meaning363 q) hs
  change valuationOf q 185 = false ∨ valuationOf q 363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause944 (q : Snake 81) (h : Conditions q) : valuation q 185 = false ∨ valuation q 363 = true := counterClause944 (baseVal q)

theorem counterClause945 (q : Nat → Bool) : valuationOf q 363 = false ∨ valuationOf q 365 = true := by
  have hs : count365 q = (countLit q [183, 184]) + (countLit q [185, 186]) := List.countP_append (p := literal q) (l₁ := [183, 184]) (l₂ := [185, 186])
  have hm := merge_right (literal (valuationOf q) (363)) (literal (valuationOf q) (365)) (countLit q [183, 184]) (countLit q [185, 186]) (count365 q) 1 (meaning363 q) (meaning365 q) hs
  change valuationOf q 363 = false ∨ valuationOf q 365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause945 (q : Snake 81) (h : Conditions q) : valuation q 363 = false ∨ valuation q 365 = true := counterClause945 (baseVal q)

theorem counterClause946 (q : Nat → Bool) : valuationOf q 361 = false ∨ valuationOf q 365 = true := by
  have hs : count365 q = (countLit q [183, 184]) + (countLit q [185, 186]) := List.countP_append (p := literal q) (l₁ := [183, 184]) (l₂ := [185, 186])
  have hm := merge_left (literal (valuationOf q) (361)) (literal (valuationOf q) (365)) (countLit q [183, 184]) (countLit q [185, 186]) (count365 q) 1 (meaning361 q) (meaning365 q) hs
  change valuationOf q 361 = false ∨ valuationOf q 365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause946 (q : Snake 81) (h : Conditions q) : valuation q 361 = false ∨ valuation q 365 = true := counterClause946 (baseVal q)

theorem counterClause947 (q : Nat → Bool) : valuationOf q 361 = false ∨ valuationOf q 363 = false ∨ valuationOf q 366 = true := by
  have hs : count365 q = (countLit q [183, 184]) + (countLit q [185, 186]) := List.countP_append (p := literal q) (l₁ := [183, 184]) (l₂ := [185, 186])
  have hm := merge_two (literal (valuationOf q) (361)) (literal (valuationOf q) (363)) (literal (valuationOf q) (366)) (countLit q [183, 184]) (countLit q [185, 186]) (count365 q) 1 1 (meaning361 q) (meaning363 q) (meaning366 q) hs
  change valuationOf q 361 = false ∨ valuationOf q 363 = false ∨ valuationOf q 366 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause947 (q : Snake 81) (h : Conditions q) : valuation q 361 = false ∨ valuation q 363 = false ∨ valuation q 366 = true := counterClause947 (baseVal q)

theorem counterClause948 (q : Nat → Bool) : valuationOf q 365 = false ∨ valuationOf q 367 = true := by
  have hs : count367 q = (countLit q [180, 181, 182]) + (countLit q [183, 184, 185, 186]) := List.countP_append (p := literal q) (l₁ := [180, 181, 182]) (l₂ := [183, 184, 185, 186])
  have hm := merge_right (literal (valuationOf q) (365)) (literal (valuationOf q) (367)) (countLit q [180, 181, 182]) (countLit q [183, 184, 185, 186]) (count367 q) 1 (meaning365 q) (meaning367 q) hs
  change valuationOf q 365 = false ∨ valuationOf q 367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause948 (q : Snake 81) (h : Conditions q) : valuation q 365 = false ∨ valuation q 367 = true := counterClause948 (baseVal q)

theorem counterClause949 (q : Nat → Bool) : valuationOf q 366 = false ∨ valuationOf q 368 = true := by
  have hs : count367 q = (countLit q [180, 181, 182]) + (countLit q [183, 184, 185, 186]) := List.countP_append (p := literal q) (l₁ := [180, 181, 182]) (l₂ := [183, 184, 185, 186])
  have hm := merge_right (literal (valuationOf q) (366)) (literal (valuationOf q) (368)) (countLit q [180, 181, 182]) (countLit q [183, 184, 185, 186]) (count367 q) 2 (meaning366 q) (meaning368 q) hs
  change valuationOf q 366 = false ∨ valuationOf q 368 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause949 (q : Snake 81) (h : Conditions q) : valuation q 366 = false ∨ valuation q 368 = true := counterClause949 (baseVal q)

theorem counterClause950 (q : Nat → Bool) : valuationOf q 188 = false ∨ valuationOf q 369 = true := by
  have hs : count369 q = (countLit q [187]) + (countLit q [188]) := List.countP_append (p := literal q) (l₁ := [187]) (l₂ := [188])
  have hm := merge_right (literal (valuationOf q) (188)) (literal (valuationOf q) (369)) (countLit q [187]) (countLit q [188]) (count369 q) 1 (meaning188 q) (meaning369 q) hs
  change valuationOf q 188 = false ∨ valuationOf q 369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause950 (q : Snake 81) (h : Conditions q) : valuation q 188 = false ∨ valuation q 369 = true := counterClause950 (baseVal q)

theorem counterClause951 (q : Nat → Bool) : valuationOf q 189 = false ∨ valuationOf q 371 = true := by
  have hs : count371 q = (countLit q [189]) + (countLit q [190]) := List.countP_append (p := literal q) (l₁ := [189]) (l₂ := [190])
  have hm := merge_left (literal (valuationOf q) (189)) (literal (valuationOf q) (371)) (countLit q [189]) (countLit q [190]) (count371 q) 1 (meaning189 q) (meaning371 q) hs
  change valuationOf q 189 = false ∨ valuationOf q 371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause951 (q : Snake 81) (h : Conditions q) : valuation q 189 = false ∨ valuation q 371 = true := counterClause951 (baseVal q)

theorem counterClause952 (q : Nat → Bool) : valuationOf q 371 = false ∨ valuationOf q 373 = true := by
  have hs : count373 q = (countLit q [187, 188]) + (countLit q [189, 190]) := List.countP_append (p := literal q) (l₁ := [187, 188]) (l₂ := [189, 190])
  have hm := merge_right (literal (valuationOf q) (371)) (literal (valuationOf q) (373)) (countLit q [187, 188]) (countLit q [189, 190]) (count373 q) 1 (meaning371 q) (meaning373 q) hs
  change valuationOf q 371 = false ∨ valuationOf q 373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause952 (q : Snake 81) (h : Conditions q) : valuation q 371 = false ∨ valuation q 373 = true := counterClause952 (baseVal q)

theorem counterClause953 (q : Nat → Bool) : valuationOf q 369 = false ∨ valuationOf q 373 = true := by
  have hs : count373 q = (countLit q [187, 188]) + (countLit q [189, 190]) := List.countP_append (p := literal q) (l₁ := [187, 188]) (l₂ := [189, 190])
  have hm := merge_left (literal (valuationOf q) (369)) (literal (valuationOf q) (373)) (countLit q [187, 188]) (countLit q [189, 190]) (count373 q) 1 (meaning369 q) (meaning373 q) hs
  change valuationOf q 369 = false ∨ valuationOf q 373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause953 (q : Snake 81) (h : Conditions q) : valuation q 369 = false ∨ valuation q 373 = true := counterClause953 (baseVal q)

theorem counterClause954 (q : Nat → Bool) : valuationOf q 192 = false ∨ valuationOf q 375 = true := by
  have hs : count375 q = (countLit q [191]) + (countLit q [192]) := List.countP_append (p := literal q) (l₁ := [191]) (l₂ := [192])
  have hm := merge_right (literal (valuationOf q) (192)) (literal (valuationOf q) (375)) (countLit q [191]) (countLit q [192]) (count375 q) 1 (meaning192 q) (meaning375 q) hs
  change valuationOf q 192 = false ∨ valuationOf q 375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause954 (q : Snake 81) (h : Conditions q) : valuation q 192 = false ∨ valuation q 375 = true := counterClause954 (baseVal q)

theorem counterClause955 (q : Nat → Bool) : valuationOf q 194 = false ∨ valuationOf q 377 = true := by
  have hs : count377 q = (countLit q [193]) + (countLit q [194]) := List.countP_append (p := literal q) (l₁ := [193]) (l₂ := [194])
  have hm := merge_right (literal (valuationOf q) (194)) (literal (valuationOf q) (377)) (countLit q [193]) (countLit q [194]) (count377 q) 1 (meaning194 q) (meaning377 q) hs
  change valuationOf q 194 = false ∨ valuationOf q 377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause955 (q : Snake 81) (h : Conditions q) : valuation q 194 = false ∨ valuation q 377 = true := counterClause955 (baseVal q)

theorem counterClause956 (q : Nat → Bool) : valuationOf q 377 = false ∨ valuationOf q 379 = true := by
  have hs : count379 q = (countLit q [191, 192]) + (countLit q [193, 194]) := List.countP_append (p := literal q) (l₁ := [191, 192]) (l₂ := [193, 194])
  have hm := merge_right (literal (valuationOf q) (377)) (literal (valuationOf q) (379)) (countLit q [191, 192]) (countLit q [193, 194]) (count379 q) 1 (meaning377 q) (meaning379 q) hs
  change valuationOf q 377 = false ∨ valuationOf q 379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause956 (q : Snake 81) (h : Conditions q) : valuation q 377 = false ∨ valuation q 379 = true := counterClause956 (baseVal q)

theorem counterClause957 (q : Nat → Bool) : valuationOf q 375 = false ∨ valuationOf q 379 = true := by
  have hs : count379 q = (countLit q [191, 192]) + (countLit q [193, 194]) := List.countP_append (p := literal q) (l₁ := [191, 192]) (l₂ := [193, 194])
  have hm := merge_left (literal (valuationOf q) (375)) (literal (valuationOf q) (379)) (countLit q [191, 192]) (countLit q [193, 194]) (count379 q) 1 (meaning375 q) (meaning379 q) hs
  change valuationOf q 375 = false ∨ valuationOf q 379 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause957 (q : Snake 81) (h : Conditions q) : valuation q 375 = false ∨ valuation q 379 = true := counterClause957 (baseVal q)

theorem counterClause958 (q : Nat → Bool) : valuationOf q 379 = false ∨ valuationOf q 381 = true := by
  have hs : count381 q = (countLit q [187, 188, 189, 190]) + (countLit q [191, 192, 193, 194]) := List.countP_append (p := literal q) (l₁ := [187, 188, 189, 190]) (l₂ := [191, 192, 193, 194])
  have hm := merge_right (literal (valuationOf q) (379)) (literal (valuationOf q) (381)) (countLit q [187, 188, 189, 190]) (countLit q [191, 192, 193, 194]) (count381 q) 1 (meaning379 q) (meaning381 q) hs
  change valuationOf q 379 = false ∨ valuationOf q 381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause958 (q : Snake 81) (h : Conditions q) : valuation q 379 = false ∨ valuation q 381 = true := counterClause958 (baseVal q)

theorem counterClause959 (q : Nat → Bool) : valuationOf q 373 = false ∨ valuationOf q 381 = true := by
  have hs : count381 q = (countLit q [187, 188, 189, 190]) + (countLit q [191, 192, 193, 194]) := List.countP_append (p := literal q) (l₁ := [187, 188, 189, 190]) (l₂ := [191, 192, 193, 194])
  have hm := merge_left (literal (valuationOf q) (373)) (literal (valuationOf q) (381)) (countLit q [187, 188, 189, 190]) (countLit q [191, 192, 193, 194]) (count381 q) 1 (meaning373 q) (meaning381 q) hs
  change valuationOf q 373 = false ∨ valuationOf q 381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause959 (q : Snake 81) (h : Conditions q) : valuation q 373 = false ∨ valuation q 381 = true := counterClause959 (baseVal q)

theorem counterClause960 (q : Nat → Bool) : valuationOf q 373 = false ∨ valuationOf q 379 = false ∨ valuationOf q 382 = true := by
  have hs : count381 q = (countLit q [187, 188, 189, 190]) + (countLit q [191, 192, 193, 194]) := List.countP_append (p := literal q) (l₁ := [187, 188, 189, 190]) (l₂ := [191, 192, 193, 194])
  have hm := merge_two (literal (valuationOf q) (373)) (literal (valuationOf q) (379)) (literal (valuationOf q) (382)) (countLit q [187, 188, 189, 190]) (countLit q [191, 192, 193, 194]) (count381 q) 1 1 (meaning373 q) (meaning379 q) (meaning382 q) hs
  change valuationOf q 373 = false ∨ valuationOf q 379 = false ∨ valuationOf q 382 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause960 (q : Snake 81) (h : Conditions q) : valuation q 373 = false ∨ valuation q 379 = false ∨ valuation q 382 = true := counterClause960 (baseVal q)

theorem block29 (q : Snake 81) (h : Conditions q) : B112E004.Block29 (valuation q) :=
  ⟨clause929 q h, clause930 q h, clause931 q h, clause932 q h, clause933 q h, clause934 q h, clause935 q h, clause936 q h, clause937 q h, clause938 q h, clause939 q h, clause940 q h, clause941 q h, clause942 q h, clause943 q h, clause944 q h, clause945 q h, clause946 q h, clause947 q h, clause948 q h, clause949 q h, clause950 q h, clause951 q h, clause952 q h, clause953 q h, clause954 q h, clause955 q h, clause956 q h, clause957 q h, clause958 q h, clause959 q h, clause960 q h⟩

end
end Snake9.Regrowth.E112004
