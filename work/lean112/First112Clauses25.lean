import First112Semantics
import Dfs112FirstBooleanInputs
namespace Snake9.Regrowth.First112
noncomputable section
local instance blockDec25 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause801 (q : Snake 81) (h : Conditions q) : valuation q 177 = false ∨ valuation q 345 = true := by
  have hs : count345 q = (countLit q [177]) + (countLit q [178]) := List.countP_append (p := literal (baseVal q)) (l₁ := [177]) (l₂ := [178])
  have hm := merge_left (literal (valuation q) (177)) (literal (valuation q) (345)) (countLit q [177]) (countLit q [178]) (count345 q) 1 (meaning177 q) (meaning345 q) hs
  change valuation q 177 = false ∨ valuation q 345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause802 (q : Snake 81) (h : Conditions q) : valuation q 345 = false ∨ valuation q 347 = true := by
  have hs : count347 q = (countLit q [175, 176]) + (countLit q [177, 178]) := List.countP_append (p := literal (baseVal q)) (l₁ := [175, 176]) (l₂ := [177, 178])
  have hm := merge_right (literal (valuation q) (345)) (literal (valuation q) (347)) (countLit q [175, 176]) (countLit q [177, 178]) (count347 q) 1 (meaning345 q) (meaning347 q) hs
  change valuation q 345 = false ∨ valuation q 347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause803 (q : Snake 81) (h : Conditions q) : valuation q 343 = false ∨ valuation q 347 = true := by
  have hs : count347 q = (countLit q [175, 176]) + (countLit q [177, 178]) := List.countP_append (p := literal (baseVal q)) (l₁ := [175, 176]) (l₂ := [177, 178])
  have hm := merge_left (literal (valuation q) (343)) (literal (valuation q) (347)) (countLit q [175, 176]) (countLit q [177, 178]) (count347 q) 1 (meaning343 q) (meaning347 q) hs
  change valuation q 343 = false ∨ valuation q 347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause804 (q : Snake 81) (h : Conditions q) : valuation q 180 = false ∨ valuation q 349 = true := by
  have hs : count349 q = (countLit q [179]) + (countLit q [180]) := List.countP_append (p := literal (baseVal q)) (l₁ := [179]) (l₂ := [180])
  have hm := merge_right (literal (valuation q) (180)) (literal (valuation q) (349)) (countLit q [179]) (countLit q [180]) (count349 q) 1 (meaning180 q) (meaning349 q) hs
  change valuation q 180 = false ∨ valuation q 349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause805 (q : Snake 81) (h : Conditions q) : valuation q 349 = false ∨ valuation q 353 = true := by
  have hs : count353 q = (countLit q [179, 180]) + (countLit q [181, 182]) := List.countP_append (p := literal (baseVal q)) (l₁ := [179, 180]) (l₂ := [181, 182])
  have hm := merge_left (literal (valuation q) (349)) (literal (valuation q) (353)) (countLit q [179, 180]) (countLit q [181, 182]) (count353 q) 1 (meaning349 q) (meaning353 q) hs
  change valuation q 349 = false ∨ valuation q 353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause806 (q : Snake 81) (h : Conditions q) : valuation q 353 = false ∨ valuation q 355 = true := by
  have hs : count355 q = (countLit q [175, 176, 177, 178]) + (countLit q [179, 180, 181, 182]) := List.countP_append (p := literal (baseVal q)) (l₁ := [175, 176, 177, 178]) (l₂ := [179, 180, 181, 182])
  have hm := merge_right (literal (valuation q) (353)) (literal (valuation q) (355)) (countLit q [175, 176, 177, 178]) (countLit q [179, 180, 181, 182]) (count355 q) 1 (meaning353 q) (meaning355 q) hs
  change valuation q 353 = false ∨ valuation q 355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause807 (q : Snake 81) (h : Conditions q) : valuation q 347 = false ∨ valuation q 355 = true := by
  have hs : count355 q = (countLit q [175, 176, 177, 178]) + (countLit q [179, 180, 181, 182]) := List.countP_append (p := literal (baseVal q)) (l₁ := [175, 176, 177, 178]) (l₂ := [179, 180, 181, 182])
  have hm := merge_left (literal (valuation q) (347)) (literal (valuation q) (355)) (countLit q [175, 176, 177, 178]) (countLit q [179, 180, 181, 182]) (count355 q) 1 (meaning347 q) (meaning355 q) hs
  change valuation q 347 = false ∨ valuation q 355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause808 (q : Snake 81) (h : Conditions q) : valuation q 347 = false ∨ valuation q 353 = false ∨ valuation q 356 = true := by
  have hs : count355 q = (countLit q [175, 176, 177, 178]) + (countLit q [179, 180, 181, 182]) := List.countP_append (p := literal (baseVal q)) (l₁ := [175, 176, 177, 178]) (l₂ := [179, 180, 181, 182])
  have hm := merge_two (literal (valuation q) (347)) (literal (valuation q) (353)) (literal (valuation q) (356)) (countLit q [175, 176, 177, 178]) (countLit q [179, 180, 181, 182]) (count355 q) 1 1 (meaning347 q) (meaning353 q) (meaning356 q) hs
  change valuation q 347 = false ∨ valuation q 353 = false ∨ valuation q 356 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause809 (q : Snake 81) (h : Conditions q) : valuation q 355 = false ∨ valuation q 357 = true := by
  have hs : count357 q = (countLit q [168, 169, 170, 171, 172, 173, 174]) + (countLit q [175, 176, 177, 178, 179, 180, 181, 182]) := List.countP_append (p := literal (baseVal q)) (l₁ := [168, 169, 170, 171, 172, 173, 174]) (l₂ := [175, 176, 177, 178, 179, 180, 181, 182])
  have hm := merge_right (literal (valuation q) (355)) (literal (valuation q) (357)) (countLit q [168, 169, 170, 171, 172, 173, 174]) (countLit q [175, 176, 177, 178, 179, 180, 181, 182]) (count357 q) 1 (meaning355 q) (meaning357 q) hs
  change valuation q 355 = false ∨ valuation q 357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause810 (q : Snake 81) (h : Conditions q) : valuation q 356 = false ∨ valuation q 358 = true := by
  have hs : count357 q = (countLit q [168, 169, 170, 171, 172, 173, 174]) + (countLit q [175, 176, 177, 178, 179, 180, 181, 182]) := List.countP_append (p := literal (baseVal q)) (l₁ := [168, 169, 170, 171, 172, 173, 174]) (l₂ := [175, 176, 177, 178, 179, 180, 181, 182])
  have hm := merge_right (literal (valuation q) (356)) (literal (valuation q) (358)) (countLit q [168, 169, 170, 171, 172, 173, 174]) (countLit q [175, 176, 177, 178, 179, 180, 181, 182]) (count357 q) 2 (meaning356 q) (meaning358 q) hs
  change valuation q 356 = false ∨ valuation q 358 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause811 (q : Snake 81) (h : Conditions q) : valuation q 341 = false ∨ valuation q 357 = true := by
  have hs : count357 q = (countLit q [168, 169, 170, 171, 172, 173, 174]) + (countLit q [175, 176, 177, 178, 179, 180, 181, 182]) := List.countP_append (p := literal (baseVal q)) (l₁ := [168, 169, 170, 171, 172, 173, 174]) (l₂ := [175, 176, 177, 178, 179, 180, 181, 182])
  have hm := merge_left (literal (valuation q) (341)) (literal (valuation q) (357)) (countLit q [168, 169, 170, 171, 172, 173, 174]) (countLit q [175, 176, 177, 178, 179, 180, 181, 182]) (count357 q) 1 (meaning341 q) (meaning357 q) hs
  change valuation q 341 = false ∨ valuation q 357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause812 (q : Snake 81) (h : Conditions q) : valuation q 341 = false ∨ valuation q 355 = false ∨ valuation q 358 = true := by
  have hs : count357 q = (countLit q [168, 169, 170, 171, 172, 173, 174]) + (countLit q [175, 176, 177, 178, 179, 180, 181, 182]) := List.countP_append (p := literal (baseVal q)) (l₁ := [168, 169, 170, 171, 172, 173, 174]) (l₂ := [175, 176, 177, 178, 179, 180, 181, 182])
  have hm := merge_two (literal (valuation q) (341)) (literal (valuation q) (355)) (literal (valuation q) (358)) (countLit q [168, 169, 170, 171, 172, 173, 174]) (countLit q [175, 176, 177, 178, 179, 180, 181, 182]) (count357 q) 1 1 (meaning341 q) (meaning355 q) (meaning358 q) hs
  change valuation q 341 = false ∨ valuation q 355 = false ∨ valuation q 358 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause813 (q : Snake 81) (h : Conditions q) : valuation q 342 = false ∨ valuation q 358 = true := by
  have hs : count357 q = (countLit q [168, 169, 170, 171, 172, 173, 174]) + (countLit q [175, 176, 177, 178, 179, 180, 181, 182]) := List.countP_append (p := literal (baseVal q)) (l₁ := [168, 169, 170, 171, 172, 173, 174]) (l₂ := [175, 176, 177, 178, 179, 180, 181, 182])
  have hm := merge_left (literal (valuation q) (342)) (literal (valuation q) (358)) (countLit q [168, 169, 170, 171, 172, 173, 174]) (countLit q [175, 176, 177, 178, 179, 180, 181, 182]) (count357 q) 2 (meaning342 q) (meaning358 q) hs
  change valuation q 342 = false ∨ valuation q 358 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause814 (q : Snake 81) (h : Conditions q) : valuation q 357 = false ∨ valuation q 359 = true := by
  have hs : count359 q = (countLit q [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167]) + (countLit q [168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) := List.countP_append (p := literal (baseVal q)) (l₁ := [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167]) (l₂ := [168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182])
  have hm := merge_right (literal (valuation q) (357)) (literal (valuation q) (359)) (countLit q [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167]) (countLit q [168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (count359 q) 1 (meaning357 q) (meaning359 q) hs
  change valuation q 357 = false ∨ valuation q 359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause815 (q : Snake 81) (h : Conditions q) : valuation q 358 = false ∨ valuation q 360 = true := by
  have hs : count359 q = (countLit q [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167]) + (countLit q [168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) := List.countP_append (p := literal (baseVal q)) (l₁ := [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167]) (l₂ := [168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182])
  have hm := merge_right (literal (valuation q) (358)) (literal (valuation q) (360)) (countLit q [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167]) (countLit q [168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (count359 q) 2 (meaning358 q) (meaning360 q) hs
  change valuation q 358 = false ∨ valuation q 360 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause816 (q : Snake 81) (h : Conditions q) : valuation q 329 = false ∨ valuation q 359 = true := by
  have hs : count359 q = (countLit q [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167]) + (countLit q [168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) := List.countP_append (p := literal (baseVal q)) (l₁ := [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167]) (l₂ := [168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182])
  have hm := merge_left (literal (valuation q) (329)) (literal (valuation q) (359)) (countLit q [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167]) (countLit q [168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (count359 q) 1 (meaning329 q) (meaning359 q) hs
  change valuation q 329 = false ∨ valuation q 359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause817 (q : Snake 81) (h : Conditions q) : valuation q 359 = false ∨ valuation q 361 = true := by
  have hs : count361 q = (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) + (countLit q [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) := List.countP_append (p := literal (baseVal q)) (l₁ := [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) (l₂ := [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182])
  have hm := merge_right (literal (valuation q) (359)) (literal (valuation q) (361)) (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) (countLit q [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (count361 q) 1 (meaning359 q) (meaning361 q) hs
  change valuation q 359 = false ∨ valuation q 361 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause818 (q : Snake 81) (h : Conditions q) : valuation q 360 = false ∨ valuation q 362 = true := by
  have hs : count361 q = (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) + (countLit q [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) := List.countP_append (p := literal (baseVal q)) (l₁ := [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) (l₂ := [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182])
  have hm := merge_right (literal (valuation q) (360)) (literal (valuation q) (362)) (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) (countLit q [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (count361 q) 2 (meaning360 q) (meaning362 q) hs
  change valuation q 360 = false ∨ valuation q 362 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause819 (q : Snake 81) (h : Conditions q) : valuation q 301 = false ∨ valuation q 361 = true := by
  have hs : count361 q = (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) + (countLit q [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) := List.countP_append (p := literal (baseVal q)) (l₁ := [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) (l₂ := [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182])
  have hm := merge_left (literal (valuation q) (301)) (literal (valuation q) (361)) (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) (countLit q [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (count361 q) 1 (meaning301 q) (meaning361 q) hs
  change valuation q 301 = false ∨ valuation q 361 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause820 (q : Snake 81) (h : Conditions q) : valuation q 301 = false ∨ valuation q 359 = false ∨ valuation q 362 = true := by
  have hs : count361 q = (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) + (countLit q [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) := List.countP_append (p := literal (baseVal q)) (l₁ := [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) (l₂ := [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182])
  have hm := merge_two (literal (valuation q) (301)) (literal (valuation q) (359)) (literal (valuation q) (362)) (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) (countLit q [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (count361 q) 1 1 (meaning301 q) (meaning359 q) (meaning362 q) hs
  change valuation q 301 = false ∨ valuation q 359 = false ∨ valuation q 362 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause821 (q : Snake 81) (h : Conditions q) : valuation q 302 = false ∨ valuation q 362 = true := by
  have hs : count361 q = (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) + (countLit q [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) := List.countP_append (p := literal (baseVal q)) (l₁ := [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) (l₂ := [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182])
  have hm := merge_left (literal (valuation q) (302)) (literal (valuation q) (362)) (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) (countLit q [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (count361 q) 2 (meaning302 q) (meaning362 q) hs
  change valuation q 302 = false ∨ valuation q 362 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause822 (q : Snake 81) (h : Conditions q) : valuation q 185 = false ∨ valuation q 363 = true := by
  have hs : count363 q = (countLit q [184]) + (countLit q [185]) := List.countP_append (p := literal (baseVal q)) (l₁ := [184]) (l₂ := [185])
  have hm := merge_right (literal (valuation q) (185)) (literal (valuation q) (363)) (countLit q [184]) (countLit q [185]) (count363 q) 1 (meaning185 q) (meaning363 q) hs
  change valuation q 185 = false ∨ valuation q 363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause823 (q : Snake 81) (h : Conditions q) : valuation q 363 = false ∨ valuation q 365 = true := by
  have hs : count365 q = (countLit q [183]) + (countLit q [184, 185]) := List.countP_append (p := literal (baseVal q)) (l₁ := [183]) (l₂ := [184, 185])
  have hm := merge_right (literal (valuation q) (363)) (literal (valuation q) (365)) (countLit q [183]) (countLit q [184, 185]) (count365 q) 1 (meaning363 q) (meaning365 q) hs
  change valuation q 363 = false ∨ valuation q 365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause824 (q : Snake 81) (h : Conditions q) : valuation q 187 = false ∨ valuation q 367 = true := by
  have hs : count367 q = (countLit q [186]) + (countLit q [187]) := List.countP_append (p := literal (baseVal q)) (l₁ := [186]) (l₂ := [187])
  have hm := merge_right (literal (valuation q) (187)) (literal (valuation q) (367)) (countLit q [186]) (countLit q [187]) (count367 q) 1 (meaning187 q) (meaning367 q) hs
  change valuation q 187 = false ∨ valuation q 367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause825 (q : Snake 81) (h : Conditions q) : valuation q 188 = false ∨ valuation q 369 = true := by
  have hs : count369 q = (countLit q [188]) + (countLit q [189]) := List.countP_append (p := literal (baseVal q)) (l₁ := [188]) (l₂ := [189])
  have hm := merge_left (literal (valuation q) (188)) (literal (valuation q) (369)) (countLit q [188]) (countLit q [189]) (count369 q) 1 (meaning188 q) (meaning369 q) hs
  change valuation q 188 = false ∨ valuation q 369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause826 (q : Snake 81) (h : Conditions q) : valuation q 369 = false ∨ valuation q 371 = true := by
  have hs : count371 q = (countLit q [186, 187]) + (countLit q [188, 189]) := List.countP_append (p := literal (baseVal q)) (l₁ := [186, 187]) (l₂ := [188, 189])
  have hm := merge_right (literal (valuation q) (369)) (literal (valuation q) (371)) (countLit q [186, 187]) (countLit q [188, 189]) (count371 q) 1 (meaning369 q) (meaning371 q) hs
  change valuation q 369 = false ∨ valuation q 371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause827 (q : Snake 81) (h : Conditions q) : valuation q 367 = false ∨ valuation q 371 = true := by
  have hs : count371 q = (countLit q [186, 187]) + (countLit q [188, 189]) := List.countP_append (p := literal (baseVal q)) (l₁ := [186, 187]) (l₂ := [188, 189])
  have hm := merge_left (literal (valuation q) (367)) (literal (valuation q) (371)) (countLit q [186, 187]) (countLit q [188, 189]) (count371 q) 1 (meaning367 q) (meaning371 q) hs
  change valuation q 367 = false ∨ valuation q 371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause828 (q : Snake 81) (h : Conditions q) : valuation q 371 = false ∨ valuation q 373 = true := by
  have hs : count373 q = (countLit q [183, 184, 185]) + (countLit q [186, 187, 188, 189]) := List.countP_append (p := literal (baseVal q)) (l₁ := [183, 184, 185]) (l₂ := [186, 187, 188, 189])
  have hm := merge_right (literal (valuation q) (371)) (literal (valuation q) (373)) (countLit q [183, 184, 185]) (countLit q [186, 187, 188, 189]) (count373 q) 1 (meaning371 q) (meaning373 q) hs
  change valuation q 371 = false ∨ valuation q 373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause829 (q : Snake 81) (h : Conditions q) : valuation q 365 = false ∨ valuation q 373 = true := by
  have hs : count373 q = (countLit q [183, 184, 185]) + (countLit q [186, 187, 188, 189]) := List.countP_append (p := literal (baseVal q)) (l₁ := [183, 184, 185]) (l₂ := [186, 187, 188, 189])
  have hm := merge_left (literal (valuation q) (365)) (literal (valuation q) (373)) (countLit q [183, 184, 185]) (countLit q [186, 187, 188, 189]) (count373 q) 1 (meaning365 q) (meaning373 q) hs
  change valuation q 365 = false ∨ valuation q 373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause830 (q : Snake 81) (h : Conditions q) : valuation q 193 = false ∨ valuation q 377 = true := by
  have hs : count377 q = (countLit q [192]) + (countLit q [193]) := List.countP_append (p := literal (baseVal q)) (l₁ := [192]) (l₂ := [193])
  have hm := merge_right (literal (valuation q) (193)) (literal (valuation q) (377)) (countLit q [192]) (countLit q [193]) (count377 q) 1 (meaning193 q) (meaning377 q) hs
  change valuation q 193 = false ∨ valuation q 377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause831 (q : Snake 81) (h : Conditions q) : valuation q 192 = false ∨ valuation q 377 = true := by
  have hs : count377 q = (countLit q [192]) + (countLit q [193]) := List.countP_append (p := literal (baseVal q)) (l₁ := [192]) (l₂ := [193])
  have hm := merge_left (literal (valuation q) (192)) (literal (valuation q) (377)) (countLit q [192]) (countLit q [193]) (count377 q) 1 (meaning192 q) (meaning377 q) hs
  change valuation q 192 = false ∨ valuation q 377 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause832 (q : Snake 81) (h : Conditions q) : valuation q 192 = false ∨ valuation q 193 = false ∨ valuation q 378 = true := by
  have hs : count377 q = (countLit q [192]) + (countLit q [193]) := List.countP_append (p := literal (baseVal q)) (l₁ := [192]) (l₂ := [193])
  have hm := merge_two (literal (valuation q) (192)) (literal (valuation q) (193)) (literal (valuation q) (378)) (countLit q [192]) (countLit q [193]) (count377 q) 1 1 (meaning192 q) (meaning193 q) (meaning378 q) hs
  change valuation q 192 = false ∨ valuation q 193 = false ∨ valuation q 378 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem block25 (q : Snake 81) (h : Conditions q) : Dfs112FirstBoolean.Block25 (valuation q) :=
  ⟨clause801 q h, clause802 q h, clause803 q h, clause804 q h, clause805 q h, clause806 q h, clause807 q h, clause808 q h, clause809 q h, clause810 q h, clause811 q h, clause812 q h, clause813 q h, clause814 q h, clause815 q h, clause816 q h, clause817 q h, clause818 q h, clause819 q h, clause820 q h, clause821 q h, clause822 q h, clause823 q h, clause824 q h, clause825 q h, clause826 q h, clause827 q h, clause828 q h, clause829 q h, clause830 q h, clause831 q h, clause832 q h⟩

end
end Snake9.Regrowth.First112
