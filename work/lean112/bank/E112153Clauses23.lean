import E112153Semantics
import B112E153Inputs
namespace Snake9.Regrowth.E112153
noncomputable section
local instance blockDec23 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause737 (q : Nat → Bool) : valuationOf q 276 = false ∨ valuationOf q 306 = true := by
  have hs : count305 q = (countLit q [125, 126, 127, 128, 129, 130, 131, 133, 134, 135, 136, 137, 138, 139, 140]) + (countLit q [141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 130, 131, 133, 134, 135, 136, 137, 138, 139, 140]) (l₂ := [141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155])
  have hm := merge_left (literal (valuationOf q) (276)) (literal (valuationOf q) (306)) (countLit q [125, 126, 127, 128, 129, 130, 131, 133, 134, 135, 136, 137, 138, 139, 140]) (countLit q [141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (count305 q) 2 (meaning276 q) (meaning306 q) hs
  change valuationOf q 276 = false ∨ valuationOf q 306 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause737 (q : Snake 81) (h : Conditions q) : valuation q 276 = false ∨ valuation q 306 = true := counterClause737 (baseVal q)

theorem counterClause738 (q : Nat → Bool) : valuationOf q 158 = false ∨ valuationOf q 307 = true := by
  have hs : count307 q = (countLit q [157]) + (countLit q [158]) := List.countP_append (p := literal q) (l₁ := [157]) (l₂ := [158])
  have hm := merge_right (literal (valuationOf q) (158)) (literal (valuationOf q) (307)) (countLit q [157]) (countLit q [158]) (count307 q) 1 (meaning158 q) (meaning307 q) hs
  change valuationOf q 158 = false ∨ valuationOf q 307 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause738 (q : Snake 81) (h : Conditions q) : valuation q 158 = false ∨ valuation q 307 = true := counterClause738 (baseVal q)

theorem counterClause739 (q : Nat → Bool) : valuationOf q 157 = false ∨ valuationOf q 307 = true := by
  have hs : count307 q = (countLit q [157]) + (countLit q [158]) := List.countP_append (p := literal q) (l₁ := [157]) (l₂ := [158])
  have hm := merge_left (literal (valuationOf q) (157)) (literal (valuationOf q) (307)) (countLit q [157]) (countLit q [158]) (count307 q) 1 (meaning157 q) (meaning307 q) hs
  change valuationOf q 157 = false ∨ valuationOf q 307 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause739 (q : Snake 81) (h : Conditions q) : valuation q 157 = false ∨ valuation q 307 = true := counterClause739 (baseVal q)

theorem counterClause740 (q : Nat → Bool) : valuationOf q 307 = false ∨ valuationOf q 309 = true := by
  have hs : count309 q = (countLit q [156]) + (countLit q [157, 158]) := List.countP_append (p := literal q) (l₁ := [156]) (l₂ := [157, 158])
  have hm := merge_right (literal (valuationOf q) (307)) (literal (valuationOf q) (309)) (countLit q [156]) (countLit q [157, 158]) (count309 q) 1 (meaning307 q) (meaning309 q) hs
  change valuationOf q 307 = false ∨ valuationOf q 309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause740 (q : Snake 81) (h : Conditions q) : valuation q 307 = false ∨ valuation q 309 = true := counterClause740 (baseVal q)

theorem counterClause741 (q : Nat → Bool) : valuationOf q 160 = false ∨ valuationOf q 311 = true := by
  have hs : count311 q = (countLit q [159]) + (countLit q [160]) := List.countP_append (p := literal q) (l₁ := [159]) (l₂ := [160])
  have hm := merge_right (literal (valuationOf q) (160)) (literal (valuationOf q) (311)) (countLit q [159]) (countLit q [160]) (count311 q) 1 (meaning160 q) (meaning311 q) hs
  change valuationOf q 160 = false ∨ valuationOf q 311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause741 (q : Snake 81) (h : Conditions q) : valuation q 160 = false ∨ valuation q 311 = true := counterClause741 (baseVal q)

theorem counterClause742 (q : Nat → Bool) : valuationOf q 311 = false ∨ valuationOf q 315 = true := by
  have hs : count315 q = (countLit q [159, 160]) + (countLit q [161, 162]) := List.countP_append (p := literal q) (l₁ := [159, 160]) (l₂ := [161, 162])
  have hm := merge_left (literal (valuationOf q) (311)) (literal (valuationOf q) (315)) (countLit q [159, 160]) (countLit q [161, 162]) (count315 q) 1 (meaning311 q) (meaning315 q) hs
  change valuationOf q 311 = false ∨ valuationOf q 315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause742 (q : Snake 81) (h : Conditions q) : valuation q 311 = false ∨ valuation q 315 = true := counterClause742 (baseVal q)

theorem counterClause743 (q : Nat → Bool) : valuationOf q 315 = false ∨ valuationOf q 317 = true := by
  have hs : count317 q = (countLit q [156, 157, 158]) + (countLit q [159, 160, 161, 162]) := List.countP_append (p := literal q) (l₁ := [156, 157, 158]) (l₂ := [159, 160, 161, 162])
  have hm := merge_right (literal (valuationOf q) (315)) (literal (valuationOf q) (317)) (countLit q [156, 157, 158]) (countLit q [159, 160, 161, 162]) (count317 q) 1 (meaning315 q) (meaning317 q) hs
  change valuationOf q 315 = false ∨ valuationOf q 317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause743 (q : Snake 81) (h : Conditions q) : valuation q 315 = false ∨ valuation q 317 = true := counterClause743 (baseVal q)

theorem counterClause744 (q : Nat → Bool) : valuationOf q 309 = false ∨ valuationOf q 317 = true := by
  have hs : count317 q = (countLit q [156, 157, 158]) + (countLit q [159, 160, 161, 162]) := List.countP_append (p := literal q) (l₁ := [156, 157, 158]) (l₂ := [159, 160, 161, 162])
  have hm := merge_left (literal (valuationOf q) (309)) (literal (valuationOf q) (317)) (countLit q [156, 157, 158]) (countLit q [159, 160, 161, 162]) (count317 q) 1 (meaning309 q) (meaning317 q) hs
  change valuationOf q 309 = false ∨ valuationOf q 317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause744 (q : Snake 81) (h : Conditions q) : valuation q 309 = false ∨ valuation q 317 = true := counterClause744 (baseVal q)

theorem counterClause745 (q : Nat → Bool) : valuationOf q 164 = false ∨ valuationOf q 319 = true := by
  have hs : count319 q = (countLit q [163]) + (countLit q [164]) := List.countP_append (p := literal q) (l₁ := [163]) (l₂ := [164])
  have hm := merge_right (literal (valuationOf q) (164)) (literal (valuationOf q) (319)) (countLit q [163]) (countLit q [164]) (count319 q) 1 (meaning164 q) (meaning319 q) hs
  change valuationOf q 164 = false ∨ valuationOf q 319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause745 (q : Snake 81) (h : Conditions q) : valuation q 164 = false ∨ valuation q 319 = true := counterClause745 (baseVal q)

theorem counterClause746 (q : Nat → Bool) : valuationOf q 319 = false ∨ valuationOf q 323 = true := by
  have hs : count323 q = (countLit q [163, 164]) + (countLit q [165, 166]) := List.countP_append (p := literal q) (l₁ := [163, 164]) (l₂ := [165, 166])
  have hm := merge_left (literal (valuationOf q) (319)) (literal (valuationOf q) (323)) (countLit q [163, 164]) (countLit q [165, 166]) (count323 q) 1 (meaning319 q) (meaning323 q) hs
  change valuationOf q 319 = false ∨ valuationOf q 323 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause746 (q : Snake 81) (h : Conditions q) : valuation q 319 = false ∨ valuation q 323 = true := counterClause746 (baseVal q)

theorem counterClause747 (q : Nat → Bool) : valuationOf q 168 = false ∨ valuationOf q 325 = true := by
  have hs : count325 q = (countLit q [167]) + (countLit q [168]) := List.countP_append (p := literal q) (l₁ := [167]) (l₂ := [168])
  have hm := merge_right (literal (valuationOf q) (168)) (literal (valuationOf q) (325)) (countLit q [167]) (countLit q [168]) (count325 q) 1 (meaning168 q) (meaning325 q) hs
  change valuationOf q 168 = false ∨ valuationOf q 325 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause747 (q : Snake 81) (h : Conditions q) : valuation q 168 = false ∨ valuation q 325 = true := counterClause747 (baseVal q)

theorem counterClause748 (q : Nat → Bool) : valuationOf q 325 = false ∨ valuationOf q 329 = true := by
  have hs : count329 q = (countLit q [167, 168]) + (countLit q [169, 170]) := List.countP_append (p := literal q) (l₁ := [167, 168]) (l₂ := [169, 170])
  have hm := merge_left (literal (valuationOf q) (325)) (literal (valuationOf q) (329)) (countLit q [167, 168]) (countLit q [169, 170]) (count329 q) 1 (meaning325 q) (meaning329 q) hs
  change valuationOf q 325 = false ∨ valuationOf q 329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause748 (q : Snake 81) (h : Conditions q) : valuation q 325 = false ∨ valuation q 329 = true := counterClause748 (baseVal q)

theorem counterClause749 (q : Nat → Bool) : valuationOf q 329 = false ∨ valuationOf q 331 = true := by
  have hs : count331 q = (countLit q [163, 164, 165, 166]) + (countLit q [167, 168, 169, 170]) := List.countP_append (p := literal q) (l₁ := [163, 164, 165, 166]) (l₂ := [167, 168, 169, 170])
  have hm := merge_right (literal (valuationOf q) (329)) (literal (valuationOf q) (331)) (countLit q [163, 164, 165, 166]) (countLit q [167, 168, 169, 170]) (count331 q) 1 (meaning329 q) (meaning331 q) hs
  change valuationOf q 329 = false ∨ valuationOf q 331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause749 (q : Snake 81) (h : Conditions q) : valuation q 329 = false ∨ valuation q 331 = true := counterClause749 (baseVal q)

theorem counterClause750 (q : Nat → Bool) : valuationOf q 323 = false ∨ valuationOf q 331 = true := by
  have hs : count331 q = (countLit q [163, 164, 165, 166]) + (countLit q [167, 168, 169, 170]) := List.countP_append (p := literal q) (l₁ := [163, 164, 165, 166]) (l₂ := [167, 168, 169, 170])
  have hm := merge_left (literal (valuationOf q) (323)) (literal (valuationOf q) (331)) (countLit q [163, 164, 165, 166]) (countLit q [167, 168, 169, 170]) (count331 q) 1 (meaning323 q) (meaning331 q) hs
  change valuationOf q 323 = false ∨ valuationOf q 331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause750 (q : Snake 81) (h : Conditions q) : valuation q 323 = false ∨ valuation q 331 = true := counterClause750 (baseVal q)

theorem counterClause751 (q : Nat → Bool) : valuationOf q 331 = false ∨ valuationOf q 333 = true := by
  have hs : count333 q = (countLit q [156, 157, 158, 159, 160, 161, 162]) + (countLit q [163, 164, 165, 166, 167, 168, 169, 170]) := List.countP_append (p := literal q) (l₁ := [156, 157, 158, 159, 160, 161, 162]) (l₂ := [163, 164, 165, 166, 167, 168, 169, 170])
  have hm := merge_right (literal (valuationOf q) (331)) (literal (valuationOf q) (333)) (countLit q [156, 157, 158, 159, 160, 161, 162]) (countLit q [163, 164, 165, 166, 167, 168, 169, 170]) (count333 q) 1 (meaning331 q) (meaning333 q) hs
  change valuationOf q 331 = false ∨ valuationOf q 333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause751 (q : Snake 81) (h : Conditions q) : valuation q 331 = false ∨ valuation q 333 = true := counterClause751 (baseVal q)

theorem counterClause752 (q : Nat → Bool) : valuationOf q 317 = false ∨ valuationOf q 333 = true := by
  have hs : count333 q = (countLit q [156, 157, 158, 159, 160, 161, 162]) + (countLit q [163, 164, 165, 166, 167, 168, 169, 170]) := List.countP_append (p := literal q) (l₁ := [156, 157, 158, 159, 160, 161, 162]) (l₂ := [163, 164, 165, 166, 167, 168, 169, 170])
  have hm := merge_left (literal (valuationOf q) (317)) (literal (valuationOf q) (333)) (countLit q [156, 157, 158, 159, 160, 161, 162]) (countLit q [163, 164, 165, 166, 167, 168, 169, 170]) (count333 q) 1 (meaning317 q) (meaning333 q) hs
  change valuationOf q 317 = false ∨ valuationOf q 333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause752 (q : Snake 81) (h : Conditions q) : valuation q 317 = false ∨ valuation q 333 = true := counterClause752 (baseVal q)

theorem counterClause753 (q : Nat → Bool) : valuationOf q 172 = false ∨ valuationOf q 335 = true := by
  have hs : count335 q = (countLit q [171]) + (countLit q [172]) := List.countP_append (p := literal q) (l₁ := [171]) (l₂ := [172])
  have hm := merge_right (literal (valuationOf q) (172)) (literal (valuationOf q) (335)) (countLit q [171]) (countLit q [172]) (count335 q) 1 (meaning172 q) (meaning335 q) hs
  change valuationOf q 172 = false ∨ valuationOf q 335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause753 (q : Snake 81) (h : Conditions q) : valuation q 172 = false ∨ valuation q 335 = true := counterClause753 (baseVal q)

theorem counterClause754 (q : Nat → Bool) : valuationOf q 335 = false ∨ valuationOf q 339 = true := by
  have hs : count339 q = (countLit q [171, 172]) + (countLit q [173, 174]) := List.countP_append (p := literal q) (l₁ := [171, 172]) (l₂ := [173, 174])
  have hm := merge_left (literal (valuationOf q) (335)) (literal (valuationOf q) (339)) (countLit q [171, 172]) (countLit q [173, 174]) (count339 q) 1 (meaning335 q) (meaning339 q) hs
  change valuationOf q 335 = false ∨ valuationOf q 339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause754 (q : Snake 81) (h : Conditions q) : valuation q 335 = false ∨ valuation q 339 = true := counterClause754 (baseVal q)

theorem counterClause755 (q : Nat → Bool) : valuationOf q 339 = false ∨ valuationOf q 347 = true := by
  have hs : count347 q = (countLit q [171, 172, 173, 174]) + (countLit q [175, 176, 177, 178]) := List.countP_append (p := literal q) (l₁ := [171, 172, 173, 174]) (l₂ := [175, 176, 177, 178])
  have hm := merge_left (literal (valuationOf q) (339)) (literal (valuationOf q) (347)) (countLit q [171, 172, 173, 174]) (countLit q [175, 176, 177, 178]) (count347 q) 1 (meaning339 q) (meaning347 q) hs
  change valuationOf q 339 = false ∨ valuationOf q 347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause755 (q : Snake 81) (h : Conditions q) : valuation q 339 = false ∨ valuation q 347 = true := counterClause755 (baseVal q)

theorem counterClause756 (q : Nat → Bool) : valuationOf q 183 = false ∨ valuationOf q 355 = true := by
  have hs : count355 q = (countLit q [183]) + (countLit q [184]) := List.countP_append (p := literal q) (l₁ := [183]) (l₂ := [184])
  have hm := merge_left (literal (valuationOf q) (183)) (literal (valuationOf q) (355)) (countLit q [183]) (countLit q [184]) (count355 q) 1 (meaning183 q) (meaning355 q) hs
  change valuationOf q 183 = false ∨ valuationOf q 355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause756 (q : Snake 81) (h : Conditions q) : valuation q 183 = false ∨ valuation q 355 = true := counterClause756 (baseVal q)

theorem counterClause757 (q : Nat → Bool) : valuationOf q 186 = false ∨ valuationOf q 357 = true := by
  have hs : count357 q = (countLit q [185]) + (countLit q [186]) := List.countP_append (p := literal q) (l₁ := [185]) (l₂ := [186])
  have hm := merge_right (literal (valuationOf q) (186)) (literal (valuationOf q) (357)) (countLit q [185]) (countLit q [186]) (count357 q) 1 (meaning186 q) (meaning357 q) hs
  change valuationOf q 186 = false ∨ valuationOf q 357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause757 (q : Snake 81) (h : Conditions q) : valuation q 186 = false ∨ valuation q 357 = true := counterClause757 (baseVal q)

theorem counterClause758 (q : Nat → Bool) : valuationOf q 357 = false ∨ valuationOf q 359 = true := by
  have hs : count359 q = (countLit q [183, 184]) + (countLit q [185, 186]) := List.countP_append (p := literal q) (l₁ := [183, 184]) (l₂ := [185, 186])
  have hm := merge_right (literal (valuationOf q) (357)) (literal (valuationOf q) (359)) (countLit q [183, 184]) (countLit q [185, 186]) (count359 q) 1 (meaning357 q) (meaning359 q) hs
  change valuationOf q 357 = false ∨ valuationOf q 359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause758 (q : Snake 81) (h : Conditions q) : valuation q 357 = false ∨ valuation q 359 = true := counterClause758 (baseVal q)

theorem counterClause759 (q : Nat → Bool) : valuationOf q 355 = false ∨ valuationOf q 359 = true := by
  have hs : count359 q = (countLit q [183, 184]) + (countLit q [185, 186]) := List.countP_append (p := literal q) (l₁ := [183, 184]) (l₂ := [185, 186])
  have hm := merge_left (literal (valuationOf q) (355)) (literal (valuationOf q) (359)) (countLit q [183, 184]) (countLit q [185, 186]) (count359 q) 1 (meaning355 q) (meaning359 q) hs
  change valuationOf q 355 = false ∨ valuationOf q 359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause759 (q : Snake 81) (h : Conditions q) : valuation q 355 = false ∨ valuation q 359 = true := counterClause759 (baseVal q)

theorem counterClause760 (q : Nat → Bool) : valuationOf q 359 = false ∨ valuationOf q 361 = true := by
  have hs : count361 q = (countLit q [179, 180, 181, 182]) + (countLit q [183, 184, 185, 186]) := List.countP_append (p := literal q) (l₁ := [179, 180, 181, 182]) (l₂ := [183, 184, 185, 186])
  have hm := merge_right (literal (valuationOf q) (359)) (literal (valuationOf q) (361)) (countLit q [179, 180, 181, 182]) (countLit q [183, 184, 185, 186]) (count361 q) 1 (meaning359 q) (meaning361 q) hs
  change valuationOf q 359 = false ∨ valuationOf q 361 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause760 (q : Snake 81) (h : Conditions q) : valuation q 359 = false ∨ valuation q 361 = true := counterClause760 (baseVal q)

theorem counterClause761 (q : Nat → Bool) : valuationOf q 361 = false ∨ valuationOf q 363 = true := by
  have hs : count363 q = (countLit q [171, 172, 173, 174, 175, 176, 177, 178]) + (countLit q [179, 180, 181, 182, 183, 184, 185, 186]) := List.countP_append (p := literal q) (l₁ := [171, 172, 173, 174, 175, 176, 177, 178]) (l₂ := [179, 180, 181, 182, 183, 184, 185, 186])
  have hm := merge_right (literal (valuationOf q) (361)) (literal (valuationOf q) (363)) (countLit q [171, 172, 173, 174, 175, 176, 177, 178]) (countLit q [179, 180, 181, 182, 183, 184, 185, 186]) (count363 q) 1 (meaning361 q) (meaning363 q) hs
  change valuationOf q 361 = false ∨ valuationOf q 363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause761 (q : Snake 81) (h : Conditions q) : valuation q 361 = false ∨ valuation q 363 = true := counterClause761 (baseVal q)

theorem counterClause762 (q : Nat → Bool) : valuationOf q 347 = false ∨ valuationOf q 363 = true := by
  have hs : count363 q = (countLit q [171, 172, 173, 174, 175, 176, 177, 178]) + (countLit q [179, 180, 181, 182, 183, 184, 185, 186]) := List.countP_append (p := literal q) (l₁ := [171, 172, 173, 174, 175, 176, 177, 178]) (l₂ := [179, 180, 181, 182, 183, 184, 185, 186])
  have hm := merge_left (literal (valuationOf q) (347)) (literal (valuationOf q) (363)) (countLit q [171, 172, 173, 174, 175, 176, 177, 178]) (countLit q [179, 180, 181, 182, 183, 184, 185, 186]) (count363 q) 1 (meaning347 q) (meaning363 q) hs
  change valuationOf q 347 = false ∨ valuationOf q 363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause762 (q : Snake 81) (h : Conditions q) : valuation q 347 = false ∨ valuation q 363 = true := counterClause762 (baseVal q)

theorem counterClause763 (q : Nat → Bool) : valuationOf q 363 = false ∨ valuationOf q 365 = true := by
  have hs : count365 q = (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) + (countLit q [171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) := List.countP_append (p := literal q) (l₁ := [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) (l₂ := [171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186])
  have hm := merge_right (literal (valuationOf q) (363)) (literal (valuationOf q) (365)) (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) (countLit q [171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) (count365 q) 1 (meaning363 q) (meaning365 q) hs
  change valuationOf q 363 = false ∨ valuationOf q 365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause763 (q : Snake 81) (h : Conditions q) : valuation q 363 = false ∨ valuation q 365 = true := counterClause763 (baseVal q)

theorem counterClause764 (q : Nat → Bool) : valuationOf q 333 = false ∨ valuationOf q 365 = true := by
  have hs : count365 q = (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) + (countLit q [171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) := List.countP_append (p := literal q) (l₁ := [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) (l₂ := [171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186])
  have hm := merge_left (literal (valuationOf q) (333)) (literal (valuationOf q) (365)) (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) (countLit q [171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) (count365 q) 1 (meaning333 q) (meaning365 q) hs
  change valuationOf q 333 = false ∨ valuationOf q 365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause764 (q : Snake 81) (h : Conditions q) : valuation q 333 = false ∨ valuation q 365 = true := counterClause764 (baseVal q)

theorem counterClause765 (q : Nat → Bool) : valuationOf q 333 = false ∨ valuationOf q 363 = false ∨ valuationOf q 366 = true := by
  have hs : count365 q = (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) + (countLit q [171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) := List.countP_append (p := literal q) (l₁ := [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) (l₂ := [171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186])
  have hm := merge_two (literal (valuationOf q) (333)) (literal (valuationOf q) (363)) (literal (valuationOf q) (366)) (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) (countLit q [171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) (count365 q) 1 1 (meaning333 q) (meaning363 q) (meaning366 q) hs
  change valuationOf q 333 = false ∨ valuationOf q 363 = false ∨ valuationOf q 366 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause765 (q : Snake 81) (h : Conditions q) : valuation q 333 = false ∨ valuation q 363 = false ∨ valuation q 366 = true := counterClause765 (baseVal q)

theorem counterClause766 (q : Nat → Bool) : valuationOf q 365 = false ∨ valuationOf q 367 = true := by
  have hs : count367 q = (countLit q [125, 126, 127, 128, 129, 130, 131, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) + (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 130, 131, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (l₂ := [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186])
  have hm := merge_right (literal (valuationOf q) (365)) (literal (valuationOf q) (367)) (countLit q [125, 126, 127, 128, 129, 130, 131, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) (count367 q) 1 (meaning365 q) (meaning367 q) hs
  change valuationOf q 365 = false ∨ valuationOf q 367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause766 (q : Snake 81) (h : Conditions q) : valuation q 365 = false ∨ valuation q 367 = true := counterClause766 (baseVal q)

theorem counterClause767 (q : Nat → Bool) : valuationOf q 366 = false ∨ valuationOf q 368 = true := by
  have hs : count367 q = (countLit q [125, 126, 127, 128, 129, 130, 131, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) + (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 130, 131, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (l₂ := [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186])
  have hm := merge_right (literal (valuationOf q) (366)) (literal (valuationOf q) (368)) (countLit q [125, 126, 127, 128, 129, 130, 131, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) (count367 q) 2 (meaning366 q) (meaning368 q) hs
  change valuationOf q 366 = false ∨ valuationOf q 368 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause767 (q : Snake 81) (h : Conditions q) : valuation q 366 = false ∨ valuation q 368 = true := counterClause767 (baseVal q)

theorem counterClause768 (q : Nat → Bool) : valuationOf q 305 = false ∨ valuationOf q 367 = true := by
  have hs : count367 q = (countLit q [125, 126, 127, 128, 129, 130, 131, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) + (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 130, 131, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (l₂ := [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186])
  have hm := merge_left (literal (valuationOf q) (305)) (literal (valuationOf q) (367)) (countLit q [125, 126, 127, 128, 129, 130, 131, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) (count367 q) 1 (meaning305 q) (meaning367 q) hs
  change valuationOf q 305 = false ∨ valuationOf q 367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause768 (q : Snake 81) (h : Conditions q) : valuation q 305 = false ∨ valuation q 367 = true := counterClause768 (baseVal q)

theorem block23 (q : Snake 81) (h : Conditions q) : B112E153.Block23 (valuation q) :=
  ⟨clause737 q h, clause738 q h, clause739 q h, clause740 q h, clause741 q h, clause742 q h, clause743 q h, clause744 q h, clause745 q h, clause746 q h, clause747 q h, clause748 q h, clause749 q h, clause750 q h, clause751 q h, clause752 q h, clause753 q h, clause754 q h, clause755 q h, clause756 q h, clause757 q h, clause758 q h, clause759 q h, clause760 q h, clause761 q h, clause762 q h, clause763 q h, clause764 q h, clause765 q h, clause766 q h, clause767 q h, clause768 q h⟩

end
end Snake9.Regrowth.E112153
