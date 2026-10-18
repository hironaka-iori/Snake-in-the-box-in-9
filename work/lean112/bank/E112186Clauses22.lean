import E112186Semantics
import B112E186Inputs
namespace Snake9.Regrowth.E112186
noncomputable section
local instance blockDec22 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause705 (q : Snake 81) (h : Conditions q) : valuation q 238 = false := by
  rw [value238]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (460 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause706 (q : Snake 81) (h : Conditions q) : valuation q 241 = false := by
  rw [value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (468 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause707 (q : Snake 81) (h : Conditions q) : valuation q 243 = false := by
  rw [value243]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (471 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause708 (q : Snake 81) (h : Conditions q) : valuation q 246 = false := by
  rw [value246]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (475 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem counterClause709 (q : Nat → Bool) : valuationOf q 131 = false ∨ valuationOf q 255 = true := by
  have hs : count255 q = (countLit q [131]) + (countLit q [132]) := List.countP_append (p := literal q) (l₁ := [131]) (l₂ := [132])
  have hm := merge_left (literal (valuationOf q) (131)) (literal (valuationOf q) (255)) (countLit q [131]) (countLit q [132]) (count255 q) 1 (meaning131 q) (meaning255 q) hs
  change valuationOf q 131 = false ∨ valuationOf q 255 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause709 (q : Snake 81) (h : Conditions q) : valuation q 131 = false ∨ valuation q 255 = true := counterClause709 (baseVal q)

theorem counterClause710 (q : Nat → Bool) : valuationOf q 255 = false ∨ valuationOf q 257 = true := by
  have hs : count257 q = (countLit q [128, 129]) + (countLit q [131, 132]) := List.countP_append (p := literal q) (l₁ := [128, 129]) (l₂ := [131, 132])
  have hm := merge_right (literal (valuationOf q) (255)) (literal (valuationOf q) (257)) (countLit q [128, 129]) (countLit q [131, 132]) (count257 q) 1 (meaning255 q) (meaning257 q) hs
  change valuationOf q 255 = false ∨ valuationOf q 257 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause710 (q : Snake 81) (h : Conditions q) : valuation q 255 = false ∨ valuation q 257 = true := counterClause710 (baseVal q)

theorem counterClause711 (q : Nat → Bool) : valuationOf q 257 = false ∨ valuationOf q 259 = true := by
  have hs : count259 q = (countLit q [125, 126, 127]) + (countLit q [128, 129, 131, 132]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127]) (l₂ := [128, 129, 131, 132])
  have hm := merge_right (literal (valuationOf q) (257)) (literal (valuationOf q) (259)) (countLit q [125, 126, 127]) (countLit q [128, 129, 131, 132]) (count259 q) 1 (meaning257 q) (meaning259 q) hs
  change valuationOf q 257 = false ∨ valuationOf q 259 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause711 (q : Snake 81) (h : Conditions q) : valuation q 257 = false ∨ valuation q 259 = true := counterClause711 (baseVal q)

theorem counterClause712 (q : Nat → Bool) : valuationOf q 133 = false ∨ valuationOf q 261 = true := by
  have hs : count261 q = (countLit q [133]) + (countLit q [134]) := List.countP_append (p := literal q) (l₁ := [133]) (l₂ := [134])
  have hm := merge_left (literal (valuationOf q) (133)) (literal (valuationOf q) (261)) (countLit q [133]) (countLit q [134]) (count261 q) 1 (meaning133 q) (meaning261 q) hs
  change valuationOf q 133 = false ∨ valuationOf q 261 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause712 (q : Snake 81) (h : Conditions q) : valuation q 133 = false ∨ valuation q 261 = true := counterClause712 (baseVal q)

theorem counterClause713 (q : Nat → Bool) : valuationOf q 136 = false ∨ valuationOf q 263 = true := by
  have hs : count263 q = (countLit q [135]) + (countLit q [136]) := List.countP_append (p := literal q) (l₁ := [135]) (l₂ := [136])
  have hm := merge_right (literal (valuationOf q) (136)) (literal (valuationOf q) (263)) (countLit q [135]) (countLit q [136]) (count263 q) 1 (meaning136 q) (meaning263 q) hs
  change valuationOf q 136 = false ∨ valuationOf q 263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause713 (q : Snake 81) (h : Conditions q) : valuation q 136 = false ∨ valuation q 263 = true := counterClause713 (baseVal q)

theorem counterClause714 (q : Nat → Bool) : valuationOf q 135 = false ∨ valuationOf q 263 = true := by
  have hs : count263 q = (countLit q [135]) + (countLit q [136]) := List.countP_append (p := literal q) (l₁ := [135]) (l₂ := [136])
  have hm := merge_left (literal (valuationOf q) (135)) (literal (valuationOf q) (263)) (countLit q [135]) (countLit q [136]) (count263 q) 1 (meaning135 q) (meaning263 q) hs
  change valuationOf q 135 = false ∨ valuationOf q 263 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause714 (q : Snake 81) (h : Conditions q) : valuation q 135 = false ∨ valuation q 263 = true := counterClause714 (baseVal q)

theorem counterClause715 (q : Nat → Bool) : valuationOf q 263 = false ∨ valuationOf q 265 = true := by
  have hs : count265 q = (countLit q [133, 134]) + (countLit q [135, 136]) := List.countP_append (p := literal q) (l₁ := [133, 134]) (l₂ := [135, 136])
  have hm := merge_right (literal (valuationOf q) (263)) (literal (valuationOf q) (265)) (countLit q [133, 134]) (countLit q [135, 136]) (count265 q) 1 (meaning263 q) (meaning265 q) hs
  change valuationOf q 263 = false ∨ valuationOf q 265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause715 (q : Snake 81) (h : Conditions q) : valuation q 263 = false ∨ valuation q 265 = true := counterClause715 (baseVal q)

theorem counterClause716 (q : Nat → Bool) : valuationOf q 261 = false ∨ valuationOf q 265 = true := by
  have hs : count265 q = (countLit q [133, 134]) + (countLit q [135, 136]) := List.countP_append (p := literal q) (l₁ := [133, 134]) (l₂ := [135, 136])
  have hm := merge_left (literal (valuationOf q) (261)) (literal (valuationOf q) (265)) (countLit q [133, 134]) (countLit q [135, 136]) (count265 q) 1 (meaning261 q) (meaning265 q) hs
  change valuationOf q 261 = false ∨ valuationOf q 265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause716 (q : Snake 81) (h : Conditions q) : valuation q 261 = false ∨ valuation q 265 = true := counterClause716 (baseVal q)

theorem counterClause717 (q : Nat → Bool) : valuationOf q 138 = false ∨ valuationOf q 267 = true := by
  have hs : count267 q = (countLit q [137]) + (countLit q [138]) := List.countP_append (p := literal q) (l₁ := [137]) (l₂ := [138])
  have hm := merge_right (literal (valuationOf q) (138)) (literal (valuationOf q) (267)) (countLit q [137]) (countLit q [138]) (count267 q) 1 (meaning138 q) (meaning267 q) hs
  change valuationOf q 138 = false ∨ valuationOf q 267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause717 (q : Snake 81) (h : Conditions q) : valuation q 138 = false ∨ valuation q 267 = true := counterClause717 (baseVal q)

theorem counterClause718 (q : Nat → Bool) : valuationOf q 267 = false ∨ valuationOf q 271 = true := by
  have hs : count271 q = (countLit q [137, 138]) + (countLit q [139, 140]) := List.countP_append (p := literal q) (l₁ := [137, 138]) (l₂ := [139, 140])
  have hm := merge_left (literal (valuationOf q) (267)) (literal (valuationOf q) (271)) (countLit q [137, 138]) (countLit q [139, 140]) (count271 q) 1 (meaning267 q) (meaning271 q) hs
  change valuationOf q 267 = false ∨ valuationOf q 271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause718 (q : Snake 81) (h : Conditions q) : valuation q 267 = false ∨ valuation q 271 = true := counterClause718 (baseVal q)

theorem counterClause719 (q : Nat → Bool) : valuationOf q 271 = false ∨ valuationOf q 273 = true := by
  have hs : count273 q = (countLit q [133, 134, 135, 136]) + (countLit q [137, 138, 139, 140]) := List.countP_append (p := literal q) (l₁ := [133, 134, 135, 136]) (l₂ := [137, 138, 139, 140])
  have hm := merge_right (literal (valuationOf q) (271)) (literal (valuationOf q) (273)) (countLit q [133, 134, 135, 136]) (countLit q [137, 138, 139, 140]) (count273 q) 1 (meaning271 q) (meaning273 q) hs
  change valuationOf q 271 = false ∨ valuationOf q 273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause719 (q : Snake 81) (h : Conditions q) : valuation q 271 = false ∨ valuation q 273 = true := counterClause719 (baseVal q)

theorem counterClause720 (q : Nat → Bool) : valuationOf q 265 = false ∨ valuationOf q 273 = true := by
  have hs : count273 q = (countLit q [133, 134, 135, 136]) + (countLit q [137, 138, 139, 140]) := List.countP_append (p := literal q) (l₁ := [133, 134, 135, 136]) (l₂ := [137, 138, 139, 140])
  have hm := merge_left (literal (valuationOf q) (265)) (literal (valuationOf q) (273)) (countLit q [133, 134, 135, 136]) (countLit q [137, 138, 139, 140]) (count273 q) 1 (meaning265 q) (meaning273 q) hs
  change valuationOf q 265 = false ∨ valuationOf q 273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause720 (q : Snake 81) (h : Conditions q) : valuation q 265 = false ∨ valuation q 273 = true := counterClause720 (baseVal q)

theorem counterClause721 (q : Nat → Bool) : valuationOf q 273 = false ∨ valuationOf q 275 = true := by
  have hs : count275 q = (countLit q [125, 126, 127, 128, 129, 131, 132]) + (countLit q [133, 134, 135, 136, 137, 138, 139, 140]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 131, 132]) (l₂ := [133, 134, 135, 136, 137, 138, 139, 140])
  have hm := merge_right (literal (valuationOf q) (273)) (literal (valuationOf q) (275)) (countLit q [125, 126, 127, 128, 129, 131, 132]) (countLit q [133, 134, 135, 136, 137, 138, 139, 140]) (count275 q) 1 (meaning273 q) (meaning275 q) hs
  change valuationOf q 273 = false ∨ valuationOf q 275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause721 (q : Snake 81) (h : Conditions q) : valuation q 273 = false ∨ valuation q 275 = true := counterClause721 (baseVal q)

theorem counterClause722 (q : Nat → Bool) : valuationOf q 259 = false ∨ valuationOf q 275 = true := by
  have hs : count275 q = (countLit q [125, 126, 127, 128, 129, 131, 132]) + (countLit q [133, 134, 135, 136, 137, 138, 139, 140]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 131, 132]) (l₂ := [133, 134, 135, 136, 137, 138, 139, 140])
  have hm := merge_left (literal (valuationOf q) (259)) (literal (valuationOf q) (275)) (countLit q [125, 126, 127, 128, 129, 131, 132]) (countLit q [133, 134, 135, 136, 137, 138, 139, 140]) (count275 q) 1 (meaning259 q) (meaning275 q) hs
  change valuationOf q 259 = false ∨ valuationOf q 275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause722 (q : Snake 81) (h : Conditions q) : valuation q 259 = false ∨ valuation q 275 = true := counterClause722 (baseVal q)

theorem counterClause723 (q : Nat → Bool) : valuationOf q 145 = false ∨ valuationOf q 281 = true := by
  have hs : count281 q = (countLit q [144]) + (countLit q [145]) := List.countP_append (p := literal q) (l₁ := [144]) (l₂ := [145])
  have hm := merge_right (literal (valuationOf q) (145)) (literal (valuationOf q) (281)) (countLit q [144]) (countLit q [145]) (count281 q) 1 (meaning145 q) (meaning281 q) hs
  change valuationOf q 145 = false ∨ valuationOf q 281 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause723 (q : Snake 81) (h : Conditions q) : valuation q 145 = false ∨ valuation q 281 = true := counterClause723 (baseVal q)

theorem counterClause724 (q : Nat → Bool) : valuationOf q 144 = false ∨ valuationOf q 281 = true := by
  have hs : count281 q = (countLit q [144]) + (countLit q [145]) := List.countP_append (p := literal q) (l₁ := [144]) (l₂ := [145])
  have hm := merge_left (literal (valuationOf q) (144)) (literal (valuationOf q) (281)) (countLit q [144]) (countLit q [145]) (count281 q) 1 (meaning144 q) (meaning281 q) hs
  change valuationOf q 144 = false ∨ valuationOf q 281 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause724 (q : Snake 81) (h : Conditions q) : valuation q 144 = false ∨ valuation q 281 = true := counterClause724 (baseVal q)

theorem counterClause725 (q : Nat → Bool) : valuationOf q 281 = false ∨ valuationOf q 285 = true := by
  have hs : count285 q = (countLit q [144, 145]) + (countLit q [146, 147]) := List.countP_append (p := literal q) (l₁ := [144, 145]) (l₂ := [146, 147])
  have hm := merge_left (literal (valuationOf q) (281)) (literal (valuationOf q) (285)) (countLit q [144, 145]) (countLit q [146, 147]) (count285 q) 1 (meaning281 q) (meaning285 q) hs
  change valuationOf q 281 = false ∨ valuationOf q 285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause725 (q : Snake 81) (h : Conditions q) : valuation q 281 = false ∨ valuation q 285 = true := counterClause725 (baseVal q)

theorem counterClause726 (q : Nat → Bool) : valuationOf q 285 = false ∨ valuationOf q 287 = true := by
  have hs : count287 q = (countLit q [141, 142, 143]) + (countLit q [144, 145, 146, 147]) := List.countP_append (p := literal q) (l₁ := [141, 142, 143]) (l₂ := [144, 145, 146, 147])
  have hm := merge_right (literal (valuationOf q) (285)) (literal (valuationOf q) (287)) (countLit q [141, 142, 143]) (countLit q [144, 145, 146, 147]) (count287 q) 1 (meaning285 q) (meaning287 q) hs
  change valuationOf q 285 = false ∨ valuationOf q 287 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause726 (q : Snake 81) (h : Conditions q) : valuation q 285 = false ∨ valuation q 287 = true := counterClause726 (baseVal q)

theorem counterClause727 (q : Nat → Bool) : valuationOf q 151 = false ∨ valuationOf q 291 = true := by
  have hs : count291 q = (countLit q [150]) + (countLit q [151]) := List.countP_append (p := literal q) (l₁ := [150]) (l₂ := [151])
  have hm := merge_right (literal (valuationOf q) (151)) (literal (valuationOf q) (291)) (countLit q [150]) (countLit q [151]) (count291 q) 1 (meaning151 q) (meaning291 q) hs
  change valuationOf q 151 = false ∨ valuationOf q 291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause727 (q : Snake 81) (h : Conditions q) : valuation q 151 = false ∨ valuation q 291 = true := counterClause727 (baseVal q)

theorem counterClause728 (q : Nat → Bool) : valuationOf q 291 = false ∨ valuationOf q 293 = true := by
  have hs : count293 q = (countLit q [148, 149]) + (countLit q [150, 151]) := List.countP_append (p := literal q) (l₁ := [148, 149]) (l₂ := [150, 151])
  have hm := merge_right (literal (valuationOf q) (291)) (literal (valuationOf q) (293)) (countLit q [148, 149]) (countLit q [150, 151]) (count293 q) 1 (meaning291 q) (meaning293 q) hs
  change valuationOf q 291 = false ∨ valuationOf q 293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause728 (q : Snake 81) (h : Conditions q) : valuation q 291 = false ∨ valuation q 293 = true := counterClause728 (baseVal q)

theorem counterClause729 (q : Nat → Bool) : valuationOf q 153 = false ∨ valuationOf q 295 = true := by
  have hs : count295 q = (countLit q [152]) + (countLit q [153]) := List.countP_append (p := literal q) (l₁ := [152]) (l₂ := [153])
  have hm := merge_right (literal (valuationOf q) (153)) (literal (valuationOf q) (295)) (countLit q [152]) (countLit q [153]) (count295 q) 1 (meaning153 q) (meaning295 q) hs
  change valuationOf q 153 = false ∨ valuationOf q 295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause729 (q : Snake 81) (h : Conditions q) : valuation q 153 = false ∨ valuation q 295 = true := counterClause729 (baseVal q)

theorem counterClause730 (q : Nat → Bool) : valuationOf q 295 = false ∨ valuationOf q 299 = true := by
  have hs : count299 q = (countLit q [152, 153]) + (countLit q [154, 155]) := List.countP_append (p := literal q) (l₁ := [152, 153]) (l₂ := [154, 155])
  have hm := merge_left (literal (valuationOf q) (295)) (literal (valuationOf q) (299)) (countLit q [152, 153]) (countLit q [154, 155]) (count299 q) 1 (meaning295 q) (meaning299 q) hs
  change valuationOf q 295 = false ∨ valuationOf q 299 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause730 (q : Snake 81) (h : Conditions q) : valuation q 295 = false ∨ valuation q 299 = true := counterClause730 (baseVal q)

theorem counterClause731 (q : Nat → Bool) : valuationOf q 299 = false ∨ valuationOf q 301 = true := by
  have hs : count301 q = (countLit q [148, 149, 150, 151]) + (countLit q [152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [148, 149, 150, 151]) (l₂ := [152, 153, 154, 155])
  have hm := merge_right (literal (valuationOf q) (299)) (literal (valuationOf q) (301)) (countLit q [148, 149, 150, 151]) (countLit q [152, 153, 154, 155]) (count301 q) 1 (meaning299 q) (meaning301 q) hs
  change valuationOf q 299 = false ∨ valuationOf q 301 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause731 (q : Snake 81) (h : Conditions q) : valuation q 299 = false ∨ valuation q 301 = true := counterClause731 (baseVal q)

theorem counterClause732 (q : Nat → Bool) : valuationOf q 293 = false ∨ valuationOf q 301 = true := by
  have hs : count301 q = (countLit q [148, 149, 150, 151]) + (countLit q [152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [148, 149, 150, 151]) (l₂ := [152, 153, 154, 155])
  have hm := merge_left (literal (valuationOf q) (293)) (literal (valuationOf q) (301)) (countLit q [148, 149, 150, 151]) (countLit q [152, 153, 154, 155]) (count301 q) 1 (meaning293 q) (meaning301 q) hs
  change valuationOf q 293 = false ∨ valuationOf q 301 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause732 (q : Snake 81) (h : Conditions q) : valuation q 293 = false ∨ valuation q 301 = true := counterClause732 (baseVal q)

theorem counterClause733 (q : Nat → Bool) : valuationOf q 293 = false ∨ valuationOf q 299 = false ∨ valuationOf q 302 = true := by
  have hs : count301 q = (countLit q [148, 149, 150, 151]) + (countLit q [152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [148, 149, 150, 151]) (l₂ := [152, 153, 154, 155])
  have hm := merge_two (literal (valuationOf q) (293)) (literal (valuationOf q) (299)) (literal (valuationOf q) (302)) (countLit q [148, 149, 150, 151]) (countLit q [152, 153, 154, 155]) (count301 q) 1 1 (meaning293 q) (meaning299 q) (meaning302 q) hs
  change valuationOf q 293 = false ∨ valuationOf q 299 = false ∨ valuationOf q 302 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause733 (q : Snake 81) (h : Conditions q) : valuation q 293 = false ∨ valuation q 299 = false ∨ valuation q 302 = true := counterClause733 (baseVal q)

theorem counterClause734 (q : Nat → Bool) : valuationOf q 301 = false ∨ valuationOf q 303 = true := by
  have hs : count303 q = (countLit q [141, 142, 143, 144, 145, 146, 147]) + (countLit q [148, 149, 150, 151, 152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [141, 142, 143, 144, 145, 146, 147]) (l₂ := [148, 149, 150, 151, 152, 153, 154, 155])
  have hm := merge_right (literal (valuationOf q) (301)) (literal (valuationOf q) (303)) (countLit q [141, 142, 143, 144, 145, 146, 147]) (countLit q [148, 149, 150, 151, 152, 153, 154, 155]) (count303 q) 1 (meaning301 q) (meaning303 q) hs
  change valuationOf q 301 = false ∨ valuationOf q 303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause734 (q : Snake 81) (h : Conditions q) : valuation q 301 = false ∨ valuation q 303 = true := counterClause734 (baseVal q)

theorem counterClause735 (q : Nat → Bool) : valuationOf q 302 = false ∨ valuationOf q 304 = true := by
  have hs : count303 q = (countLit q [141, 142, 143, 144, 145, 146, 147]) + (countLit q [148, 149, 150, 151, 152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [141, 142, 143, 144, 145, 146, 147]) (l₂ := [148, 149, 150, 151, 152, 153, 154, 155])
  have hm := merge_right (literal (valuationOf q) (302)) (literal (valuationOf q) (304)) (countLit q [141, 142, 143, 144, 145, 146, 147]) (countLit q [148, 149, 150, 151, 152, 153, 154, 155]) (count303 q) 2 (meaning302 q) (meaning304 q) hs
  change valuationOf q 302 = false ∨ valuationOf q 304 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause735 (q : Snake 81) (h : Conditions q) : valuation q 302 = false ∨ valuation q 304 = true := counterClause735 (baseVal q)

theorem counterClause736 (q : Nat → Bool) : valuationOf q 287 = false ∨ valuationOf q 303 = true := by
  have hs : count303 q = (countLit q [141, 142, 143, 144, 145, 146, 147]) + (countLit q [148, 149, 150, 151, 152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [141, 142, 143, 144, 145, 146, 147]) (l₂ := [148, 149, 150, 151, 152, 153, 154, 155])
  have hm := merge_left (literal (valuationOf q) (287)) (literal (valuationOf q) (303)) (countLit q [141, 142, 143, 144, 145, 146, 147]) (countLit q [148, 149, 150, 151, 152, 153, 154, 155]) (count303 q) 1 (meaning287 q) (meaning303 q) hs
  change valuationOf q 287 = false ∨ valuationOf q 303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause736 (q : Snake 81) (h : Conditions q) : valuation q 287 = false ∨ valuation q 303 = true := counterClause736 (baseVal q)

theorem block22 (q : Snake 81) (h : Conditions q) : B112E186.Block22 (valuation q) :=
  ⟨clause705 q h, clause706 q h, clause707 q h, clause708 q h, clause709 q h, clause710 q h, clause711 q h, clause712 q h, clause713 q h, clause714 q h, clause715 q h, clause716 q h, clause717 q h, clause718 q h, clause719 q h, clause720 q h, clause721 q h, clause722 q h, clause723 q h, clause724 q h, clause725 q h, clause726 q h, clause727 q h, clause728 q h, clause729 q h, clause730 q h, clause731 q h, clause732 q h, clause733 q h, clause734 q h, clause735 q h, clause736 q h⟩

end
end Snake9.Regrowth.E112186
