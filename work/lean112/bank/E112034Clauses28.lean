import E112034Semantics
import B112E034Inputs
namespace Snake9.Regrowth.E112034
noncomputable section
local instance blockDec28 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause897 (q : Snake 81) (h : Conditions q) : valuation q 249 = false := by
  rw [value249]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (501 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause898 (q : Snake 81) (h : Conditions q) : valuation q 250 = false := by
  rw [value250]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (502 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause899 (q : Snake 81) (h : Conditions q) : valuation q 253 = false := by
  rw [value253]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (505 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause900 (q : Snake 81) (h : Conditions q) : valuation q 254 = false := by
  rw [value254]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (506 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem counterClause901 (q : Nat → Bool) : valuationOf q 133 = false ∨ valuationOf q 261 = true := by
  have hs : count261 q = (countLit q [132]) + (countLit q [133]) := List.countP_append (p := literal q) (l₁ := [132]) (l₂ := [133])
  have hm := merge_right (literal (valuationOf q) (133)) (literal (valuationOf q) (261)) (countLit q [132]) (countLit q [133]) (count261 q) 1 (meaning133 q) (meaning261 q) hs
  change valuationOf q 133 = false ∨ valuationOf q 261 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause901 (q : Snake 81) (h : Conditions q) : valuation q 133 = false ∨ valuation q 261 = true := counterClause901 (baseVal q)

theorem counterClause902 (q : Nat → Bool) : valuationOf q 261 = false ∨ valuationOf q 265 = true := by
  have hs : count265 q = (countLit q [132, 133]) + (countLit q [134, 135]) := List.countP_append (p := literal q) (l₁ := [132, 133]) (l₂ := [134, 135])
  have hm := merge_left (literal (valuationOf q) (261)) (literal (valuationOf q) (265)) (countLit q [132, 133]) (countLit q [134, 135]) (count265 q) 1 (meaning261 q) (meaning265 q) hs
  change valuationOf q 261 = false ∨ valuationOf q 265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause902 (q : Snake 81) (h : Conditions q) : valuation q 261 = false ∨ valuation q 265 = true := counterClause902 (baseVal q)

theorem counterClause903 (q : Nat → Bool) : valuationOf q 265 = false ∨ valuationOf q 267 = true := by
  have hs : count267 q = (countLit q [129, 130, 131]) + (countLit q [132, 133, 134, 135]) := List.countP_append (p := literal q) (l₁ := [129, 130, 131]) (l₂ := [132, 133, 134, 135])
  have hm := merge_right (literal (valuationOf q) (265)) (literal (valuationOf q) (267)) (countLit q [129, 130, 131]) (countLit q [132, 133, 134, 135]) (count267 q) 1 (meaning265 q) (meaning267 q) hs
  change valuationOf q 265 = false ∨ valuationOf q 267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause903 (q : Snake 81) (h : Conditions q) : valuation q 265 = false ∨ valuation q 267 = true := counterClause903 (baseVal q)

theorem counterClause904 (q : Nat → Bool) : valuationOf q 138 = false ∨ valuationOf q 271 = true := by
  have hs : count271 q = (countLit q [138]) + (countLit q [139]) := List.countP_append (p := literal q) (l₁ := [138]) (l₂ := [139])
  have hm := merge_left (literal (valuationOf q) (138)) (literal (valuationOf q) (271)) (countLit q [138]) (countLit q [139]) (count271 q) 1 (meaning138 q) (meaning271 q) hs
  change valuationOf q 138 = false ∨ valuationOf q 271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause904 (q : Snake 81) (h : Conditions q) : valuation q 138 = false ∨ valuation q 271 = true := counterClause904 (baseVal q)

theorem counterClause905 (q : Nat → Bool) : valuationOf q 271 = false ∨ valuationOf q 273 = true := by
  have hs : count273 q = (countLit q [136, 137]) + (countLit q [138, 139]) := List.countP_append (p := literal q) (l₁ := [136, 137]) (l₂ := [138, 139])
  have hm := merge_right (literal (valuationOf q) (271)) (literal (valuationOf q) (273)) (countLit q [136, 137]) (countLit q [138, 139]) (count273 q) 1 (meaning271 q) (meaning273 q) hs
  change valuationOf q 271 = false ∨ valuationOf q 273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause905 (q : Snake 81) (h : Conditions q) : valuation q 271 = false ∨ valuation q 273 = true := counterClause905 (baseVal q)

theorem counterClause906 (q : Nat → Bool) : valuationOf q 142 = false ∨ valuationOf q 275 = true := by
  have hs : count275 q = (countLit q [140]) + (countLit q [142]) := List.countP_append (p := literal q) (l₁ := [140]) (l₂ := [142])
  have hm := merge_right (literal (valuationOf q) (142)) (literal (valuationOf q) (275)) (countLit q [140]) (countLit q [142]) (count275 q) 1 (meaning142 q) (meaning275 q) hs
  change valuationOf q 142 = false ∨ valuationOf q 275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause906 (q : Snake 81) (h : Conditions q) : valuation q 142 = false ∨ valuation q 275 = true := counterClause906 (baseVal q)

theorem counterClause907 (q : Nat → Bool) : valuationOf q 140 = false ∨ valuationOf q 275 = true := by
  have hs : count275 q = (countLit q [140]) + (countLit q [142]) := List.countP_append (p := literal q) (l₁ := [140]) (l₂ := [142])
  have hm := merge_left (literal (valuationOf q) (140)) (literal (valuationOf q) (275)) (countLit q [140]) (countLit q [142]) (count275 q) 1 (meaning140 q) (meaning275 q) hs
  change valuationOf q 140 = false ∨ valuationOf q 275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause907 (q : Snake 81) (h : Conditions q) : valuation q 140 = false ∨ valuation q 275 = true := counterClause907 (baseVal q)

theorem counterClause908 (q : Nat → Bool) : valuationOf q 275 = false ∨ valuationOf q 279 = true := by
  have hs : count279 q = (countLit q [140, 142]) + (countLit q [143, 144]) := List.countP_append (p := literal q) (l₁ := [140, 142]) (l₂ := [143, 144])
  have hm := merge_left (literal (valuationOf q) (275)) (literal (valuationOf q) (279)) (countLit q [140, 142]) (countLit q [143, 144]) (count279 q) 1 (meaning275 q) (meaning279 q) hs
  change valuationOf q 275 = false ∨ valuationOf q 279 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause908 (q : Snake 81) (h : Conditions q) : valuation q 275 = false ∨ valuation q 279 = true := counterClause908 (baseVal q)

theorem counterClause909 (q : Nat → Bool) : valuationOf q 279 = false ∨ valuationOf q 281 = true := by
  have hs : count281 q = (countLit q [136, 137, 138, 139]) + (countLit q [140, 142, 143, 144]) := List.countP_append (p := literal q) (l₁ := [136, 137, 138, 139]) (l₂ := [140, 142, 143, 144])
  have hm := merge_right (literal (valuationOf q) (279)) (literal (valuationOf q) (281)) (countLit q [136, 137, 138, 139]) (countLit q [140, 142, 143, 144]) (count281 q) 1 (meaning279 q) (meaning281 q) hs
  change valuationOf q 279 = false ∨ valuationOf q 281 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause909 (q : Snake 81) (h : Conditions q) : valuation q 279 = false ∨ valuation q 281 = true := counterClause909 (baseVal q)

theorem counterClause910 (q : Nat → Bool) : valuationOf q 273 = false ∨ valuationOf q 281 = true := by
  have hs : count281 q = (countLit q [136, 137, 138, 139]) + (countLit q [140, 142, 143, 144]) := List.countP_append (p := literal q) (l₁ := [136, 137, 138, 139]) (l₂ := [140, 142, 143, 144])
  have hm := merge_left (literal (valuationOf q) (273)) (literal (valuationOf q) (281)) (countLit q [136, 137, 138, 139]) (countLit q [140, 142, 143, 144]) (count281 q) 1 (meaning273 q) (meaning281 q) hs
  change valuationOf q 273 = false ∨ valuationOf q 281 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause910 (q : Snake 81) (h : Conditions q) : valuation q 273 = false ∨ valuation q 281 = true := counterClause910 (baseVal q)

theorem counterClause911 (q : Nat → Bool) : valuationOf q 273 = false ∨ valuationOf q 279 = false ∨ valuationOf q 282 = true := by
  have hs : count281 q = (countLit q [136, 137, 138, 139]) + (countLit q [140, 142, 143, 144]) := List.countP_append (p := literal q) (l₁ := [136, 137, 138, 139]) (l₂ := [140, 142, 143, 144])
  have hm := merge_two (literal (valuationOf q) (273)) (literal (valuationOf q) (279)) (literal (valuationOf q) (282)) (countLit q [136, 137, 138, 139]) (countLit q [140, 142, 143, 144]) (count281 q) 1 1 (meaning273 q) (meaning279 q) (meaning282 q) hs
  change valuationOf q 273 = false ∨ valuationOf q 279 = false ∨ valuationOf q 282 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause911 (q : Snake 81) (h : Conditions q) : valuation q 273 = false ∨ valuation q 279 = false ∨ valuation q 282 = true := counterClause911 (baseVal q)

theorem counterClause912 (q : Nat → Bool) : valuationOf q 281 = false ∨ valuationOf q 283 = true := by
  have hs : count283 q = (countLit q [129, 130, 131, 132, 133, 134, 135]) + (countLit q [136, 137, 138, 139, 140, 142, 143, 144]) := List.countP_append (p := literal q) (l₁ := [129, 130, 131, 132, 133, 134, 135]) (l₂ := [136, 137, 138, 139, 140, 142, 143, 144])
  have hm := merge_right (literal (valuationOf q) (281)) (literal (valuationOf q) (283)) (countLit q [129, 130, 131, 132, 133, 134, 135]) (countLit q [136, 137, 138, 139, 140, 142, 143, 144]) (count283 q) 1 (meaning281 q) (meaning283 q) hs
  change valuationOf q 281 = false ∨ valuationOf q 283 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause912 (q : Snake 81) (h : Conditions q) : valuation q 281 = false ∨ valuation q 283 = true := counterClause912 (baseVal q)

theorem counterClause913 (q : Nat → Bool) : valuationOf q 282 = false ∨ valuationOf q 284 = true := by
  have hs : count283 q = (countLit q [129, 130, 131, 132, 133, 134, 135]) + (countLit q [136, 137, 138, 139, 140, 142, 143, 144]) := List.countP_append (p := literal q) (l₁ := [129, 130, 131, 132, 133, 134, 135]) (l₂ := [136, 137, 138, 139, 140, 142, 143, 144])
  have hm := merge_right (literal (valuationOf q) (282)) (literal (valuationOf q) (284)) (countLit q [129, 130, 131, 132, 133, 134, 135]) (countLit q [136, 137, 138, 139, 140, 142, 143, 144]) (count283 q) 2 (meaning282 q) (meaning284 q) hs
  change valuationOf q 282 = false ∨ valuationOf q 284 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause913 (q : Snake 81) (h : Conditions q) : valuation q 282 = false ∨ valuation q 284 = true := counterClause913 (baseVal q)

theorem counterClause914 (q : Nat → Bool) : valuationOf q 267 = false ∨ valuationOf q 283 = true := by
  have hs : count283 q = (countLit q [129, 130, 131, 132, 133, 134, 135]) + (countLit q [136, 137, 138, 139, 140, 142, 143, 144]) := List.countP_append (p := literal q) (l₁ := [129, 130, 131, 132, 133, 134, 135]) (l₂ := [136, 137, 138, 139, 140, 142, 143, 144])
  have hm := merge_left (literal (valuationOf q) (267)) (literal (valuationOf q) (283)) (countLit q [129, 130, 131, 132, 133, 134, 135]) (countLit q [136, 137, 138, 139, 140, 142, 143, 144]) (count283 q) 1 (meaning267 q) (meaning283 q) hs
  change valuationOf q 267 = false ∨ valuationOf q 283 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause914 (q : Snake 81) (h : Conditions q) : valuation q 267 = false ∨ valuation q 283 = true := counterClause914 (baseVal q)

theorem counterClause915 (q : Nat → Bool) : valuationOf q 145 = false ∨ valuationOf q 285 = true := by
  have hs : count285 q = (countLit q [145]) + (countLit q [146]) := List.countP_append (p := literal q) (l₁ := [145]) (l₂ := [146])
  have hm := merge_left (literal (valuationOf q) (145)) (literal (valuationOf q) (285)) (countLit q [145]) (countLit q [146]) (count285 q) 1 (meaning145 q) (meaning285 q) hs
  change valuationOf q 145 = false ∨ valuationOf q 285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause915 (q : Snake 81) (h : Conditions q) : valuation q 145 = false ∨ valuation q 285 = true := counterClause915 (baseVal q)

theorem counterClause916 (q : Nat → Bool) : valuationOf q 148 = false ∨ valuationOf q 287 = true := by
  have hs : count287 q = (countLit q [147]) + (countLit q [148]) := List.countP_append (p := literal q) (l₁ := [147]) (l₂ := [148])
  have hm := merge_right (literal (valuationOf q) (148)) (literal (valuationOf q) (287)) (countLit q [147]) (countLit q [148]) (count287 q) 1 (meaning148 q) (meaning287 q) hs
  change valuationOf q 148 = false ∨ valuationOf q 287 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause916 (q : Snake 81) (h : Conditions q) : valuation q 148 = false ∨ valuation q 287 = true := counterClause916 (baseVal q)

theorem counterClause917 (q : Nat → Bool) : valuationOf q 287 = false ∨ valuationOf q 289 = true := by
  have hs : count289 q = (countLit q [145, 146]) + (countLit q [147, 148]) := List.countP_append (p := literal q) (l₁ := [145, 146]) (l₂ := [147, 148])
  have hm := merge_right (literal (valuationOf q) (287)) (literal (valuationOf q) (289)) (countLit q [145, 146]) (countLit q [147, 148]) (count289 q) 1 (meaning287 q) (meaning289 q) hs
  change valuationOf q 287 = false ∨ valuationOf q 289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause917 (q : Snake 81) (h : Conditions q) : valuation q 287 = false ∨ valuation q 289 = true := counterClause917 (baseVal q)

theorem counterClause918 (q : Nat → Bool) : valuationOf q 285 = false ∨ valuationOf q 289 = true := by
  have hs : count289 q = (countLit q [145, 146]) + (countLit q [147, 148]) := List.countP_append (p := literal q) (l₁ := [145, 146]) (l₂ := [147, 148])
  have hm := merge_left (literal (valuationOf q) (285)) (literal (valuationOf q) (289)) (countLit q [145, 146]) (countLit q [147, 148]) (count289 q) 1 (meaning285 q) (meaning289 q) hs
  change valuationOf q 285 = false ∨ valuationOf q 289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause918 (q : Snake 81) (h : Conditions q) : valuation q 285 = false ∨ valuation q 289 = true := counterClause918 (baseVal q)

theorem counterClause919 (q : Nat → Bool) : valuationOf q 150 = false ∨ valuationOf q 291 = true := by
  have hs : count291 q = (countLit q [149]) + (countLit q [150]) := List.countP_append (p := literal q) (l₁ := [149]) (l₂ := [150])
  have hm := merge_right (literal (valuationOf q) (150)) (literal (valuationOf q) (291)) (countLit q [149]) (countLit q [150]) (count291 q) 1 (meaning150 q) (meaning291 q) hs
  change valuationOf q 150 = false ∨ valuationOf q 291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause919 (q : Snake 81) (h : Conditions q) : valuation q 150 = false ∨ valuation q 291 = true := counterClause919 (baseVal q)

theorem counterClause920 (q : Nat → Bool) : valuationOf q 291 = false ∨ valuationOf q 295 = true := by
  have hs : count295 q = (countLit q [149, 150]) + (countLit q [151, 152]) := List.countP_append (p := literal q) (l₁ := [149, 150]) (l₂ := [151, 152])
  have hm := merge_left (literal (valuationOf q) (291)) (literal (valuationOf q) (295)) (countLit q [149, 150]) (countLit q [151, 152]) (count295 q) 1 (meaning291 q) (meaning295 q) hs
  change valuationOf q 291 = false ∨ valuationOf q 295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause920 (q : Snake 81) (h : Conditions q) : valuation q 291 = false ∨ valuation q 295 = true := counterClause920 (baseVal q)

theorem counterClause921 (q : Nat → Bool) : valuationOf q 295 = false ∨ valuationOf q 297 = true := by
  have hs : count297 q = (countLit q [145, 146, 147, 148]) + (countLit q [149, 150, 151, 152]) := List.countP_append (p := literal q) (l₁ := [145, 146, 147, 148]) (l₂ := [149, 150, 151, 152])
  have hm := merge_right (literal (valuationOf q) (295)) (literal (valuationOf q) (297)) (countLit q [145, 146, 147, 148]) (countLit q [149, 150, 151, 152]) (count297 q) 1 (meaning295 q) (meaning297 q) hs
  change valuationOf q 295 = false ∨ valuationOf q 297 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause921 (q : Snake 81) (h : Conditions q) : valuation q 295 = false ∨ valuation q 297 = true := counterClause921 (baseVal q)

theorem counterClause922 (q : Nat → Bool) : valuationOf q 289 = false ∨ valuationOf q 297 = true := by
  have hs : count297 q = (countLit q [145, 146, 147, 148]) + (countLit q [149, 150, 151, 152]) := List.countP_append (p := literal q) (l₁ := [145, 146, 147, 148]) (l₂ := [149, 150, 151, 152])
  have hm := merge_left (literal (valuationOf q) (289)) (literal (valuationOf q) (297)) (countLit q [145, 146, 147, 148]) (countLit q [149, 150, 151, 152]) (count297 q) 1 (meaning289 q) (meaning297 q) hs
  change valuationOf q 289 = false ∨ valuationOf q 297 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause922 (q : Snake 81) (h : Conditions q) : valuation q 289 = false ∨ valuation q 297 = true := counterClause922 (baseVal q)

theorem counterClause923 (q : Nat → Bool) : valuationOf q 289 = false ∨ valuationOf q 295 = false ∨ valuationOf q 298 = true := by
  have hs : count297 q = (countLit q [145, 146, 147, 148]) + (countLit q [149, 150, 151, 152]) := List.countP_append (p := literal q) (l₁ := [145, 146, 147, 148]) (l₂ := [149, 150, 151, 152])
  have hm := merge_two (literal (valuationOf q) (289)) (literal (valuationOf q) (295)) (literal (valuationOf q) (298)) (countLit q [145, 146, 147, 148]) (countLit q [149, 150, 151, 152]) (count297 q) 1 1 (meaning289 q) (meaning295 q) (meaning298 q) hs
  change valuationOf q 289 = false ∨ valuationOf q 295 = false ∨ valuationOf q 298 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause923 (q : Snake 81) (h : Conditions q) : valuation q 289 = false ∨ valuation q 295 = false ∨ valuation q 298 = true := counterClause923 (baseVal q)

theorem counterClause924 (q : Nat → Bool) : valuationOf q 154 = false ∨ valuationOf q 299 = true := by
  have hs : count299 q = (countLit q [153]) + (countLit q [154]) := List.countP_append (p := literal q) (l₁ := [153]) (l₂ := [154])
  have hm := merge_right (literal (valuationOf q) (154)) (literal (valuationOf q) (299)) (countLit q [153]) (countLit q [154]) (count299 q) 1 (meaning154 q) (meaning299 q) hs
  change valuationOf q 154 = false ∨ valuationOf q 299 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause924 (q : Snake 81) (h : Conditions q) : valuation q 154 = false ∨ valuation q 299 = true := counterClause924 (baseVal q)

theorem counterClause925 (q : Nat → Bool) : valuationOf q 299 = false ∨ valuationOf q 303 = true := by
  have hs : count303 q = (countLit q [153, 154]) + (countLit q [155, 156]) := List.countP_append (p := literal q) (l₁ := [153, 154]) (l₂ := [155, 156])
  have hm := merge_left (literal (valuationOf q) (299)) (literal (valuationOf q) (303)) (countLit q [153, 154]) (countLit q [155, 156]) (count303 q) 1 (meaning299 q) (meaning303 q) hs
  change valuationOf q 299 = false ∨ valuationOf q 303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause925 (q : Snake 81) (h : Conditions q) : valuation q 299 = false ∨ valuation q 303 = true := counterClause925 (baseVal q)

theorem counterClause926 (q : Nat → Bool) : valuationOf q 158 = false ∨ valuationOf q 305 = true := by
  have hs : count305 q = (countLit q [157]) + (countLit q [158]) := List.countP_append (p := literal q) (l₁ := [157]) (l₂ := [158])
  have hm := merge_right (literal (valuationOf q) (158)) (literal (valuationOf q) (305)) (countLit q [157]) (countLit q [158]) (count305 q) 1 (meaning158 q) (meaning305 q) hs
  change valuationOf q 158 = false ∨ valuationOf q 305 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause926 (q : Snake 81) (h : Conditions q) : valuation q 158 = false ∨ valuation q 305 = true := counterClause926 (baseVal q)

theorem counterClause927 (q : Nat → Bool) : valuationOf q 160 = false ∨ valuationOf q 307 = true := by
  have hs : count307 q = (countLit q [159]) + (countLit q [160]) := List.countP_append (p := literal q) (l₁ := [159]) (l₂ := [160])
  have hm := merge_right (literal (valuationOf q) (160)) (literal (valuationOf q) (307)) (countLit q [159]) (countLit q [160]) (count307 q) 1 (meaning160 q) (meaning307 q) hs
  change valuationOf q 160 = false ∨ valuationOf q 307 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause927 (q : Snake 81) (h : Conditions q) : valuation q 160 = false ∨ valuation q 307 = true := counterClause927 (baseVal q)

theorem counterClause928 (q : Nat → Bool) : valuationOf q 159 = false ∨ valuationOf q 307 = true := by
  have hs : count307 q = (countLit q [159]) + (countLit q [160]) := List.countP_append (p := literal q) (l₁ := [159]) (l₂ := [160])
  have hm := merge_left (literal (valuationOf q) (159)) (literal (valuationOf q) (307)) (countLit q [159]) (countLit q [160]) (count307 q) 1 (meaning159 q) (meaning307 q) hs
  change valuationOf q 159 = false ∨ valuationOf q 307 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause928 (q : Snake 81) (h : Conditions q) : valuation q 159 = false ∨ valuation q 307 = true := counterClause928 (baseVal q)

theorem block28 (q : Snake 81) (h : Conditions q) : B112E034.Block28 (valuation q) :=
  ⟨clause897 q h, clause898 q h, clause899 q h, clause900 q h, clause901 q h, clause902 q h, clause903 q h, clause904 q h, clause905 q h, clause906 q h, clause907 q h, clause908 q h, clause909 q h, clause910 q h, clause911 q h, clause912 q h, clause913 q h, clause914 q h, clause915 q h, clause916 q h, clause917 q h, clause918 q h, clause919 q h, clause920 q h, clause921 q h, clause922 q h, clause923 q h, clause924 q h, clause925 q h, clause926 q h, clause927 q h, clause928 q h⟩

end
end Snake9.Regrowth.E112034
