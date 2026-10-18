import E112145Semantics
import B112E145Inputs
namespace Snake9.Regrowth.E112145
noncomputable section
local instance blockDec10 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause321 (q : Nat → Bool) : valuationOf q 304 = false ∨ valuationOf q 306 = true := by
  have hs : count305 q = (countLit q [131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143]) + (countLit q [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156]) := List.countP_append (p := literal q) (l₁ := [131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143]) (l₂ := [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156])
  have hm := merge_right (literal (valuationOf q) (304)) (literal (valuationOf q) (306)) (countLit q [131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143]) (countLit q [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156]) (count305 q) 2 (meaning304 q) (meaning306 q) hs
  change valuationOf q 304 = false ∨ valuationOf q 306 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause321 (q : Snake 81) (h : Conditions q) : valuation q 304 = false ∨ valuation q 306 = true := counterClause321 (baseVal q)

theorem counterClause322 (q : Nat → Bool) : valuationOf q 279 = false ∨ valuationOf q 305 = true := by
  have hs : count305 q = (countLit q [131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143]) + (countLit q [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156]) := List.countP_append (p := literal q) (l₁ := [131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143]) (l₂ := [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156])
  have hm := merge_left (literal (valuationOf q) (279)) (literal (valuationOf q) (305)) (countLit q [131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143]) (countLit q [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156]) (count305 q) 1 (meaning279 q) (meaning305 q) hs
  change valuationOf q 279 = false ∨ valuationOf q 305 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause322 (q : Snake 81) (h : Conditions q) : valuation q 279 = false ∨ valuation q 305 = true := counterClause322 (baseVal q)

theorem counterClause323 (q : Nat → Bool) : valuationOf q 279 = false ∨ valuationOf q 303 = false ∨ valuationOf q 306 = true := by
  have hs : count305 q = (countLit q [131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143]) + (countLit q [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156]) := List.countP_append (p := literal q) (l₁ := [131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143]) (l₂ := [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156])
  have hm := merge_two (literal (valuationOf q) (279)) (literal (valuationOf q) (303)) (literal (valuationOf q) (306)) (countLit q [131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143]) (countLit q [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156]) (count305 q) 1 1 (meaning279 q) (meaning303 q) (meaning306 q) hs
  change valuationOf q 279 = false ∨ valuationOf q 303 = false ∨ valuationOf q 306 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause323 (q : Snake 81) (h : Conditions q) : valuation q 279 = false ∨ valuation q 303 = false ∨ valuation q 306 = true := counterClause323 (baseVal q)

theorem counterClause324 (q : Nat → Bool) : valuationOf q 280 = false ∨ valuationOf q 306 = true := by
  have hs : count305 q = (countLit q [131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143]) + (countLit q [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156]) := List.countP_append (p := literal q) (l₁ := [131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143]) (l₂ := [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156])
  have hm := merge_left (literal (valuationOf q) (280)) (literal (valuationOf q) (306)) (countLit q [131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143]) (countLit q [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156]) (count305 q) 2 (meaning280 q) (meaning306 q) hs
  change valuationOf q 280 = false ∨ valuationOf q 306 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause324 (q : Snake 81) (h : Conditions q) : valuation q 280 = false ∨ valuation q 306 = true := counterClause324 (baseVal q)

theorem counterClause325 (q : Nat → Bool) : valuationOf q 305 = false ∨ valuationOf q 307 = true := by
  have hs : count307 q = (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 124, 125, 126, 127, 128, 129, 130]) + (countLit q [131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 124, 125, 126, 127, 128, 129, 130]) (l₂ := [131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156])
  have hm := merge_right (literal (valuationOf q) (305)) (literal (valuationOf q) (307)) (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 124, 125, 126, 127, 128, 129, 130]) (countLit q [131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156]) (count307 q) 1 (meaning305 q) (meaning307 q) hs
  change valuationOf q 305 = false ∨ valuationOf q 307 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause325 (q : Snake 81) (h : Conditions q) : valuation q 305 = false ∨ valuation q 307 = true := counterClause325 (baseVal q)

theorem counterClause326 (q : Nat → Bool) : valuationOf q 306 = false ∨ valuationOf q 308 = true := by
  have hs : count307 q = (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 124, 125, 126, 127, 128, 129, 130]) + (countLit q [131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 124, 125, 126, 127, 128, 129, 130]) (l₂ := [131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156])
  have hm := merge_right (literal (valuationOf q) (306)) (literal (valuationOf q) (308)) (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 124, 125, 126, 127, 128, 129, 130]) (countLit q [131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156]) (count307 q) 2 (meaning306 q) (meaning308 q) hs
  change valuationOf q 306 = false ∨ valuationOf q 308 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause326 (q : Snake 81) (h : Conditions q) : valuation q 306 = false ∨ valuation q 308 = true := counterClause326 (baseVal q)

theorem counterClause327 (q : Nat → Bool) : valuationOf q 255 = false ∨ valuationOf q 307 = true := by
  have hs : count307 q = (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 124, 125, 126, 127, 128, 129, 130]) + (countLit q [131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 124, 125, 126, 127, 128, 129, 130]) (l₂ := [131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156])
  have hm := merge_left (literal (valuationOf q) (255)) (literal (valuationOf q) (307)) (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 124, 125, 126, 127, 128, 129, 130]) (countLit q [131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156]) (count307 q) 1 (meaning255 q) (meaning307 q) hs
  change valuationOf q 255 = false ∨ valuationOf q 307 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause327 (q : Snake 81) (h : Conditions q) : valuation q 255 = false ∨ valuation q 307 = true := counterClause327 (baseVal q)

theorem counterClause328 (q : Nat → Bool) : valuationOf q 255 = false ∨ valuationOf q 305 = false ∨ valuationOf q 308 = true := by
  have hs : count307 q = (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 124, 125, 126, 127, 128, 129, 130]) + (countLit q [131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 124, 125, 126, 127, 128, 129, 130]) (l₂ := [131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156])
  have hm := merge_two (literal (valuationOf q) (255)) (literal (valuationOf q) (305)) (literal (valuationOf q) (308)) (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 124, 125, 126, 127, 128, 129, 130]) (countLit q [131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156]) (count307 q) 1 1 (meaning255 q) (meaning305 q) (meaning308 q) hs
  change valuationOf q 255 = false ∨ valuationOf q 305 = false ∨ valuationOf q 308 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause328 (q : Snake 81) (h : Conditions q) : valuation q 255 = false ∨ valuation q 305 = false ∨ valuation q 308 = true := counterClause328 (baseVal q)

theorem counterClause329 (q : Nat → Bool) : valuationOf q 256 = false ∨ valuationOf q 308 = true := by
  have hs : count307 q = (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 124, 125, 126, 127, 128, 129, 130]) + (countLit q [131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 124, 125, 126, 127, 128, 129, 130]) (l₂ := [131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156])
  have hm := merge_left (literal (valuationOf q) (256)) (literal (valuationOf q) (308)) (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 124, 125, 126, 127, 128, 129, 130]) (countLit q [131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156]) (count307 q) 2 (meaning256 q) (meaning308 q) hs
  change valuationOf q 256 = false ∨ valuationOf q 308 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause329 (q : Snake 81) (h : Conditions q) : valuation q 256 = false ∨ valuation q 308 = true := counterClause329 (baseVal q)

theorem counterClause330 (q : Nat → Bool) : valuationOf q 159 = false ∨ valuationOf q 309 = true := by
  have hs : count309 q = (countLit q [158]) + (countLit q [159]) := List.countP_append (p := literal q) (l₁ := [158]) (l₂ := [159])
  have hm := merge_right (literal (valuationOf q) (159)) (literal (valuationOf q) (309)) (countLit q [158]) (countLit q [159]) (count309 q) 1 (meaning159 q) (meaning309 q) hs
  change valuationOf q 159 = false ∨ valuationOf q 309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause330 (q : Snake 81) (h : Conditions q) : valuation q 159 = false ∨ valuation q 309 = true := counterClause330 (baseVal q)

theorem counterClause331 (q : Nat → Bool) : valuationOf q 309 = false ∨ valuationOf q 311 = true := by
  have hs : count311 q = (countLit q [157]) + (countLit q [158, 159]) := List.countP_append (p := literal q) (l₁ := [157]) (l₂ := [158, 159])
  have hm := merge_right (literal (valuationOf q) (309)) (literal (valuationOf q) (311)) (countLit q [157]) (countLit q [158, 159]) (count311 q) 1 (meaning309 q) (meaning311 q) hs
  change valuationOf q 309 = false ∨ valuationOf q 311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause331 (q : Snake 81) (h : Conditions q) : valuation q 309 = false ∨ valuation q 311 = true := counterClause331 (baseVal q)

theorem counterClause332 (q : Nat → Bool) : valuationOf q 157 = false ∨ valuationOf q 311 = true := by
  have hs : count311 q = (countLit q [157]) + (countLit q [158, 159]) := List.countP_append (p := literal q) (l₁ := [157]) (l₂ := [158, 159])
  have hm := merge_left (literal (valuationOf q) (157)) (literal (valuationOf q) (311)) (countLit q [157]) (countLit q [158, 159]) (count311 q) 1 (meaning157 q) (meaning311 q) hs
  change valuationOf q 157 = false ∨ valuationOf q 311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause332 (q : Snake 81) (h : Conditions q) : valuation q 157 = false ∨ valuation q 311 = true := counterClause332 (baseVal q)

theorem counterClause333 (q : Nat → Bool) : valuationOf q 162 = false ∨ valuationOf q 313 = true := by
  have hs : count313 q = (countLit q [161]) + (countLit q [162]) := List.countP_append (p := literal q) (l₁ := [161]) (l₂ := [162])
  have hm := merge_right (literal (valuationOf q) (162)) (literal (valuationOf q) (313)) (countLit q [161]) (countLit q [162]) (count313 q) 1 (meaning162 q) (meaning313 q) hs
  change valuationOf q 162 = false ∨ valuationOf q 313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause333 (q : Snake 81) (h : Conditions q) : valuation q 162 = false ∨ valuation q 313 = true := counterClause333 (baseVal q)

theorem counterClause334 (q : Nat → Bool) : valuationOf q 161 = false ∨ valuationOf q 313 = true := by
  have hs : count313 q = (countLit q [161]) + (countLit q [162]) := List.countP_append (p := literal q) (l₁ := [161]) (l₂ := [162])
  have hm := merge_left (literal (valuationOf q) (161)) (literal (valuationOf q) (313)) (countLit q [161]) (countLit q [162]) (count313 q) 1 (meaning161 q) (meaning313 q) hs
  change valuationOf q 161 = false ∨ valuationOf q 313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause334 (q : Snake 81) (h : Conditions q) : valuation q 161 = false ∨ valuation q 313 = true := counterClause334 (baseVal q)

theorem counterClause335 (q : Nat → Bool) : valuationOf q 161 = false ∨ valuationOf q 162 = false ∨ valuationOf q 314 = true := by
  have hs : count313 q = (countLit q [161]) + (countLit q [162]) := List.countP_append (p := literal q) (l₁ := [161]) (l₂ := [162])
  have hm := merge_two (literal (valuationOf q) (161)) (literal (valuationOf q) (162)) (literal (valuationOf q) (314)) (countLit q [161]) (countLit q [162]) (count313 q) 1 1 (meaning161 q) (meaning162 q) (meaning314 q) hs
  change valuationOf q 161 = false ∨ valuationOf q 162 = false ∨ valuationOf q 314 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause335 (q : Snake 81) (h : Conditions q) : valuation q 161 = false ∨ valuation q 162 = false ∨ valuation q 314 = true := counterClause335 (baseVal q)

theorem counterClause336 (q : Nat → Bool) : valuationOf q 313 = false ∨ valuationOf q 315 = true := by
  have hs : count315 q = (countLit q [160]) + (countLit q [161, 162]) := List.countP_append (p := literal q) (l₁ := [160]) (l₂ := [161, 162])
  have hm := merge_right (literal (valuationOf q) (313)) (literal (valuationOf q) (315)) (countLit q [160]) (countLit q [161, 162]) (count315 q) 1 (meaning313 q) (meaning315 q) hs
  change valuationOf q 313 = false ∨ valuationOf q 315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause336 (q : Snake 81) (h : Conditions q) : valuation q 313 = false ∨ valuation q 315 = true := counterClause336 (baseVal q)

theorem counterClause337 (q : Nat → Bool) : valuationOf q 314 = false ∨ valuationOf q 316 = true := by
  have hs : count315 q = (countLit q [160]) + (countLit q [161, 162]) := List.countP_append (p := literal q) (l₁ := [160]) (l₂ := [161, 162])
  have hm := merge_right (literal (valuationOf q) (314)) (literal (valuationOf q) (316)) (countLit q [160]) (countLit q [161, 162]) (count315 q) 2 (meaning314 q) (meaning316 q) hs
  change valuationOf q 314 = false ∨ valuationOf q 316 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause337 (q : Snake 81) (h : Conditions q) : valuation q 314 = false ∨ valuation q 316 = true := counterClause337 (baseVal q)

theorem counterClause338 (q : Nat → Bool) : valuationOf q 315 = false ∨ valuationOf q 317 = true := by
  have hs : count317 q = (countLit q [157, 158, 159]) + (countLit q [160, 161, 162]) := List.countP_append (p := literal q) (l₁ := [157, 158, 159]) (l₂ := [160, 161, 162])
  have hm := merge_right (literal (valuationOf q) (315)) (literal (valuationOf q) (317)) (countLit q [157, 158, 159]) (countLit q [160, 161, 162]) (count317 q) 1 (meaning315 q) (meaning317 q) hs
  change valuationOf q 315 = false ∨ valuationOf q 317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause338 (q : Snake 81) (h : Conditions q) : valuation q 315 = false ∨ valuation q 317 = true := counterClause338 (baseVal q)

theorem counterClause339 (q : Nat → Bool) : valuationOf q 316 = false ∨ valuationOf q 318 = true := by
  have hs : count317 q = (countLit q [157, 158, 159]) + (countLit q [160, 161, 162]) := List.countP_append (p := literal q) (l₁ := [157, 158, 159]) (l₂ := [160, 161, 162])
  have hm := merge_right (literal (valuationOf q) (316)) (literal (valuationOf q) (318)) (countLit q [157, 158, 159]) (countLit q [160, 161, 162]) (count317 q) 2 (meaning316 q) (meaning318 q) hs
  change valuationOf q 316 = false ∨ valuationOf q 318 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause339 (q : Snake 81) (h : Conditions q) : valuation q 316 = false ∨ valuation q 318 = true := counterClause339 (baseVal q)

theorem counterClause340 (q : Nat → Bool) : valuationOf q 311 = false ∨ valuationOf q 317 = true := by
  have hs : count317 q = (countLit q [157, 158, 159]) + (countLit q [160, 161, 162]) := List.countP_append (p := literal q) (l₁ := [157, 158, 159]) (l₂ := [160, 161, 162])
  have hm := merge_left (literal (valuationOf q) (311)) (literal (valuationOf q) (317)) (countLit q [157, 158, 159]) (countLit q [160, 161, 162]) (count317 q) 1 (meaning311 q) (meaning317 q) hs
  change valuationOf q 311 = false ∨ valuationOf q 317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause340 (q : Snake 81) (h : Conditions q) : valuation q 311 = false ∨ valuation q 317 = true := counterClause340 (baseVal q)

theorem counterClause341 (q : Nat → Bool) : valuationOf q 163 = false ∨ valuationOf q 321 = true := by
  have hs : count321 q = (countLit q [163]) + (countLit q [164, 165]) := List.countP_append (p := literal q) (l₁ := [163]) (l₂ := [164, 165])
  have hm := merge_left (literal (valuationOf q) (163)) (literal (valuationOf q) (321)) (countLit q [163]) (countLit q [164, 165]) (count321 q) 1 (meaning163 q) (meaning321 q) hs
  change valuationOf q 163 = false ∨ valuationOf q 321 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause341 (q : Snake 81) (h : Conditions q) : valuation q 163 = false ∨ valuation q 321 = true := counterClause341 (baseVal q)

theorem counterClause342 (q : Nat → Bool) : valuationOf q 167 = false ∨ valuationOf q 323 = true := by
  have hs : count323 q = (countLit q [166]) + (countLit q [167]) := List.countP_append (p := literal q) (l₁ := [166]) (l₂ := [167])
  have hm := merge_right (literal (valuationOf q) (167)) (literal (valuationOf q) (323)) (countLit q [166]) (countLit q [167]) (count323 q) 1 (meaning167 q) (meaning323 q) hs
  change valuationOf q 167 = false ∨ valuationOf q 323 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause342 (q : Snake 81) (h : Conditions q) : valuation q 167 = false ∨ valuation q 323 = true := counterClause342 (baseVal q)

theorem counterClause343 (q : Nat → Bool) : valuationOf q 169 = false ∨ valuationOf q 325 = true := by
  have hs : count325 q = (countLit q [168]) + (countLit q [169]) := List.countP_append (p := literal q) (l₁ := [168]) (l₂ := [169])
  have hm := merge_right (literal (valuationOf q) (169)) (literal (valuationOf q) (325)) (countLit q [168]) (countLit q [169]) (count325 q) 1 (meaning169 q) (meaning325 q) hs
  change valuationOf q 169 = false ∨ valuationOf q 325 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause343 (q : Snake 81) (h : Conditions q) : valuation q 169 = false ∨ valuation q 325 = true := counterClause343 (baseVal q)

theorem counterClause344 (q : Nat → Bool) : valuationOf q 325 = false ∨ valuationOf q 327 = true := by
  have hs : count327 q = (countLit q [166, 167]) + (countLit q [168, 169]) := List.countP_append (p := literal q) (l₁ := [166, 167]) (l₂ := [168, 169])
  have hm := merge_right (literal (valuationOf q) (325)) (literal (valuationOf q) (327)) (countLit q [166, 167]) (countLit q [168, 169]) (count327 q) 1 (meaning325 q) (meaning327 q) hs
  change valuationOf q 325 = false ∨ valuationOf q 327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause344 (q : Snake 81) (h : Conditions q) : valuation q 325 = false ∨ valuation q 327 = true := counterClause344 (baseVal q)

theorem counterClause345 (q : Nat → Bool) : valuationOf q 323 = false ∨ valuationOf q 327 = true := by
  have hs : count327 q = (countLit q [166, 167]) + (countLit q [168, 169]) := List.countP_append (p := literal q) (l₁ := [166, 167]) (l₂ := [168, 169])
  have hm := merge_left (literal (valuationOf q) (323)) (literal (valuationOf q) (327)) (countLit q [166, 167]) (countLit q [168, 169]) (count327 q) 1 (meaning323 q) (meaning327 q) hs
  change valuationOf q 323 = false ∨ valuationOf q 327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause345 (q : Snake 81) (h : Conditions q) : valuation q 323 = false ∨ valuation q 327 = true := counterClause345 (baseVal q)

theorem counterClause346 (q : Nat → Bool) : valuationOf q 327 = false ∨ valuationOf q 329 = true := by
  have hs : count329 q = (countLit q [163, 164, 165]) + (countLit q [166, 167, 168, 169]) := List.countP_append (p := literal q) (l₁ := [163, 164, 165]) (l₂ := [166, 167, 168, 169])
  have hm := merge_right (literal (valuationOf q) (327)) (literal (valuationOf q) (329)) (countLit q [163, 164, 165]) (countLit q [166, 167, 168, 169]) (count329 q) 1 (meaning327 q) (meaning329 q) hs
  change valuationOf q 327 = false ∨ valuationOf q 329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause346 (q : Snake 81) (h : Conditions q) : valuation q 327 = false ∨ valuation q 329 = true := counterClause346 (baseVal q)

theorem counterClause347 (q : Nat → Bool) : valuationOf q 321 = false ∨ valuationOf q 329 = true := by
  have hs : count329 q = (countLit q [163, 164, 165]) + (countLit q [166, 167, 168, 169]) := List.countP_append (p := literal q) (l₁ := [163, 164, 165]) (l₂ := [166, 167, 168, 169])
  have hm := merge_left (literal (valuationOf q) (321)) (literal (valuationOf q) (329)) (countLit q [163, 164, 165]) (countLit q [166, 167, 168, 169]) (count329 q) 1 (meaning321 q) (meaning329 q) hs
  change valuationOf q 321 = false ∨ valuationOf q 329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause347 (q : Snake 81) (h : Conditions q) : valuation q 321 = false ∨ valuation q 329 = true := counterClause347 (baseVal q)

theorem counterClause348 (q : Nat → Bool) : valuationOf q 329 = false ∨ valuationOf q 331 = true := by
  have hs : count331 q = (countLit q [157, 158, 159, 160, 161, 162]) + (countLit q [163, 164, 165, 166, 167, 168, 169]) := List.countP_append (p := literal q) (l₁ := [157, 158, 159, 160, 161, 162]) (l₂ := [163, 164, 165, 166, 167, 168, 169])
  have hm := merge_right (literal (valuationOf q) (329)) (literal (valuationOf q) (331)) (countLit q [157, 158, 159, 160, 161, 162]) (countLit q [163, 164, 165, 166, 167, 168, 169]) (count331 q) 1 (meaning329 q) (meaning331 q) hs
  change valuationOf q 329 = false ∨ valuationOf q 331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause348 (q : Snake 81) (h : Conditions q) : valuation q 329 = false ∨ valuation q 331 = true := counterClause348 (baseVal q)

theorem counterClause349 (q : Nat → Bool) : valuationOf q 317 = false ∨ valuationOf q 331 = true := by
  have hs : count331 q = (countLit q [157, 158, 159, 160, 161, 162]) + (countLit q [163, 164, 165, 166, 167, 168, 169]) := List.countP_append (p := literal q) (l₁ := [157, 158, 159, 160, 161, 162]) (l₂ := [163, 164, 165, 166, 167, 168, 169])
  have hm := merge_left (literal (valuationOf q) (317)) (literal (valuationOf q) (331)) (countLit q [157, 158, 159, 160, 161, 162]) (countLit q [163, 164, 165, 166, 167, 168, 169]) (count331 q) 1 (meaning317 q) (meaning331 q) hs
  change valuationOf q 317 = false ∨ valuationOf q 331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause349 (q : Snake 81) (h : Conditions q) : valuation q 317 = false ∨ valuation q 331 = true := counterClause349 (baseVal q)

theorem counterClause350 (q : Nat → Bool) : valuationOf q 318 = false ∨ valuationOf q 332 = true := by
  have hs : count331 q = (countLit q [157, 158, 159, 160, 161, 162]) + (countLit q [163, 164, 165, 166, 167, 168, 169]) := List.countP_append (p := literal q) (l₁ := [157, 158, 159, 160, 161, 162]) (l₂ := [163, 164, 165, 166, 167, 168, 169])
  have hm := merge_left (literal (valuationOf q) (318)) (literal (valuationOf q) (332)) (countLit q [157, 158, 159, 160, 161, 162]) (countLit q [163, 164, 165, 166, 167, 168, 169]) (count331 q) 2 (meaning318 q) (meaning332 q) hs
  change valuationOf q 318 = false ∨ valuationOf q 332 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause350 (q : Snake 81) (h : Conditions q) : valuation q 318 = false ∨ valuation q 332 = true := counterClause350 (baseVal q)

theorem counterClause351 (q : Nat → Bool) : valuationOf q 171 = false ∨ valuationOf q 333 = true := by
  have hs : count333 q = (countLit q [171]) + (countLit q [172]) := List.countP_append (p := literal q) (l₁ := [171]) (l₂ := [172])
  have hm := merge_left (literal (valuationOf q) (171)) (literal (valuationOf q) (333)) (countLit q [171]) (countLit q [172]) (count333 q) 1 (meaning171 q) (meaning333 q) hs
  change valuationOf q 171 = false ∨ valuationOf q 333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause351 (q : Snake 81) (h : Conditions q) : valuation q 171 = false ∨ valuation q 333 = true := counterClause351 (baseVal q)

theorem counterClause352 (q : Nat → Bool) : valuationOf q 333 = false ∨ valuationOf q 335 = true := by
  have hs : count335 q = (countLit q [170]) + (countLit q [171, 172]) := List.countP_append (p := literal q) (l₁ := [170]) (l₂ := [171, 172])
  have hm := merge_right (literal (valuationOf q) (333)) (literal (valuationOf q) (335)) (countLit q [170]) (countLit q [171, 172]) (count335 q) 1 (meaning333 q) (meaning335 q) hs
  change valuationOf q 333 = false ∨ valuationOf q 335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause352 (q : Snake 81) (h : Conditions q) : valuation q 333 = false ∨ valuation q 335 = true := counterClause352 (baseVal q)

theorem block10 (q : Snake 81) (h : Conditions q) : B112E145.Block10 (valuation q) :=
  ⟨clause321 q h, clause322 q h, clause323 q h, clause324 q h, clause325 q h, clause326 q h, clause327 q h, clause328 q h, clause329 q h, clause330 q h, clause331 q h, clause332 q h, clause333 q h, clause334 q h, clause335 q h, clause336 q h, clause337 q h, clause338 q h, clause339 q h, clause340 q h, clause341 q h, clause342 q h, clause343 q h, clause344 q h, clause345 q h, clause346 q h, clause347 q h, clause348 q h, clause349 q h, clause350 q h, clause351 q h, clause352 q h⟩

end
end Snake9.Regrowth.E112145
