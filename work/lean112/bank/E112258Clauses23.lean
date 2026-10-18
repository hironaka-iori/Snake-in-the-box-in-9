import E112258Semantics
import B112E258Inputs
namespace Snake9.Regrowth.E112258
noncomputable section
local instance blockDec23 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause737 (q : Nat → Bool) : valuationOf q 152 = false ∨ valuationOf q 293 = true := by
  have hs : count293 q = (countLit q [151]) + (countLit q [152]) := List.countP_append (p := literal q) (l₁ := [151]) (l₂ := [152])
  have hm := merge_right (literal (valuationOf q) (152)) (literal (valuationOf q) (293)) (countLit q [151]) (countLit q [152]) (count293 q) 1 (meaning152 q) (meaning293 q) hs
  change valuationOf q 152 = false ∨ valuationOf q 293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause737 (q : Snake 81) (h : Conditions q) : valuation q 152 = false ∨ valuation q 293 = true := counterClause737 (baseVal q)

theorem counterClause738 (q : Nat → Bool) : valuationOf q 293 = false ∨ valuationOf q 295 = true := by
  have hs : count295 q = (countLit q [149, 150]) + (countLit q [151, 152]) := List.countP_append (p := literal q) (l₁ := [149, 150]) (l₂ := [151, 152])
  have hm := merge_right (literal (valuationOf q) (293)) (literal (valuationOf q) (295)) (countLit q [149, 150]) (countLit q [151, 152]) (count295 q) 1 (meaning293 q) (meaning295 q) hs
  change valuationOf q 293 = false ∨ valuationOf q 295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause738 (q : Snake 81) (h : Conditions q) : valuation q 293 = false ∨ valuation q 295 = true := counterClause738 (baseVal q)

theorem counterClause739 (q : Nat → Bool) : valuationOf q 291 = false ∨ valuationOf q 295 = true := by
  have hs : count295 q = (countLit q [149, 150]) + (countLit q [151, 152]) := List.countP_append (p := literal q) (l₁ := [149, 150]) (l₂ := [151, 152])
  have hm := merge_left (literal (valuationOf q) (291)) (literal (valuationOf q) (295)) (countLit q [149, 150]) (countLit q [151, 152]) (count295 q) 1 (meaning291 q) (meaning295 q) hs
  change valuationOf q 291 = false ∨ valuationOf q 295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause739 (q : Snake 81) (h : Conditions q) : valuation q 291 = false ∨ valuation q 295 = true := counterClause739 (baseVal q)

theorem counterClause740 (q : Nat → Bool) : valuationOf q 295 = false ∨ valuationOf q 297 = true := by
  have hs : count297 q = (countLit q [145, 146, 147, 148]) + (countLit q [149, 150, 151, 152]) := List.countP_append (p := literal q) (l₁ := [145, 146, 147, 148]) (l₂ := [149, 150, 151, 152])
  have hm := merge_right (literal (valuationOf q) (295)) (literal (valuationOf q) (297)) (countLit q [145, 146, 147, 148]) (countLit q [149, 150, 151, 152]) (count297 q) 1 (meaning295 q) (meaning297 q) hs
  change valuationOf q 295 = false ∨ valuationOf q 297 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause740 (q : Snake 81) (h : Conditions q) : valuation q 295 = false ∨ valuation q 297 = true := counterClause740 (baseVal q)

theorem counterClause741 (q : Nat → Bool) : valuationOf q 289 = false ∨ valuationOf q 297 = true := by
  have hs : count297 q = (countLit q [145, 146, 147, 148]) + (countLit q [149, 150, 151, 152]) := List.countP_append (p := literal q) (l₁ := [145, 146, 147, 148]) (l₂ := [149, 150, 151, 152])
  have hm := merge_left (literal (valuationOf q) (289)) (literal (valuationOf q) (297)) (countLit q [145, 146, 147, 148]) (countLit q [149, 150, 151, 152]) (count297 q) 1 (meaning289 q) (meaning297 q) hs
  change valuationOf q 289 = false ∨ valuationOf q 297 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause741 (q : Snake 81) (h : Conditions q) : valuation q 289 = false ∨ valuation q 297 = true := counterClause741 (baseVal q)

theorem counterClause742 (q : Nat → Bool) : valuationOf q 297 = false ∨ valuationOf q 299 = true := by
  have hs : count299 q = (countLit q [138, 139, 140, 141, 142, 143, 144]) + (countLit q [145, 146, 147, 148, 149, 150, 151, 152]) := List.countP_append (p := literal q) (l₁ := [138, 139, 140, 141, 142, 143, 144]) (l₂ := [145, 146, 147, 148, 149, 150, 151, 152])
  have hm := merge_right (literal (valuationOf q) (297)) (literal (valuationOf q) (299)) (countLit q [138, 139, 140, 141, 142, 143, 144]) (countLit q [145, 146, 147, 148, 149, 150, 151, 152]) (count299 q) 1 (meaning297 q) (meaning299 q) hs
  change valuationOf q 297 = false ∨ valuationOf q 299 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause742 (q : Snake 81) (h : Conditions q) : valuation q 297 = false ∨ valuation q 299 = true := counterClause742 (baseVal q)

theorem counterClause743 (q : Nat → Bool) : valuationOf q 283 = false ∨ valuationOf q 299 = true := by
  have hs : count299 q = (countLit q [138, 139, 140, 141, 142, 143, 144]) + (countLit q [145, 146, 147, 148, 149, 150, 151, 152]) := List.countP_append (p := literal q) (l₁ := [138, 139, 140, 141, 142, 143, 144]) (l₂ := [145, 146, 147, 148, 149, 150, 151, 152])
  have hm := merge_left (literal (valuationOf q) (283)) (literal (valuationOf q) (299)) (countLit q [138, 139, 140, 141, 142, 143, 144]) (countLit q [145, 146, 147, 148, 149, 150, 151, 152]) (count299 q) 1 (meaning283 q) (meaning299 q) hs
  change valuationOf q 283 = false ∨ valuationOf q 299 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause743 (q : Snake 81) (h : Conditions q) : valuation q 283 = false ∨ valuation q 299 = true := counterClause743 (baseVal q)

theorem counterClause744 (q : Nat → Bool) : valuationOf q 283 = false ∨ valuationOf q 297 = false ∨ valuationOf q 300 = true := by
  have hs : count299 q = (countLit q [138, 139, 140, 141, 142, 143, 144]) + (countLit q [145, 146, 147, 148, 149, 150, 151, 152]) := List.countP_append (p := literal q) (l₁ := [138, 139, 140, 141, 142, 143, 144]) (l₂ := [145, 146, 147, 148, 149, 150, 151, 152])
  have hm := merge_two (literal (valuationOf q) (283)) (literal (valuationOf q) (297)) (literal (valuationOf q) (300)) (countLit q [138, 139, 140, 141, 142, 143, 144]) (countLit q [145, 146, 147, 148, 149, 150, 151, 152]) (count299 q) 1 1 (meaning283 q) (meaning297 q) (meaning300 q) hs
  change valuationOf q 283 = false ∨ valuationOf q 297 = false ∨ valuationOf q 300 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause744 (q : Snake 81) (h : Conditions q) : valuation q 283 = false ∨ valuation q 297 = false ∨ valuation q 300 = true := counterClause744 (baseVal q)

theorem counterClause745 (q : Nat → Bool) : valuationOf q 284 = false ∨ valuationOf q 300 = true := by
  have hs : count299 q = (countLit q [138, 139, 140, 141, 142, 143, 144]) + (countLit q [145, 146, 147, 148, 149, 150, 151, 152]) := List.countP_append (p := literal q) (l₁ := [138, 139, 140, 141, 142, 143, 144]) (l₂ := [145, 146, 147, 148, 149, 150, 151, 152])
  have hm := merge_left (literal (valuationOf q) (284)) (literal (valuationOf q) (300)) (countLit q [138, 139, 140, 141, 142, 143, 144]) (countLit q [145, 146, 147, 148, 149, 150, 151, 152]) (count299 q) 2 (meaning284 q) (meaning300 q) hs
  change valuationOf q 284 = false ∨ valuationOf q 300 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause745 (q : Snake 81) (h : Conditions q) : valuation q 284 = false ∨ valuation q 300 = true := counterClause745 (baseVal q)

theorem counterClause746 (q : Nat → Bool) : valuationOf q 299 = false ∨ valuationOf q 301 = true := by
  have hs : count301 q = (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) + (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) := List.countP_append (p := literal q) (l₁ := [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (l₂ := [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152])
  have hm := merge_right (literal (valuationOf q) (299)) (literal (valuationOf q) (301)) (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) (count301 q) 1 (meaning299 q) (meaning301 q) hs
  change valuationOf q 299 = false ∨ valuationOf q 301 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause746 (q : Snake 81) (h : Conditions q) : valuation q 299 = false ∨ valuation q 301 = true := counterClause746 (baseVal q)

theorem counterClause747 (q : Nat → Bool) : valuationOf q 300 = false ∨ valuationOf q 302 = true := by
  have hs : count301 q = (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) + (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) := List.countP_append (p := literal q) (l₁ := [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (l₂ := [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152])
  have hm := merge_right (literal (valuationOf q) (300)) (literal (valuationOf q) (302)) (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) (count301 q) 2 (meaning300 q) (meaning302 q) hs
  change valuationOf q 300 = false ∨ valuationOf q 302 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause747 (q : Snake 81) (h : Conditions q) : valuation q 300 = false ∨ valuation q 302 = true := counterClause747 (baseVal q)

theorem counterClause748 (q : Nat → Bool) : valuationOf q 271 = false ∨ valuationOf q 301 = true := by
  have hs : count301 q = (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) + (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) := List.countP_append (p := literal q) (l₁ := [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (l₂ := [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152])
  have hm := merge_left (literal (valuationOf q) (271)) (literal (valuationOf q) (301)) (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) (count301 q) 1 (meaning271 q) (meaning301 q) hs
  change valuationOf q 271 = false ∨ valuationOf q 301 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause748 (q : Snake 81) (h : Conditions q) : valuation q 271 = false ∨ valuation q 301 = true := counterClause748 (baseVal q)

theorem counterClause749 (q : Nat → Bool) : valuationOf q 271 = false ∨ valuationOf q 299 = false ∨ valuationOf q 302 = true := by
  have hs : count301 q = (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) + (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) := List.countP_append (p := literal q) (l₁ := [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (l₂ := [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152])
  have hm := merge_two (literal (valuationOf q) (271)) (literal (valuationOf q) (299)) (literal (valuationOf q) (302)) (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) (count301 q) 1 1 (meaning271 q) (meaning299 q) (meaning302 q) hs
  change valuationOf q 271 = false ∨ valuationOf q 299 = false ∨ valuationOf q 302 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause749 (q : Snake 81) (h : Conditions q) : valuation q 271 = false ∨ valuation q 299 = false ∨ valuation q 302 = true := counterClause749 (baseVal q)

theorem counterClause750 (q : Nat → Bool) : valuationOf q 272 = false ∨ valuationOf q 302 = true := by
  have hs : count301 q = (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) + (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) := List.countP_append (p := literal q) (l₁ := [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (l₂ := [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152])
  have hm := merge_left (literal (valuationOf q) (272)) (literal (valuationOf q) (302)) (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) (count301 q) 2 (meaning272 q) (meaning302 q) hs
  change valuationOf q 272 = false ∨ valuationOf q 302 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause750 (q : Snake 81) (h : Conditions q) : valuation q 272 = false ∨ valuation q 302 = true := counterClause750 (baseVal q)

theorem counterClause751 (q : Nat → Bool) : valuationOf q 154 = false ∨ valuationOf q 303 = true := by
  have hs : count303 q = (countLit q [154]) + (countLit q [155]) := List.countP_append (p := literal q) (l₁ := [154]) (l₂ := [155])
  have hm := merge_left (literal (valuationOf q) (154)) (literal (valuationOf q) (303)) (countLit q [154]) (countLit q [155]) (count303 q) 1 (meaning154 q) (meaning303 q) hs
  change valuationOf q 154 = false ∨ valuationOf q 303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause751 (q : Snake 81) (h : Conditions q) : valuation q 154 = false ∨ valuation q 303 = true := counterClause751 (baseVal q)

theorem counterClause752 (q : Nat → Bool) : valuationOf q 303 = false ∨ valuationOf q 305 = true := by
  have hs : count305 q = (countLit q [153]) + (countLit q [154, 155]) := List.countP_append (p := literal q) (l₁ := [153]) (l₂ := [154, 155])
  have hm := merge_right (literal (valuationOf q) (303)) (literal (valuationOf q) (305)) (countLit q [153]) (countLit q [154, 155]) (count305 q) 1 (meaning303 q) (meaning305 q) hs
  change valuationOf q 303 = false ∨ valuationOf q 305 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause752 (q : Snake 81) (h : Conditions q) : valuation q 303 = false ∨ valuation q 305 = true := counterClause752 (baseVal q)

theorem counterClause753 (q : Nat → Bool) : valuationOf q 156 = false ∨ valuationOf q 307 = true := by
  have hs : count307 q = (countLit q [156]) + (countLit q [157]) := List.countP_append (p := literal q) (l₁ := [156]) (l₂ := [157])
  have hm := merge_left (literal (valuationOf q) (156)) (literal (valuationOf q) (307)) (countLit q [156]) (countLit q [157]) (count307 q) 1 (meaning156 q) (meaning307 q) hs
  change valuationOf q 156 = false ∨ valuationOf q 307 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause753 (q : Snake 81) (h : Conditions q) : valuation q 156 = false ∨ valuation q 307 = true := counterClause753 (baseVal q)

theorem counterClause754 (q : Nat → Bool) : valuationOf q 158 = false ∨ valuationOf q 309 = true := by
  have hs : count309 q = (countLit q [158]) + (countLit q [159]) := List.countP_append (p := literal q) (l₁ := [158]) (l₂ := [159])
  have hm := merge_left (literal (valuationOf q) (158)) (literal (valuationOf q) (309)) (countLit q [158]) (countLit q [159]) (count309 q) 1 (meaning158 q) (meaning309 q) hs
  change valuationOf q 158 = false ∨ valuationOf q 309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause754 (q : Snake 81) (h : Conditions q) : valuation q 158 = false ∨ valuation q 309 = true := counterClause754 (baseVal q)

theorem counterClause755 (q : Nat → Bool) : valuationOf q 309 = false ∨ valuationOf q 311 = true := by
  have hs : count311 q = (countLit q [156, 157]) + (countLit q [158, 159]) := List.countP_append (p := literal q) (l₁ := [156, 157]) (l₂ := [158, 159])
  have hm := merge_right (literal (valuationOf q) (309)) (literal (valuationOf q) (311)) (countLit q [156, 157]) (countLit q [158, 159]) (count311 q) 1 (meaning309 q) (meaning311 q) hs
  change valuationOf q 309 = false ∨ valuationOf q 311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause755 (q : Snake 81) (h : Conditions q) : valuation q 309 = false ∨ valuation q 311 = true := counterClause755 (baseVal q)

theorem counterClause756 (q : Nat → Bool) : valuationOf q 307 = false ∨ valuationOf q 311 = true := by
  have hs : count311 q = (countLit q [156, 157]) + (countLit q [158, 159]) := List.countP_append (p := literal q) (l₁ := [156, 157]) (l₂ := [158, 159])
  have hm := merge_left (literal (valuationOf q) (307)) (literal (valuationOf q) (311)) (countLit q [156, 157]) (countLit q [158, 159]) (count311 q) 1 (meaning307 q) (meaning311 q) hs
  change valuationOf q 307 = false ∨ valuationOf q 311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause756 (q : Snake 81) (h : Conditions q) : valuation q 307 = false ∨ valuation q 311 = true := counterClause756 (baseVal q)

theorem counterClause757 (q : Nat → Bool) : valuationOf q 307 = false ∨ valuationOf q 309 = false ∨ valuationOf q 312 = true := by
  have hs : count311 q = (countLit q [156, 157]) + (countLit q [158, 159]) := List.countP_append (p := literal q) (l₁ := [156, 157]) (l₂ := [158, 159])
  have hm := merge_two (literal (valuationOf q) (307)) (literal (valuationOf q) (309)) (literal (valuationOf q) (312)) (countLit q [156, 157]) (countLit q [158, 159]) (count311 q) 1 1 (meaning307 q) (meaning309 q) (meaning312 q) hs
  change valuationOf q 307 = false ∨ valuationOf q 309 = false ∨ valuationOf q 312 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause757 (q : Snake 81) (h : Conditions q) : valuation q 307 = false ∨ valuation q 309 = false ∨ valuation q 312 = true := counterClause757 (baseVal q)

theorem counterClause758 (q : Nat → Bool) : valuationOf q 311 = false ∨ valuationOf q 313 = true := by
  have hs : count313 q = (countLit q [153, 154, 155]) + (countLit q [156, 157, 158, 159]) := List.countP_append (p := literal q) (l₁ := [153, 154, 155]) (l₂ := [156, 157, 158, 159])
  have hm := merge_right (literal (valuationOf q) (311)) (literal (valuationOf q) (313)) (countLit q [153, 154, 155]) (countLit q [156, 157, 158, 159]) (count313 q) 1 (meaning311 q) (meaning313 q) hs
  change valuationOf q 311 = false ∨ valuationOf q 313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause758 (q : Snake 81) (h : Conditions q) : valuation q 311 = false ∨ valuation q 313 = true := counterClause758 (baseVal q)

theorem counterClause759 (q : Nat → Bool) : valuationOf q 312 = false ∨ valuationOf q 314 = true := by
  have hs : count313 q = (countLit q [153, 154, 155]) + (countLit q [156, 157, 158, 159]) := List.countP_append (p := literal q) (l₁ := [153, 154, 155]) (l₂ := [156, 157, 158, 159])
  have hm := merge_right (literal (valuationOf q) (312)) (literal (valuationOf q) (314)) (countLit q [153, 154, 155]) (countLit q [156, 157, 158, 159]) (count313 q) 2 (meaning312 q) (meaning314 q) hs
  change valuationOf q 312 = false ∨ valuationOf q 314 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause759 (q : Snake 81) (h : Conditions q) : valuation q 312 = false ∨ valuation q 314 = true := counterClause759 (baseVal q)

theorem counterClause760 (q : Nat → Bool) : valuationOf q 305 = false ∨ valuationOf q 313 = true := by
  have hs : count313 q = (countLit q [153, 154, 155]) + (countLit q [156, 157, 158, 159]) := List.countP_append (p := literal q) (l₁ := [153, 154, 155]) (l₂ := [156, 157, 158, 159])
  have hm := merge_left (literal (valuationOf q) (305)) (literal (valuationOf q) (313)) (countLit q [153, 154, 155]) (countLit q [156, 157, 158, 159]) (count313 q) 1 (meaning305 q) (meaning313 q) hs
  change valuationOf q 305 = false ∨ valuationOf q 313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause760 (q : Snake 81) (h : Conditions q) : valuation q 305 = false ∨ valuation q 313 = true := counterClause760 (baseVal q)

theorem counterClause761 (q : Nat → Bool) : valuationOf q 160 = false ∨ valuationOf q 315 = true := by
  have hs : count315 q = (countLit q [160]) + (countLit q [161]) := List.countP_append (p := literal q) (l₁ := [160]) (l₂ := [161])
  have hm := merge_left (literal (valuationOf q) (160)) (literal (valuationOf q) (315)) (countLit q [160]) (countLit q [161]) (count315 q) 1 (meaning160 q) (meaning315 q) hs
  change valuationOf q 160 = false ∨ valuationOf q 315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause761 (q : Snake 81) (h : Conditions q) : valuation q 160 = false ∨ valuation q 315 = true := counterClause761 (baseVal q)

theorem counterClause762 (q : Nat → Bool) : valuationOf q 162 = false ∨ valuationOf q 317 = true := by
  have hs : count317 q = (countLit q [162]) + (countLit q [163]) := List.countP_append (p := literal q) (l₁ := [162]) (l₂ := [163])
  have hm := merge_left (literal (valuationOf q) (162)) (literal (valuationOf q) (317)) (countLit q [162]) (countLit q [163]) (count317 q) 1 (meaning162 q) (meaning317 q) hs
  change valuationOf q 162 = false ∨ valuationOf q 317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause762 (q : Snake 81) (h : Conditions q) : valuation q 162 = false ∨ valuation q 317 = true := counterClause762 (baseVal q)

theorem counterClause763 (q : Nat → Bool) : valuationOf q 317 = false ∨ valuationOf q 319 = true := by
  have hs : count319 q = (countLit q [160, 161]) + (countLit q [162, 163]) := List.countP_append (p := literal q) (l₁ := [160, 161]) (l₂ := [162, 163])
  have hm := merge_right (literal (valuationOf q) (317)) (literal (valuationOf q) (319)) (countLit q [160, 161]) (countLit q [162, 163]) (count319 q) 1 (meaning317 q) (meaning319 q) hs
  change valuationOf q 317 = false ∨ valuationOf q 319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause763 (q : Snake 81) (h : Conditions q) : valuation q 317 = false ∨ valuation q 319 = true := counterClause763 (baseVal q)

theorem counterClause764 (q : Nat → Bool) : valuationOf q 315 = false ∨ valuationOf q 319 = true := by
  have hs : count319 q = (countLit q [160, 161]) + (countLit q [162, 163]) := List.countP_append (p := literal q) (l₁ := [160, 161]) (l₂ := [162, 163])
  have hm := merge_left (literal (valuationOf q) (315)) (literal (valuationOf q) (319)) (countLit q [160, 161]) (countLit q [162, 163]) (count319 q) 1 (meaning315 q) (meaning319 q) hs
  change valuationOf q 315 = false ∨ valuationOf q 319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause764 (q : Snake 81) (h : Conditions q) : valuation q 315 = false ∨ valuation q 319 = true := counterClause764 (baseVal q)

theorem counterClause765 (q : Nat → Bool) : valuationOf q 315 = false ∨ valuationOf q 317 = false ∨ valuationOf q 320 = true := by
  have hs : count319 q = (countLit q [160, 161]) + (countLit q [162, 163]) := List.countP_append (p := literal q) (l₁ := [160, 161]) (l₂ := [162, 163])
  have hm := merge_two (literal (valuationOf q) (315)) (literal (valuationOf q) (317)) (literal (valuationOf q) (320)) (countLit q [160, 161]) (countLit q [162, 163]) (count319 q) 1 1 (meaning315 q) (meaning317 q) (meaning320 q) hs
  change valuationOf q 315 = false ∨ valuationOf q 317 = false ∨ valuationOf q 320 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause765 (q : Snake 81) (h : Conditions q) : valuation q 315 = false ∨ valuation q 317 = false ∨ valuation q 320 = true := counterClause765 (baseVal q)

theorem counterClause766 (q : Nat → Bool) : valuationOf q 167 = false ∨ valuationOf q 323 = true := by
  have hs : count323 q = (countLit q [166]) + (countLit q [167]) := List.countP_append (p := literal q) (l₁ := [166]) (l₂ := [167])
  have hm := merge_right (literal (valuationOf q) (167)) (literal (valuationOf q) (323)) (countLit q [166]) (countLit q [167]) (count323 q) 1 (meaning167 q) (meaning323 q) hs
  change valuationOf q 167 = false ∨ valuationOf q 323 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause766 (q : Snake 81) (h : Conditions q) : valuation q 167 = false ∨ valuation q 323 = true := counterClause766 (baseVal q)

theorem counterClause767 (q : Nat → Bool) : valuationOf q 323 = false ∨ valuationOf q 325 = true := by
  have hs : count325 q = (countLit q [164, 165]) + (countLit q [166, 167]) := List.countP_append (p := literal q) (l₁ := [164, 165]) (l₂ := [166, 167])
  have hm := merge_right (literal (valuationOf q) (323)) (literal (valuationOf q) (325)) (countLit q [164, 165]) (countLit q [166, 167]) (count325 q) 1 (meaning323 q) (meaning325 q) hs
  change valuationOf q 323 = false ∨ valuationOf q 325 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause767 (q : Snake 81) (h : Conditions q) : valuation q 323 = false ∨ valuation q 325 = true := counterClause767 (baseVal q)

theorem counterClause768 (q : Nat → Bool) : valuationOf q 325 = false ∨ valuationOf q 327 = true := by
  have hs : count327 q = (countLit q [160, 161, 162, 163]) + (countLit q [164, 165, 166, 167]) := List.countP_append (p := literal q) (l₁ := [160, 161, 162, 163]) (l₂ := [164, 165, 166, 167])
  have hm := merge_right (literal (valuationOf q) (325)) (literal (valuationOf q) (327)) (countLit q [160, 161, 162, 163]) (countLit q [164, 165, 166, 167]) (count327 q) 1 (meaning325 q) (meaning327 q) hs
  change valuationOf q 325 = false ∨ valuationOf q 327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause768 (q : Snake 81) (h : Conditions q) : valuation q 325 = false ∨ valuation q 327 = true := counterClause768 (baseVal q)

theorem block23 (q : Snake 81) (h : Conditions q) : B112E258.Block23 (valuation q) :=
  ⟨clause737 q h, clause738 q h, clause739 q h, clause740 q h, clause741 q h, clause742 q h, clause743 q h, clause744 q h, clause745 q h, clause746 q h, clause747 q h, clause748 q h, clause749 q h, clause750 q h, clause751 q h, clause752 q h, clause753 q h, clause754 q h, clause755 q h, clause756 q h, clause757 q h, clause758 q h, clause759 q h, clause760 q h, clause761 q h, clause762 q h, clause763 q h, clause764 q h, clause765 q h, clause766 q h, clause767 q h, clause768 q h⟩

end
end Snake9.Regrowth.E112258
