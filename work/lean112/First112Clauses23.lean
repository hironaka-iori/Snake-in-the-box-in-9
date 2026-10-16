import First112Semantics
import Dfs112FirstBooleanInputs
namespace Snake9.Regrowth.First112
noncomputable section
local instance blockDec23 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause737 (q : Snake 81) (h : Conditions q) : valuation q 257 = false ∨ valuation q 261 = true := by
  have hs : count261 q = (countLit q [130, 131]) + (countLit q [132, 133]) := List.countP_append (p := literal (baseVal q)) (l₁ := [130, 131]) (l₂ := [132, 133])
  have hm := merge_left (literal (valuation q) (257)) (literal (valuation q) (261)) (countLit q [130, 131]) (countLit q [132, 133]) (count261 q) 1 (meaning257 q) (meaning261 q) hs
  change valuation q 257 = false ∨ valuation q 261 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause738 (q : Snake 81) (h : Conditions q) : valuation q 136 = false ∨ valuation q 265 = true := by
  have hs : count265 q = (countLit q [136]) + (countLit q [137]) := List.countP_append (p := literal (baseVal q)) (l₁ := [136]) (l₂ := [137])
  have hm := merge_left (literal (valuation q) (136)) (literal (valuation q) (265)) (countLit q [136]) (countLit q [137]) (count265 q) 1 (meaning136 q) (meaning265 q) hs
  change valuation q 136 = false ∨ valuation q 265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause739 (q : Snake 81) (h : Conditions q) : valuation q 265 = false ∨ valuation q 267 = true := by
  have hs : count267 q = (countLit q [134, 135]) + (countLit q [136, 137]) := List.countP_append (p := literal (baseVal q)) (l₁ := [134, 135]) (l₂ := [136, 137])
  have hm := merge_right (literal (valuation q) (265)) (literal (valuation q) (267)) (countLit q [134, 135]) (countLit q [136, 137]) (count267 q) 1 (meaning265 q) (meaning267 q) hs
  change valuation q 265 = false ∨ valuation q 267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause740 (q : Snake 81) (h : Conditions q) : valuation q 267 = false ∨ valuation q 269 = true := by
  have hs : count269 q = (countLit q [130, 131, 132, 133]) + (countLit q [134, 135, 136, 137]) := List.countP_append (p := literal (baseVal q)) (l₁ := [130, 131, 132, 133]) (l₂ := [134, 135, 136, 137])
  have hm := merge_right (literal (valuation q) (267)) (literal (valuation q) (269)) (countLit q [130, 131, 132, 133]) (countLit q [134, 135, 136, 137]) (count269 q) 1 (meaning267 q) (meaning269 q) hs
  change valuation q 267 = false ∨ valuation q 269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause741 (q : Snake 81) (h : Conditions q) : valuation q 261 = false ∨ valuation q 269 = true := by
  have hs : count269 q = (countLit q [130, 131, 132, 133]) + (countLit q [134, 135, 136, 137]) := List.countP_append (p := literal (baseVal q)) (l₁ := [130, 131, 132, 133]) (l₂ := [134, 135, 136, 137])
  have hm := merge_left (literal (valuation q) (261)) (literal (valuation q) (269)) (countLit q [130, 131, 132, 133]) (countLit q [134, 135, 136, 137]) (count269 q) 1 (meaning261 q) (meaning269 q) hs
  change valuation q 261 = false ∨ valuation q 269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause742 (q : Snake 81) (h : Conditions q) : valuation q 261 = false ∨ valuation q 267 = false ∨ valuation q 270 = true := by
  have hs : count269 q = (countLit q [130, 131, 132, 133]) + (countLit q [134, 135, 136, 137]) := List.countP_append (p := literal (baseVal q)) (l₁ := [130, 131, 132, 133]) (l₂ := [134, 135, 136, 137])
  have hm := merge_two (literal (valuation q) (261)) (literal (valuation q) (267)) (literal (valuation q) (270)) (countLit q [130, 131, 132, 133]) (countLit q [134, 135, 136, 137]) (count269 q) 1 1 (meaning261 q) (meaning267 q) (meaning270 q) hs
  change valuation q 261 = false ∨ valuation q 267 = false ∨ valuation q 270 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause743 (q : Snake 81) (h : Conditions q) : valuation q 269 = false ∨ valuation q 271 = true := by
  have hs : count271 q = (countLit q [123, 124, 125, 126, 127, 128, 129]) + (countLit q [130, 131, 132, 133, 134, 135, 136, 137]) := List.countP_append (p := literal (baseVal q)) (l₁ := [123, 124, 125, 126, 127, 128, 129]) (l₂ := [130, 131, 132, 133, 134, 135, 136, 137])
  have hm := merge_right (literal (valuation q) (269)) (literal (valuation q) (271)) (countLit q [123, 124, 125, 126, 127, 128, 129]) (countLit q [130, 131, 132, 133, 134, 135, 136, 137]) (count271 q) 1 (meaning269 q) (meaning271 q) hs
  change valuation q 269 = false ∨ valuation q 271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause744 (q : Snake 81) (h : Conditions q) : valuation q 270 = false ∨ valuation q 272 = true := by
  have hs : count271 q = (countLit q [123, 124, 125, 126, 127, 128, 129]) + (countLit q [130, 131, 132, 133, 134, 135, 136, 137]) := List.countP_append (p := literal (baseVal q)) (l₁ := [123, 124, 125, 126, 127, 128, 129]) (l₂ := [130, 131, 132, 133, 134, 135, 136, 137])
  have hm := merge_right (literal (valuation q) (270)) (literal (valuation q) (272)) (countLit q [123, 124, 125, 126, 127, 128, 129]) (countLit q [130, 131, 132, 133, 134, 135, 136, 137]) (count271 q) 2 (meaning270 q) (meaning272 q) hs
  change valuation q 270 = false ∨ valuation q 272 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause745 (q : Snake 81) (h : Conditions q) : valuation q 255 = false ∨ valuation q 271 = true := by
  have hs : count271 q = (countLit q [123, 124, 125, 126, 127, 128, 129]) + (countLit q [130, 131, 132, 133, 134, 135, 136, 137]) := List.countP_append (p := literal (baseVal q)) (l₁ := [123, 124, 125, 126, 127, 128, 129]) (l₂ := [130, 131, 132, 133, 134, 135, 136, 137])
  have hm := merge_left (literal (valuation q) (255)) (literal (valuation q) (271)) (countLit q [123, 124, 125, 126, 127, 128, 129]) (countLit q [130, 131, 132, 133, 134, 135, 136, 137]) (count271 q) 1 (meaning255 q) (meaning271 q) hs
  change valuation q 255 = false ∨ valuation q 271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause746 (q : Snake 81) (h : Conditions q) : valuation q 255 = false ∨ valuation q 269 = false ∨ valuation q 272 = true := by
  have hs : count271 q = (countLit q [123, 124, 125, 126, 127, 128, 129]) + (countLit q [130, 131, 132, 133, 134, 135, 136, 137]) := List.countP_append (p := literal (baseVal q)) (l₁ := [123, 124, 125, 126, 127, 128, 129]) (l₂ := [130, 131, 132, 133, 134, 135, 136, 137])
  have hm := merge_two (literal (valuation q) (255)) (literal (valuation q) (269)) (literal (valuation q) (272)) (countLit q [123, 124, 125, 126, 127, 128, 129]) (countLit q [130, 131, 132, 133, 134, 135, 136, 137]) (count271 q) 1 1 (meaning255 q) (meaning269 q) (meaning272 q) hs
  change valuation q 255 = false ∨ valuation q 269 = false ∨ valuation q 272 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause747 (q : Snake 81) (h : Conditions q) : valuation q 256 = false ∨ valuation q 272 = true := by
  have hs : count271 q = (countLit q [123, 124, 125, 126, 127, 128, 129]) + (countLit q [130, 131, 132, 133, 134, 135, 136, 137]) := List.countP_append (p := literal (baseVal q)) (l₁ := [123, 124, 125, 126, 127, 128, 129]) (l₂ := [130, 131, 132, 133, 134, 135, 136, 137])
  have hm := merge_left (literal (valuation q) (256)) (literal (valuation q) (272)) (countLit q [123, 124, 125, 126, 127, 128, 129]) (countLit q [130, 131, 132, 133, 134, 135, 136, 137]) (count271 q) 2 (meaning256 q) (meaning272 q) hs
  change valuation q 256 = false ∨ valuation q 272 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause748 (q : Snake 81) (h : Conditions q) : valuation q 139 = false ∨ valuation q 273 = true := by
  have hs : count273 q = (countLit q [139]) + (countLit q [140]) := List.countP_append (p := literal (baseVal q)) (l₁ := [139]) (l₂ := [140])
  have hm := merge_left (literal (valuation q) (139)) (literal (valuation q) (273)) (countLit q [139]) (countLit q [140]) (count273 q) 1 (meaning139 q) (meaning273 q) hs
  change valuation q 139 = false ∨ valuation q 273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause749 (q : Snake 81) (h : Conditions q) : valuation q 273 = false ∨ valuation q 275 = true := by
  have hs : count275 q = (countLit q [138]) + (countLit q [139, 140]) := List.countP_append (p := literal (baseVal q)) (l₁ := [138]) (l₂ := [139, 140])
  have hm := merge_right (literal (valuation q) (273)) (literal (valuation q) (275)) (countLit q [138]) (countLit q [139, 140]) (count275 q) 1 (meaning273 q) (meaning275 q) hs
  change valuation q 273 = false ∨ valuation q 275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause750 (q : Snake 81) (h : Conditions q) : valuation q 138 = false ∨ valuation q 275 = true := by
  have hs : count275 q = (countLit q [138]) + (countLit q [139, 140]) := List.countP_append (p := literal (baseVal q)) (l₁ := [138]) (l₂ := [139, 140])
  have hm := merge_left (literal (valuation q) (138)) (literal (valuation q) (275)) (countLit q [138]) (countLit q [139, 140]) (count275 q) 1 (meaning138 q) (meaning275 q) hs
  change valuation q 138 = false ∨ valuation q 275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause751 (q : Snake 81) (h : Conditions q) : valuation q 142 = false ∨ valuation q 277 = true := by
  have hs : count277 q = (countLit q [141]) + (countLit q [142]) := List.countP_append (p := literal (baseVal q)) (l₁ := [141]) (l₂ := [142])
  have hm := merge_right (literal (valuation q) (142)) (literal (valuation q) (277)) (countLit q [141]) (countLit q [142]) (count277 q) 1 (meaning142 q) (meaning277 q) hs
  change valuation q 142 = false ∨ valuation q 277 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause752 (q : Snake 81) (h : Conditions q) : valuation q 144 = false ∨ valuation q 279 = true := by
  have hs : count279 q = (countLit q [143]) + (countLit q [144]) := List.countP_append (p := literal (baseVal q)) (l₁ := [143]) (l₂ := [144])
  have hm := merge_right (literal (valuation q) (144)) (literal (valuation q) (279)) (countLit q [143]) (countLit q [144]) (count279 q) 1 (meaning144 q) (meaning279 q) hs
  change valuation q 144 = false ∨ valuation q 279 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause753 (q : Snake 81) (h : Conditions q) : valuation q 279 = false ∨ valuation q 281 = true := by
  have hs : count281 q = (countLit q [141, 142]) + (countLit q [143, 144]) := List.countP_append (p := literal (baseVal q)) (l₁ := [141, 142]) (l₂ := [143, 144])
  have hm := merge_right (literal (valuation q) (279)) (literal (valuation q) (281)) (countLit q [141, 142]) (countLit q [143, 144]) (count281 q) 1 (meaning279 q) (meaning281 q) hs
  change valuation q 279 = false ∨ valuation q 281 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause754 (q : Snake 81) (h : Conditions q) : valuation q 277 = false ∨ valuation q 281 = true := by
  have hs : count281 q = (countLit q [141, 142]) + (countLit q [143, 144]) := List.countP_append (p := literal (baseVal q)) (l₁ := [141, 142]) (l₂ := [143, 144])
  have hm := merge_left (literal (valuation q) (277)) (literal (valuation q) (281)) (countLit q [141, 142]) (countLit q [143, 144]) (count281 q) 1 (meaning277 q) (meaning281 q) hs
  change valuation q 277 = false ∨ valuation q 281 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause755 (q : Snake 81) (h : Conditions q) : valuation q 281 = false ∨ valuation q 283 = true := by
  have hs : count283 q = (countLit q [138, 139, 140]) + (countLit q [141, 142, 143, 144]) := List.countP_append (p := literal (baseVal q)) (l₁ := [138, 139, 140]) (l₂ := [141, 142, 143, 144])
  have hm := merge_right (literal (valuation q) (281)) (literal (valuation q) (283)) (countLit q [138, 139, 140]) (countLit q [141, 142, 143, 144]) (count283 q) 1 (meaning281 q) (meaning283 q) hs
  change valuation q 281 = false ∨ valuation q 283 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause756 (q : Snake 81) (h : Conditions q) : valuation q 275 = false ∨ valuation q 283 = true := by
  have hs : count283 q = (countLit q [138, 139, 140]) + (countLit q [141, 142, 143, 144]) := List.countP_append (p := literal (baseVal q)) (l₁ := [138, 139, 140]) (l₂ := [141, 142, 143, 144])
  have hm := merge_left (literal (valuation q) (275)) (literal (valuation q) (283)) (countLit q [138, 139, 140]) (countLit q [141, 142, 143, 144]) (count283 q) 1 (meaning275 q) (meaning283 q) hs
  change valuation q 275 = false ∨ valuation q 283 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause757 (q : Snake 81) (h : Conditions q) : valuation q 147 = false ∨ valuation q 287 = true := by
  have hs : count287 q = (countLit q [147]) + (countLit q [148]) := List.countP_append (p := literal (baseVal q)) (l₁ := [147]) (l₂ := [148])
  have hm := merge_left (literal (valuation q) (147)) (literal (valuation q) (287)) (countLit q [147]) (countLit q [148]) (count287 q) 1 (meaning147 q) (meaning287 q) hs
  change valuation q 147 = false ∨ valuation q 287 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause758 (q : Snake 81) (h : Conditions q) : valuation q 287 = false ∨ valuation q 289 = true := by
  have hs : count289 q = (countLit q [145, 146]) + (countLit q [147, 148]) := List.countP_append (p := literal (baseVal q)) (l₁ := [145, 146]) (l₂ := [147, 148])
  have hm := merge_right (literal (valuation q) (287)) (literal (valuation q) (289)) (countLit q [145, 146]) (countLit q [147, 148]) (count289 q) 1 (meaning287 q) (meaning289 q) hs
  change valuation q 287 = false ∨ valuation q 289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause759 (q : Snake 81) (h : Conditions q) : valuation q 150 = false ∨ valuation q 291 = true := by
  have hs : count291 q = (countLit q [149]) + (countLit q [150]) := List.countP_append (p := literal (baseVal q)) (l₁ := [149]) (l₂ := [150])
  have hm := merge_right (literal (valuation q) (150)) (literal (valuation q) (291)) (countLit q [149]) (countLit q [150]) (count291 q) 1 (meaning150 q) (meaning291 q) hs
  change valuation q 150 = false ∨ valuation q 291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause760 (q : Snake 81) (h : Conditions q) : valuation q 152 = false ∨ valuation q 293 = true := by
  have hs : count293 q = (countLit q [151]) + (countLit q [152]) := List.countP_append (p := literal (baseVal q)) (l₁ := [151]) (l₂ := [152])
  have hm := merge_right (literal (valuation q) (152)) (literal (valuation q) (293)) (countLit q [151]) (countLit q [152]) (count293 q) 1 (meaning152 q) (meaning293 q) hs
  change valuation q 152 = false ∨ valuation q 293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause761 (q : Snake 81) (h : Conditions q) : valuation q 151 = false ∨ valuation q 293 = true := by
  have hs : count293 q = (countLit q [151]) + (countLit q [152]) := List.countP_append (p := literal (baseVal q)) (l₁ := [151]) (l₂ := [152])
  have hm := merge_left (literal (valuation q) (151)) (literal (valuation q) (293)) (countLit q [151]) (countLit q [152]) (count293 q) 1 (meaning151 q) (meaning293 q) hs
  change valuation q 151 = false ∨ valuation q 293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause762 (q : Snake 81) (h : Conditions q) : valuation q 293 = false ∨ valuation q 295 = true := by
  have hs : count295 q = (countLit q [149, 150]) + (countLit q [151, 152]) := List.countP_append (p := literal (baseVal q)) (l₁ := [149, 150]) (l₂ := [151, 152])
  have hm := merge_right (literal (valuation q) (293)) (literal (valuation q) (295)) (countLit q [149, 150]) (countLit q [151, 152]) (count295 q) 1 (meaning293 q) (meaning295 q) hs
  change valuation q 293 = false ∨ valuation q 295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause763 (q : Snake 81) (h : Conditions q) : valuation q 291 = false ∨ valuation q 295 = true := by
  have hs : count295 q = (countLit q [149, 150]) + (countLit q [151, 152]) := List.countP_append (p := literal (baseVal q)) (l₁ := [149, 150]) (l₂ := [151, 152])
  have hm := merge_left (literal (valuation q) (291)) (literal (valuation q) (295)) (countLit q [149, 150]) (countLit q [151, 152]) (count295 q) 1 (meaning291 q) (meaning295 q) hs
  change valuation q 291 = false ∨ valuation q 295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause764 (q : Snake 81) (h : Conditions q) : valuation q 295 = false ∨ valuation q 297 = true := by
  have hs : count297 q = (countLit q [145, 146, 147, 148]) + (countLit q [149, 150, 151, 152]) := List.countP_append (p := literal (baseVal q)) (l₁ := [145, 146, 147, 148]) (l₂ := [149, 150, 151, 152])
  have hm := merge_right (literal (valuation q) (295)) (literal (valuation q) (297)) (countLit q [145, 146, 147, 148]) (countLit q [149, 150, 151, 152]) (count297 q) 1 (meaning295 q) (meaning297 q) hs
  change valuation q 295 = false ∨ valuation q 297 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause765 (q : Snake 81) (h : Conditions q) : valuation q 289 = false ∨ valuation q 297 = true := by
  have hs : count297 q = (countLit q [145, 146, 147, 148]) + (countLit q [149, 150, 151, 152]) := List.countP_append (p := literal (baseVal q)) (l₁ := [145, 146, 147, 148]) (l₂ := [149, 150, 151, 152])
  have hm := merge_left (literal (valuation q) (289)) (literal (valuation q) (297)) (countLit q [145, 146, 147, 148]) (countLit q [149, 150, 151, 152]) (count297 q) 1 (meaning289 q) (meaning297 q) hs
  change valuation q 289 = false ∨ valuation q 297 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause766 (q : Snake 81) (h : Conditions q) : valuation q 297 = false ∨ valuation q 299 = true := by
  have hs : count299 q = (countLit q [138, 139, 140, 141, 142, 143, 144]) + (countLit q [145, 146, 147, 148, 149, 150, 151, 152]) := List.countP_append (p := literal (baseVal q)) (l₁ := [138, 139, 140, 141, 142, 143, 144]) (l₂ := [145, 146, 147, 148, 149, 150, 151, 152])
  have hm := merge_right (literal (valuation q) (297)) (literal (valuation q) (299)) (countLit q [138, 139, 140, 141, 142, 143, 144]) (countLit q [145, 146, 147, 148, 149, 150, 151, 152]) (count299 q) 1 (meaning297 q) (meaning299 q) hs
  change valuation q 297 = false ∨ valuation q 299 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause767 (q : Snake 81) (h : Conditions q) : valuation q 283 = false ∨ valuation q 299 = true := by
  have hs : count299 q = (countLit q [138, 139, 140, 141, 142, 143, 144]) + (countLit q [145, 146, 147, 148, 149, 150, 151, 152]) := List.countP_append (p := literal (baseVal q)) (l₁ := [138, 139, 140, 141, 142, 143, 144]) (l₂ := [145, 146, 147, 148, 149, 150, 151, 152])
  have hm := merge_left (literal (valuation q) (283)) (literal (valuation q) (299)) (countLit q [138, 139, 140, 141, 142, 143, 144]) (countLit q [145, 146, 147, 148, 149, 150, 151, 152]) (count299 q) 1 (meaning283 q) (meaning299 q) hs
  change valuation q 283 = false ∨ valuation q 299 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause768 (q : Snake 81) (h : Conditions q) : valuation q 299 = false ∨ valuation q 301 = true := by
  have hs : count301 q = (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) + (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) := List.countP_append (p := literal (baseVal q)) (l₁ := [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (l₂ := [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152])
  have hm := merge_right (literal (valuation q) (299)) (literal (valuation q) (301)) (countLit q [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]) (countLit q [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]) (count301 q) 1 (meaning299 q) (meaning301 q) hs
  change valuation q 299 = false ∨ valuation q 301 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem block23 (q : Snake 81) (h : Conditions q) : Dfs112FirstBoolean.Block23 (valuation q) :=
  ⟨clause737 q h, clause738 q h, clause739 q h, clause740 q h, clause741 q h, clause742 q h, clause743 q h, clause744 q h, clause745 q h, clause746 q h, clause747 q h, clause748 q h, clause749 q h, clause750 q h, clause751 q h, clause752 q h, clause753 q h, clause754 q h, clause755 q h, clause756 q h, clause757 q h, clause758 q h, clause759 q h, clause760 q h, clause761 q h, clause762 q h, clause763 q h, clause764 q h, clause765 q h, clause766 q h, clause767 q h, clause768 q h⟩

end
end Snake9.Regrowth.First112
