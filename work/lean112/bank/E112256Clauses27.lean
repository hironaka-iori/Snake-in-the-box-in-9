import E112256Semantics
import B112E256Inputs
namespace Snake9.Regrowth.E112256
noncomputable section
local instance blockDec27 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause865 (q : Nat → Bool) : valuationOf q 280 = false ∨ valuationOf q 282 = true := by
  have hs : count281 q = (countLit q [128, 129, 130, 131, 132, 133, 134]) + (countLit q [135, 136, 137, 138, 139, 140, 141, 142]) := List.countP_append (p := literal q) (l₁ := [128, 129, 130, 131, 132, 133, 134]) (l₂ := [135, 136, 137, 138, 139, 140, 141, 142])
  have hm := merge_right (literal (valuationOf q) (280)) (literal (valuationOf q) (282)) (countLit q [128, 129, 130, 131, 132, 133, 134]) (countLit q [135, 136, 137, 138, 139, 140, 141, 142]) (count281 q) 2 (meaning280 q) (meaning282 q) hs
  change valuationOf q 280 = false ∨ valuationOf q 282 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause865 (q : Snake 81) (h : Conditions q) : valuation q 280 = false ∨ valuation q 282 = true := counterClause865 (baseVal q)

theorem counterClause866 (q : Nat → Bool) : valuationOf q 265 = false ∨ valuationOf q 281 = true := by
  have hs : count281 q = (countLit q [128, 129, 130, 131, 132, 133, 134]) + (countLit q [135, 136, 137, 138, 139, 140, 141, 142]) := List.countP_append (p := literal q) (l₁ := [128, 129, 130, 131, 132, 133, 134]) (l₂ := [135, 136, 137, 138, 139, 140, 141, 142])
  have hm := merge_left (literal (valuationOf q) (265)) (literal (valuationOf q) (281)) (countLit q [128, 129, 130, 131, 132, 133, 134]) (countLit q [135, 136, 137, 138, 139, 140, 141, 142]) (count281 q) 1 (meaning265 q) (meaning281 q) hs
  change valuationOf q 265 = false ∨ valuationOf q 281 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause866 (q : Snake 81) (h : Conditions q) : valuation q 265 = false ∨ valuation q 281 = true := counterClause866 (baseVal q)

theorem counterClause867 (q : Nat → Bool) : valuationOf q 265 = false ∨ valuationOf q 279 = false ∨ valuationOf q 282 = true := by
  have hs : count281 q = (countLit q [128, 129, 130, 131, 132, 133, 134]) + (countLit q [135, 136, 137, 138, 139, 140, 141, 142]) := List.countP_append (p := literal q) (l₁ := [128, 129, 130, 131, 132, 133, 134]) (l₂ := [135, 136, 137, 138, 139, 140, 141, 142])
  have hm := merge_two (literal (valuationOf q) (265)) (literal (valuationOf q) (279)) (literal (valuationOf q) (282)) (countLit q [128, 129, 130, 131, 132, 133, 134]) (countLit q [135, 136, 137, 138, 139, 140, 141, 142]) (count281 q) 1 1 (meaning265 q) (meaning279 q) (meaning282 q) hs
  change valuationOf q 265 = false ∨ valuationOf q 279 = false ∨ valuationOf q 282 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause867 (q : Snake 81) (h : Conditions q) : valuation q 265 = false ∨ valuation q 279 = false ∨ valuation q 282 = true := counterClause867 (baseVal q)

theorem counterClause868 (q : Nat → Bool) : valuationOf q 266 = false ∨ valuationOf q 282 = true := by
  have hs : count281 q = (countLit q [128, 129, 130, 131, 132, 133, 134]) + (countLit q [135, 136, 137, 138, 139, 140, 141, 142]) := List.countP_append (p := literal q) (l₁ := [128, 129, 130, 131, 132, 133, 134]) (l₂ := [135, 136, 137, 138, 139, 140, 141, 142])
  have hm := merge_left (literal (valuationOf q) (266)) (literal (valuationOf q) (282)) (countLit q [128, 129, 130, 131, 132, 133, 134]) (countLit q [135, 136, 137, 138, 139, 140, 141, 142]) (count281 q) 2 (meaning266 q) (meaning282 q) hs
  change valuationOf q 266 = false ∨ valuationOf q 282 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause868 (q : Snake 81) (h : Conditions q) : valuation q 266 = false ∨ valuation q 282 = true := counterClause868 (baseVal q)

theorem counterClause869 (q : Nat → Bool) : valuationOf q 146 = false ∨ valuationOf q 285 = true := by
  have hs : count285 q = (countLit q [145]) + (countLit q [146]) := List.countP_append (p := literal q) (l₁ := [145]) (l₂ := [146])
  have hm := merge_right (literal (valuationOf q) (146)) (literal (valuationOf q) (285)) (countLit q [145]) (countLit q [146]) (count285 q) 1 (meaning146 q) (meaning285 q) hs
  change valuationOf q 146 = false ∨ valuationOf q 285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause869 (q : Snake 81) (h : Conditions q) : valuation q 146 = false ∨ valuation q 285 = true := counterClause869 (baseVal q)

theorem counterClause870 (q : Nat → Bool) : valuationOf q 145 = false ∨ valuationOf q 285 = true := by
  have hs : count285 q = (countLit q [145]) + (countLit q [146]) := List.countP_append (p := literal q) (l₁ := [145]) (l₂ := [146])
  have hm := merge_left (literal (valuationOf q) (145)) (literal (valuationOf q) (285)) (countLit q [145]) (countLit q [146]) (count285 q) 1 (meaning145 q) (meaning285 q) hs
  change valuationOf q 145 = false ∨ valuationOf q 285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause870 (q : Snake 81) (h : Conditions q) : valuation q 145 = false ∨ valuation q 285 = true := counterClause870 (baseVal q)

theorem counterClause871 (q : Nat → Bool) : valuationOf q 145 = false ∨ valuationOf q 146 = false ∨ valuationOf q 286 = true := by
  have hs : count285 q = (countLit q [145]) + (countLit q [146]) := List.countP_append (p := literal q) (l₁ := [145]) (l₂ := [146])
  have hm := merge_two (literal (valuationOf q) (145)) (literal (valuationOf q) (146)) (literal (valuationOf q) (286)) (countLit q [145]) (countLit q [146]) (count285 q) 1 1 (meaning145 q) (meaning146 q) (meaning286 q) hs
  change valuationOf q 145 = false ∨ valuationOf q 146 = false ∨ valuationOf q 286 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause871 (q : Snake 81) (h : Conditions q) : valuation q 145 = false ∨ valuation q 146 = false ∨ valuation q 286 = true := counterClause871 (baseVal q)

theorem counterClause872 (q : Nat → Bool) : valuationOf q 285 = false ∨ valuationOf q 287 = true := by
  have hs : count287 q = (countLit q [143, 144]) + (countLit q [145, 146]) := List.countP_append (p := literal q) (l₁ := [143, 144]) (l₂ := [145, 146])
  have hm := merge_right (literal (valuationOf q) (285)) (literal (valuationOf q) (287)) (countLit q [143, 144]) (countLit q [145, 146]) (count287 q) 1 (meaning285 q) (meaning287 q) hs
  change valuationOf q 285 = false ∨ valuationOf q 287 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause872 (q : Snake 81) (h : Conditions q) : valuation q 285 = false ∨ valuation q 287 = true := counterClause872 (baseVal q)

theorem counterClause873 (q : Nat → Bool) : valuationOf q 286 = false ∨ valuationOf q 288 = true := by
  have hs : count287 q = (countLit q [143, 144]) + (countLit q [145, 146]) := List.countP_append (p := literal q) (l₁ := [143, 144]) (l₂ := [145, 146])
  have hm := merge_right (literal (valuationOf q) (286)) (literal (valuationOf q) (288)) (countLit q [143, 144]) (countLit q [145, 146]) (count287 q) 2 (meaning286 q) (meaning288 q) hs
  change valuationOf q 286 = false ∨ valuationOf q 288 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause873 (q : Snake 81) (h : Conditions q) : valuation q 286 = false ∨ valuation q 288 = true := counterClause873 (baseVal q)

theorem counterClause874 (q : Nat → Bool) : valuationOf q 148 = false ∨ valuationOf q 289 = true := by
  have hs : count289 q = (countLit q [147]) + (countLit q [148]) := List.countP_append (p := literal q) (l₁ := [147]) (l₂ := [148])
  have hm := merge_right (literal (valuationOf q) (148)) (literal (valuationOf q) (289)) (countLit q [147]) (countLit q [148]) (count289 q) 1 (meaning148 q) (meaning289 q) hs
  change valuationOf q 148 = false ∨ valuationOf q 289 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause874 (q : Snake 81) (h : Conditions q) : valuation q 148 = false ∨ valuation q 289 = true := counterClause874 (baseVal q)

theorem counterClause875 (q : Nat → Bool) : valuationOf q 150 = false ∨ valuationOf q 291 = true := by
  have hs : count291 q = (countLit q [149]) + (countLit q [150]) := List.countP_append (p := literal q) (l₁ := [149]) (l₂ := [150])
  have hm := merge_right (literal (valuationOf q) (150)) (literal (valuationOf q) (291)) (countLit q [149]) (countLit q [150]) (count291 q) 1 (meaning150 q) (meaning291 q) hs
  change valuationOf q 150 = false ∨ valuationOf q 291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause875 (q : Snake 81) (h : Conditions q) : valuation q 150 = false ∨ valuation q 291 = true := counterClause875 (baseVal q)

theorem counterClause876 (q : Nat → Bool) : valuationOf q 291 = false ∨ valuationOf q 293 = true := by
  have hs : count293 q = (countLit q [147, 148]) + (countLit q [149, 150]) := List.countP_append (p := literal q) (l₁ := [147, 148]) (l₂ := [149, 150])
  have hm := merge_right (literal (valuationOf q) (291)) (literal (valuationOf q) (293)) (countLit q [147, 148]) (countLit q [149, 150]) (count293 q) 1 (meaning291 q) (meaning293 q) hs
  change valuationOf q 291 = false ∨ valuationOf q 293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause876 (q : Snake 81) (h : Conditions q) : valuation q 291 = false ∨ valuation q 293 = true := counterClause876 (baseVal q)

theorem counterClause877 (q : Nat → Bool) : valuationOf q 289 = false ∨ valuationOf q 293 = true := by
  have hs : count293 q = (countLit q [147, 148]) + (countLit q [149, 150]) := List.countP_append (p := literal q) (l₁ := [147, 148]) (l₂ := [149, 150])
  have hm := merge_left (literal (valuationOf q) (289)) (literal (valuationOf q) (293)) (countLit q [147, 148]) (countLit q [149, 150]) (count293 q) 1 (meaning289 q) (meaning293 q) hs
  change valuationOf q 289 = false ∨ valuationOf q 293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause877 (q : Snake 81) (h : Conditions q) : valuation q 289 = false ∨ valuation q 293 = true := counterClause877 (baseVal q)

theorem counterClause878 (q : Nat → Bool) : valuationOf q 289 = false ∨ valuationOf q 291 = false ∨ valuationOf q 294 = true := by
  have hs : count293 q = (countLit q [147, 148]) + (countLit q [149, 150]) := List.countP_append (p := literal q) (l₁ := [147, 148]) (l₂ := [149, 150])
  have hm := merge_two (literal (valuationOf q) (289)) (literal (valuationOf q) (291)) (literal (valuationOf q) (294)) (countLit q [147, 148]) (countLit q [149, 150]) (count293 q) 1 1 (meaning289 q) (meaning291 q) (meaning294 q) hs
  change valuationOf q 289 = false ∨ valuationOf q 291 = false ∨ valuationOf q 294 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause878 (q : Snake 81) (h : Conditions q) : valuation q 289 = false ∨ valuation q 291 = false ∨ valuation q 294 = true := counterClause878 (baseVal q)

theorem counterClause879 (q : Nat → Bool) : valuationOf q 293 = false ∨ valuationOf q 295 = true := by
  have hs : count295 q = (countLit q [143, 144, 145, 146]) + (countLit q [147, 148, 149, 150]) := List.countP_append (p := literal q) (l₁ := [143, 144, 145, 146]) (l₂ := [147, 148, 149, 150])
  have hm := merge_right (literal (valuationOf q) (293)) (literal (valuationOf q) (295)) (countLit q [143, 144, 145, 146]) (countLit q [147, 148, 149, 150]) (count295 q) 1 (meaning293 q) (meaning295 q) hs
  change valuationOf q 293 = false ∨ valuationOf q 295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause879 (q : Snake 81) (h : Conditions q) : valuation q 293 = false ∨ valuation q 295 = true := counterClause879 (baseVal q)

theorem counterClause880 (q : Nat → Bool) : valuationOf q 294 = false ∨ valuationOf q 296 = true := by
  have hs : count295 q = (countLit q [143, 144, 145, 146]) + (countLit q [147, 148, 149, 150]) := List.countP_append (p := literal q) (l₁ := [143, 144, 145, 146]) (l₂ := [147, 148, 149, 150])
  have hm := merge_right (literal (valuationOf q) (294)) (literal (valuationOf q) (296)) (countLit q [143, 144, 145, 146]) (countLit q [147, 148, 149, 150]) (count295 q) 2 (meaning294 q) (meaning296 q) hs
  change valuationOf q 294 = false ∨ valuationOf q 296 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause880 (q : Snake 81) (h : Conditions q) : valuation q 294 = false ∨ valuation q 296 = true := counterClause880 (baseVal q)

theorem counterClause881 (q : Nat → Bool) : valuationOf q 287 = false ∨ valuationOf q 295 = true := by
  have hs : count295 q = (countLit q [143, 144, 145, 146]) + (countLit q [147, 148, 149, 150]) := List.countP_append (p := literal q) (l₁ := [143, 144, 145, 146]) (l₂ := [147, 148, 149, 150])
  have hm := merge_left (literal (valuationOf q) (287)) (literal (valuationOf q) (295)) (countLit q [143, 144, 145, 146]) (countLit q [147, 148, 149, 150]) (count295 q) 1 (meaning287 q) (meaning295 q) hs
  change valuationOf q 287 = false ∨ valuationOf q 295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause881 (q : Snake 81) (h : Conditions q) : valuation q 287 = false ∨ valuation q 295 = true := counterClause881 (baseVal q)

theorem counterClause882 (q : Nat → Bool) : valuationOf q 287 = false ∨ valuationOf q 293 = false ∨ valuationOf q 296 = true := by
  have hs : count295 q = (countLit q [143, 144, 145, 146]) + (countLit q [147, 148, 149, 150]) := List.countP_append (p := literal q) (l₁ := [143, 144, 145, 146]) (l₂ := [147, 148, 149, 150])
  have hm := merge_two (literal (valuationOf q) (287)) (literal (valuationOf q) (293)) (literal (valuationOf q) (296)) (countLit q [143, 144, 145, 146]) (countLit q [147, 148, 149, 150]) (count295 q) 1 1 (meaning287 q) (meaning293 q) (meaning296 q) hs
  change valuationOf q 287 = false ∨ valuationOf q 293 = false ∨ valuationOf q 296 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause882 (q : Snake 81) (h : Conditions q) : valuation q 287 = false ∨ valuation q 293 = false ∨ valuation q 296 = true := counterClause882 (baseVal q)

theorem counterClause883 (q : Nat → Bool) : valuationOf q 288 = false ∨ valuationOf q 296 = true := by
  have hs : count295 q = (countLit q [143, 144, 145, 146]) + (countLit q [147, 148, 149, 150]) := List.countP_append (p := literal q) (l₁ := [143, 144, 145, 146]) (l₂ := [147, 148, 149, 150])
  have hm := merge_left (literal (valuationOf q) (288)) (literal (valuationOf q) (296)) (countLit q [143, 144, 145, 146]) (countLit q [147, 148, 149, 150]) (count295 q) 2 (meaning288 q) (meaning296 q) hs
  change valuationOf q 288 = false ∨ valuationOf q 296 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause883 (q : Snake 81) (h : Conditions q) : valuation q 288 = false ∨ valuation q 296 = true := counterClause883 (baseVal q)

theorem counterClause884 (q : Nat → Bool) : valuationOf q 152 = false ∨ valuationOf q 297 = true := by
  have hs : count297 q = (countLit q [151]) + (countLit q [152]) := List.countP_append (p := literal q) (l₁ := [151]) (l₂ := [152])
  have hm := merge_right (literal (valuationOf q) (152)) (literal (valuationOf q) (297)) (countLit q [151]) (countLit q [152]) (count297 q) 1 (meaning152 q) (meaning297 q) hs
  change valuationOf q 152 = false ∨ valuationOf q 297 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause884 (q : Snake 81) (h : Conditions q) : valuation q 152 = false ∨ valuation q 297 = true := counterClause884 (baseVal q)

theorem counterClause885 (q : Nat → Bool) : valuationOf q 297 = false ∨ valuationOf q 301 = true := by
  have hs : count301 q = (countLit q [151, 152]) + (countLit q [153, 154]) := List.countP_append (p := literal q) (l₁ := [151, 152]) (l₂ := [153, 154])
  have hm := merge_left (literal (valuationOf q) (297)) (literal (valuationOf q) (301)) (countLit q [151, 152]) (countLit q [153, 154]) (count301 q) 1 (meaning297 q) (meaning301 q) hs
  change valuationOf q 297 = false ∨ valuationOf q 301 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause885 (q : Snake 81) (h : Conditions q) : valuation q 297 = false ∨ valuation q 301 = true := counterClause885 (baseVal q)

theorem counterClause886 (q : Nat → Bool) : valuationOf q 155 = false ∨ valuationOf q 303 = true := by
  have hs : count303 q = (countLit q [155]) + (countLit q [156]) := List.countP_append (p := literal q) (l₁ := [155]) (l₂ := [156])
  have hm := merge_left (literal (valuationOf q) (155)) (literal (valuationOf q) (303)) (countLit q [155]) (countLit q [156]) (count303 q) 1 (meaning155 q) (meaning303 q) hs
  change valuationOf q 155 = false ∨ valuationOf q 303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause886 (q : Snake 81) (h : Conditions q) : valuation q 155 = false ∨ valuation q 303 = true := counterClause886 (baseVal q)

theorem counterClause887 (q : Nat → Bool) : valuationOf q 157 = false ∨ valuationOf q 305 = true := by
  have hs : count305 q = (countLit q [157]) + (countLit q [158]) := List.countP_append (p := literal q) (l₁ := [157]) (l₂ := [158])
  have hm := merge_left (literal (valuationOf q) (157)) (literal (valuationOf q) (305)) (countLit q [157]) (countLit q [158]) (count305 q) 1 (meaning157 q) (meaning305 q) hs
  change valuationOf q 157 = false ∨ valuationOf q 305 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause887 (q : Snake 81) (h : Conditions q) : valuation q 157 = false ∨ valuation q 305 = true := counterClause887 (baseVal q)

theorem counterClause888 (q : Nat → Bool) : valuationOf q 305 = false ∨ valuationOf q 307 = true := by
  have hs : count307 q = (countLit q [155, 156]) + (countLit q [157, 158]) := List.countP_append (p := literal q) (l₁ := [155, 156]) (l₂ := [157, 158])
  have hm := merge_right (literal (valuationOf q) (305)) (literal (valuationOf q) (307)) (countLit q [155, 156]) (countLit q [157, 158]) (count307 q) 1 (meaning305 q) (meaning307 q) hs
  change valuationOf q 305 = false ∨ valuationOf q 307 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause888 (q : Snake 81) (h : Conditions q) : valuation q 305 = false ∨ valuation q 307 = true := counterClause888 (baseVal q)

theorem counterClause889 (q : Nat → Bool) : valuationOf q 303 = false ∨ valuationOf q 307 = true := by
  have hs : count307 q = (countLit q [155, 156]) + (countLit q [157, 158]) := List.countP_append (p := literal q) (l₁ := [155, 156]) (l₂ := [157, 158])
  have hm := merge_left (literal (valuationOf q) (303)) (literal (valuationOf q) (307)) (countLit q [155, 156]) (countLit q [157, 158]) (count307 q) 1 (meaning303 q) (meaning307 q) hs
  change valuationOf q 303 = false ∨ valuationOf q 307 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause889 (q : Snake 81) (h : Conditions q) : valuation q 303 = false ∨ valuation q 307 = true := counterClause889 (baseVal q)

theorem counterClause890 (q : Nat → Bool) : valuationOf q 303 = false ∨ valuationOf q 305 = false ∨ valuationOf q 308 = true := by
  have hs : count307 q = (countLit q [155, 156]) + (countLit q [157, 158]) := List.countP_append (p := literal q) (l₁ := [155, 156]) (l₂ := [157, 158])
  have hm := merge_two (literal (valuationOf q) (303)) (literal (valuationOf q) (305)) (literal (valuationOf q) (308)) (countLit q [155, 156]) (countLit q [157, 158]) (count307 q) 1 1 (meaning303 q) (meaning305 q) (meaning308 q) hs
  change valuationOf q 303 = false ∨ valuationOf q 305 = false ∨ valuationOf q 308 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause890 (q : Snake 81) (h : Conditions q) : valuation q 303 = false ∨ valuation q 305 = false ∨ valuation q 308 = true := counterClause890 (baseVal q)

theorem counterClause891 (q : Nat → Bool) : valuationOf q 307 = false ∨ valuationOf q 309 = true := by
  have hs : count309 q = (countLit q [151, 152, 153, 154]) + (countLit q [155, 156, 157, 158]) := List.countP_append (p := literal q) (l₁ := [151, 152, 153, 154]) (l₂ := [155, 156, 157, 158])
  have hm := merge_right (literal (valuationOf q) (307)) (literal (valuationOf q) (309)) (countLit q [151, 152, 153, 154]) (countLit q [155, 156, 157, 158]) (count309 q) 1 (meaning307 q) (meaning309 q) hs
  change valuationOf q 307 = false ∨ valuationOf q 309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause891 (q : Snake 81) (h : Conditions q) : valuation q 307 = false ∨ valuation q 309 = true := counterClause891 (baseVal q)

theorem counterClause892 (q : Nat → Bool) : valuationOf q 308 = false ∨ valuationOf q 310 = true := by
  have hs : count309 q = (countLit q [151, 152, 153, 154]) + (countLit q [155, 156, 157, 158]) := List.countP_append (p := literal q) (l₁ := [151, 152, 153, 154]) (l₂ := [155, 156, 157, 158])
  have hm := merge_right (literal (valuationOf q) (308)) (literal (valuationOf q) (310)) (countLit q [151, 152, 153, 154]) (countLit q [155, 156, 157, 158]) (count309 q) 2 (meaning308 q) (meaning310 q) hs
  change valuationOf q 308 = false ∨ valuationOf q 310 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause892 (q : Snake 81) (h : Conditions q) : valuation q 308 = false ∨ valuation q 310 = true := counterClause892 (baseVal q)

theorem counterClause893 (q : Nat → Bool) : valuationOf q 301 = false ∨ valuationOf q 309 = true := by
  have hs : count309 q = (countLit q [151, 152, 153, 154]) + (countLit q [155, 156, 157, 158]) := List.countP_append (p := literal q) (l₁ := [151, 152, 153, 154]) (l₂ := [155, 156, 157, 158])
  have hm := merge_left (literal (valuationOf q) (301)) (literal (valuationOf q) (309)) (countLit q [151, 152, 153, 154]) (countLit q [155, 156, 157, 158]) (count309 q) 1 (meaning301 q) (meaning309 q) hs
  change valuationOf q 301 = false ∨ valuationOf q 309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause893 (q : Snake 81) (h : Conditions q) : valuation q 301 = false ∨ valuation q 309 = true := counterClause893 (baseVal q)

theorem counterClause894 (q : Nat → Bool) : valuationOf q 301 = false ∨ valuationOf q 307 = false ∨ valuationOf q 310 = true := by
  have hs : count309 q = (countLit q [151, 152, 153, 154]) + (countLit q [155, 156, 157, 158]) := List.countP_append (p := literal q) (l₁ := [151, 152, 153, 154]) (l₂ := [155, 156, 157, 158])
  have hm := merge_two (literal (valuationOf q) (301)) (literal (valuationOf q) (307)) (literal (valuationOf q) (310)) (countLit q [151, 152, 153, 154]) (countLit q [155, 156, 157, 158]) (count309 q) 1 1 (meaning301 q) (meaning307 q) (meaning310 q) hs
  change valuationOf q 301 = false ∨ valuationOf q 307 = false ∨ valuationOf q 310 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause894 (q : Snake 81) (h : Conditions q) : valuation q 301 = false ∨ valuation q 307 = false ∨ valuation q 310 = true := counterClause894 (baseVal q)

theorem counterClause895 (q : Nat → Bool) : valuationOf q 309 = false ∨ valuationOf q 311 = true := by
  have hs : count311 q = (countLit q [143, 144, 145, 146, 147, 148, 149, 150]) + (countLit q [151, 152, 153, 154, 155, 156, 157, 158]) := List.countP_append (p := literal q) (l₁ := [143, 144, 145, 146, 147, 148, 149, 150]) (l₂ := [151, 152, 153, 154, 155, 156, 157, 158])
  have hm := merge_right (literal (valuationOf q) (309)) (literal (valuationOf q) (311)) (countLit q [143, 144, 145, 146, 147, 148, 149, 150]) (countLit q [151, 152, 153, 154, 155, 156, 157, 158]) (count311 q) 1 (meaning309 q) (meaning311 q) hs
  change valuationOf q 309 = false ∨ valuationOf q 311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause895 (q : Snake 81) (h : Conditions q) : valuation q 309 = false ∨ valuation q 311 = true := counterClause895 (baseVal q)

theorem counterClause896 (q : Nat → Bool) : valuationOf q 310 = false ∨ valuationOf q 312 = true := by
  have hs : count311 q = (countLit q [143, 144, 145, 146, 147, 148, 149, 150]) + (countLit q [151, 152, 153, 154, 155, 156, 157, 158]) := List.countP_append (p := literal q) (l₁ := [143, 144, 145, 146, 147, 148, 149, 150]) (l₂ := [151, 152, 153, 154, 155, 156, 157, 158])
  have hm := merge_right (literal (valuationOf q) (310)) (literal (valuationOf q) (312)) (countLit q [143, 144, 145, 146, 147, 148, 149, 150]) (countLit q [151, 152, 153, 154, 155, 156, 157, 158]) (count311 q) 2 (meaning310 q) (meaning312 q) hs
  change valuationOf q 310 = false ∨ valuationOf q 312 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause896 (q : Snake 81) (h : Conditions q) : valuation q 310 = false ∨ valuation q 312 = true := counterClause896 (baseVal q)

theorem block27 (q : Snake 81) (h : Conditions q) : B112E256.Block27 (valuation q) :=
  ⟨clause865 q h, clause866 q h, clause867 q h, clause868 q h, clause869 q h, clause870 q h, clause871 q h, clause872 q h, clause873 q h, clause874 q h, clause875 q h, clause876 q h, clause877 q h, clause878 q h, clause879 q h, clause880 q h, clause881 q h, clause882 q h, clause883 q h, clause884 q h, clause885 q h, clause886 q h, clause887 q h, clause888 q h, clause889 q h, clause890 q h, clause891 q h, clause892 q h, clause893 q h, clause894 q h, clause895 q h, clause896 q h⟩

end
end Snake9.Regrowth.E112256
