import E112201Semantics
import B112E201Inputs
namespace Snake9.Regrowth.E112201
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause289 (q : Nat → Bool) : valuationOf q 283 = false ∨ valuationOf q 291 = true := by
  have hs : count291 q = (countLit q [143, 144, 145]) + (countLit q [146, 147, 148, 149]) := List.countP_append (p := literal q) (l₁ := [143, 144, 145]) (l₂ := [146, 147, 148, 149])
  have hm := merge_left (literal (valuationOf q) (283)) (literal (valuationOf q) (291)) (countLit q [143, 144, 145]) (countLit q [146, 147, 148, 149]) (count291 q) 1 (meaning283 q) (meaning291 q) hs
  change valuationOf q 283 = false ∨ valuationOf q 291 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 283 = false ∨ valuation q 291 = true := counterClause289 (baseVal q)

theorem counterClause290 (q : Nat → Bool) : valuationOf q 283 = false ∨ valuationOf q 289 = false ∨ valuationOf q 292 = true := by
  have hs : count291 q = (countLit q [143, 144, 145]) + (countLit q [146, 147, 148, 149]) := List.countP_append (p := literal q) (l₁ := [143, 144, 145]) (l₂ := [146, 147, 148, 149])
  have hm := merge_two (literal (valuationOf q) (283)) (literal (valuationOf q) (289)) (literal (valuationOf q) (292)) (countLit q [143, 144, 145]) (countLit q [146, 147, 148, 149]) (count291 q) 1 1 (meaning283 q) (meaning289 q) (meaning292 q) hs
  change valuationOf q 283 = false ∨ valuationOf q 289 = false ∨ valuationOf q 292 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 283 = false ∨ valuation q 289 = false ∨ valuation q 292 = true := counterClause290 (baseVal q)

theorem counterClause291 (q : Nat → Bool) : valuationOf q 291 = false ∨ valuationOf q 293 = true := by
  have hs : count293 q = (countLit q [137, 138, 139, 140, 141, 142]) + (countLit q [143, 144, 145, 146, 147, 148, 149]) := List.countP_append (p := literal q) (l₁ := [137, 138, 139, 140, 141, 142]) (l₂ := [143, 144, 145, 146, 147, 148, 149])
  have hm := merge_right (literal (valuationOf q) (291)) (literal (valuationOf q) (293)) (countLit q [137, 138, 139, 140, 141, 142]) (countLit q [143, 144, 145, 146, 147, 148, 149]) (count293 q) 1 (meaning291 q) (meaning293 q) hs
  change valuationOf q 291 = false ∨ valuationOf q 293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 291 = false ∨ valuation q 293 = true := counterClause291 (baseVal q)

theorem counterClause292 (q : Nat → Bool) : valuationOf q 292 = false ∨ valuationOf q 294 = true := by
  have hs : count293 q = (countLit q [137, 138, 139, 140, 141, 142]) + (countLit q [143, 144, 145, 146, 147, 148, 149]) := List.countP_append (p := literal q) (l₁ := [137, 138, 139, 140, 141, 142]) (l₂ := [143, 144, 145, 146, 147, 148, 149])
  have hm := merge_right (literal (valuationOf q) (292)) (literal (valuationOf q) (294)) (countLit q [137, 138, 139, 140, 141, 142]) (countLit q [143, 144, 145, 146, 147, 148, 149]) (count293 q) 2 (meaning292 q) (meaning294 q) hs
  change valuationOf q 292 = false ∨ valuationOf q 294 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 292 = false ∨ valuation q 294 = true := counterClause292 (baseVal q)

theorem counterClause293 (q : Nat → Bool) : valuationOf q 279 = false ∨ valuationOf q 293 = true := by
  have hs : count293 q = (countLit q [137, 138, 139, 140, 141, 142]) + (countLit q [143, 144, 145, 146, 147, 148, 149]) := List.countP_append (p := literal q) (l₁ := [137, 138, 139, 140, 141, 142]) (l₂ := [143, 144, 145, 146, 147, 148, 149])
  have hm := merge_left (literal (valuationOf q) (279)) (literal (valuationOf q) (293)) (countLit q [137, 138, 139, 140, 141, 142]) (countLit q [143, 144, 145, 146, 147, 148, 149]) (count293 q) 1 (meaning279 q) (meaning293 q) hs
  change valuationOf q 279 = false ∨ valuationOf q 293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 279 = false ∨ valuation q 293 = true := counterClause293 (baseVal q)

theorem counterClause294 (q : Nat → Bool) : valuationOf q 152 = false ∨ valuationOf q 295 = true := by
  have hs : count295 q = (countLit q [151]) + (countLit q [152]) := List.countP_append (p := literal q) (l₁ := [151]) (l₂ := [152])
  have hm := merge_right (literal (valuationOf q) (152)) (literal (valuationOf q) (295)) (countLit q [151]) (countLit q [152]) (count295 q) 1 (meaning152 q) (meaning295 q) hs
  change valuationOf q 152 = false ∨ valuationOf q 295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 152 = false ∨ valuation q 295 = true := counterClause294 (baseVal q)

theorem counterClause295 (q : Nat → Bool) : valuationOf q 295 = false ∨ valuationOf q 297 = true := by
  have hs : count297 q = (countLit q [150]) + (countLit q [151, 152]) := List.countP_append (p := literal q) (l₁ := [150]) (l₂ := [151, 152])
  have hm := merge_right (literal (valuationOf q) (295)) (literal (valuationOf q) (297)) (countLit q [150]) (countLit q [151, 152]) (count297 q) 1 (meaning295 q) (meaning297 q) hs
  change valuationOf q 295 = false ∨ valuationOf q 297 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 295 = false ∨ valuation q 297 = true := counterClause295 (baseVal q)

theorem counterClause296 (q : Nat → Bool) : valuationOf q 154 = false ∨ valuationOf q 299 = true := by
  have hs : count299 q = (countLit q [153]) + (countLit q [154]) := List.countP_append (p := literal q) (l₁ := [153]) (l₂ := [154])
  have hm := merge_right (literal (valuationOf q) (154)) (literal (valuationOf q) (299)) (countLit q [153]) (countLit q [154]) (count299 q) 1 (meaning154 q) (meaning299 q) hs
  change valuationOf q 154 = false ∨ valuationOf q 299 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 154 = false ∨ valuation q 299 = true := counterClause296 (baseVal q)

theorem counterClause297 (q : Nat → Bool) : valuationOf q 155 = false ∨ valuationOf q 301 = true := by
  have hs : count301 q = (countLit q [155]) + (countLit q [156]) := List.countP_append (p := literal q) (l₁ := [155]) (l₂ := [156])
  have hm := merge_left (literal (valuationOf q) (155)) (literal (valuationOf q) (301)) (countLit q [155]) (countLit q [156]) (count301 q) 1 (meaning155 q) (meaning301 q) hs
  change valuationOf q 155 = false ∨ valuationOf q 301 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 155 = false ∨ valuation q 301 = true := counterClause297 (baseVal q)

theorem counterClause298 (q : Nat → Bool) : valuationOf q 301 = false ∨ valuationOf q 303 = true := by
  have hs : count303 q = (countLit q [153, 154]) + (countLit q [155, 156]) := List.countP_append (p := literal q) (l₁ := [153, 154]) (l₂ := [155, 156])
  have hm := merge_right (literal (valuationOf q) (301)) (literal (valuationOf q) (303)) (countLit q [153, 154]) (countLit q [155, 156]) (count303 q) 1 (meaning301 q) (meaning303 q) hs
  change valuationOf q 301 = false ∨ valuationOf q 303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 301 = false ∨ valuation q 303 = true := counterClause298 (baseVal q)

theorem counterClause299 (q : Nat → Bool) : valuationOf q 299 = false ∨ valuationOf q 303 = true := by
  have hs : count303 q = (countLit q [153, 154]) + (countLit q [155, 156]) := List.countP_append (p := literal q) (l₁ := [153, 154]) (l₂ := [155, 156])
  have hm := merge_left (literal (valuationOf q) (299)) (literal (valuationOf q) (303)) (countLit q [153, 154]) (countLit q [155, 156]) (count303 q) 1 (meaning299 q) (meaning303 q) hs
  change valuationOf q 299 = false ∨ valuationOf q 303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 299 = false ∨ valuation q 303 = true := counterClause299 (baseVal q)

theorem counterClause300 (q : Nat → Bool) : valuationOf q 303 = false ∨ valuationOf q 305 = true := by
  have hs : count305 q = (countLit q [150, 151, 152]) + (countLit q [153, 154, 155, 156]) := List.countP_append (p := literal q) (l₁ := [150, 151, 152]) (l₂ := [153, 154, 155, 156])
  have hm := merge_right (literal (valuationOf q) (303)) (literal (valuationOf q) (305)) (countLit q [150, 151, 152]) (countLit q [153, 154, 155, 156]) (count305 q) 1 (meaning303 q) (meaning305 q) hs
  change valuationOf q 303 = false ∨ valuationOf q 305 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 303 = false ∨ valuation q 305 = true := counterClause300 (baseVal q)

theorem counterClause301 (q : Nat → Bool) : valuationOf q 297 = false ∨ valuationOf q 305 = true := by
  have hs : count305 q = (countLit q [150, 151, 152]) + (countLit q [153, 154, 155, 156]) := List.countP_append (p := literal q) (l₁ := [150, 151, 152]) (l₂ := [153, 154, 155, 156])
  have hm := merge_left (literal (valuationOf q) (297)) (literal (valuationOf q) (305)) (countLit q [150, 151, 152]) (countLit q [153, 154, 155, 156]) (count305 q) 1 (meaning297 q) (meaning305 q) hs
  change valuationOf q 297 = false ∨ valuationOf q 305 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 297 = false ∨ valuation q 305 = true := counterClause301 (baseVal q)

theorem counterClause302 (q : Nat → Bool) : valuationOf q 158 = false ∨ valuationOf q 307 = true := by
  have hs : count307 q = (countLit q [158]) + (countLit q [159]) := List.countP_append (p := literal q) (l₁ := [158]) (l₂ := [159])
  have hm := merge_left (literal (valuationOf q) (158)) (literal (valuationOf q) (307)) (countLit q [158]) (countLit q [159]) (count307 q) 1 (meaning158 q) (meaning307 q) hs
  change valuationOf q 158 = false ∨ valuationOf q 307 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 158 = false ∨ valuation q 307 = true := counterClause302 (baseVal q)

theorem counterClause303 (q : Nat → Bool) : valuationOf q 307 = false ∨ valuationOf q 309 = true := by
  have hs : count309 q = (countLit q [157]) + (countLit q [158, 159]) := List.countP_append (p := literal q) (l₁ := [157]) (l₂ := [158, 159])
  have hm := merge_right (literal (valuationOf q) (307)) (literal (valuationOf q) (309)) (countLit q [157]) (countLit q [158, 159]) (count309 q) 1 (meaning307 q) (meaning309 q) hs
  change valuationOf q 307 = false ∨ valuationOf q 309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 307 = false ∨ valuation q 309 = true := counterClause303 (baseVal q)

theorem counterClause304 (q : Nat → Bool) : valuationOf q 160 = false ∨ valuationOf q 311 = true := by
  have hs : count311 q = (countLit q [160]) + (countLit q [161]) := List.countP_append (p := literal q) (l₁ := [160]) (l₂ := [161])
  have hm := merge_left (literal (valuationOf q) (160)) (literal (valuationOf q) (311)) (countLit q [160]) (countLit q [161]) (count311 q) 1 (meaning160 q) (meaning311 q) hs
  change valuationOf q 160 = false ∨ valuationOf q 311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 160 = false ∨ valuation q 311 = true := counterClause304 (baseVal q)

theorem counterClause305 (q : Nat → Bool) : valuationOf q 162 = false ∨ valuationOf q 313 = true := by
  have hs : count313 q = (countLit q [162]) + (countLit q [163]) := List.countP_append (p := literal q) (l₁ := [162]) (l₂ := [163])
  have hm := merge_left (literal (valuationOf q) (162)) (literal (valuationOf q) (313)) (countLit q [162]) (countLit q [163]) (count313 q) 1 (meaning162 q) (meaning313 q) hs
  change valuationOf q 162 = false ∨ valuationOf q 313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 162 = false ∨ valuation q 313 = true := counterClause305 (baseVal q)

theorem counterClause306 (q : Nat → Bool) : valuationOf q 313 = false ∨ valuationOf q 315 = true := by
  have hs : count315 q = (countLit q [160, 161]) + (countLit q [162, 163]) := List.countP_append (p := literal q) (l₁ := [160, 161]) (l₂ := [162, 163])
  have hm := merge_right (literal (valuationOf q) (313)) (literal (valuationOf q) (315)) (countLit q [160, 161]) (countLit q [162, 163]) (count315 q) 1 (meaning313 q) (meaning315 q) hs
  change valuationOf q 313 = false ∨ valuationOf q 315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 313 = false ∨ valuation q 315 = true := counterClause306 (baseVal q)

theorem counterClause307 (q : Nat → Bool) : valuationOf q 311 = false ∨ valuationOf q 315 = true := by
  have hs : count315 q = (countLit q [160, 161]) + (countLit q [162, 163]) := List.countP_append (p := literal q) (l₁ := [160, 161]) (l₂ := [162, 163])
  have hm := merge_left (literal (valuationOf q) (311)) (literal (valuationOf q) (315)) (countLit q [160, 161]) (countLit q [162, 163]) (count315 q) 1 (meaning311 q) (meaning315 q) hs
  change valuationOf q 311 = false ∨ valuationOf q 315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 311 = false ∨ valuation q 315 = true := counterClause307 (baseVal q)

theorem counterClause308 (q : Nat → Bool) : valuationOf q 315 = false ∨ valuationOf q 317 = true := by
  have hs : count317 q = (countLit q [157, 158, 159]) + (countLit q [160, 161, 162, 163]) := List.countP_append (p := literal q) (l₁ := [157, 158, 159]) (l₂ := [160, 161, 162, 163])
  have hm := merge_right (literal (valuationOf q) (315)) (literal (valuationOf q) (317)) (countLit q [157, 158, 159]) (countLit q [160, 161, 162, 163]) (count317 q) 1 (meaning315 q) (meaning317 q) hs
  change valuationOf q 315 = false ∨ valuationOf q 317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 315 = false ∨ valuation q 317 = true := counterClause308 (baseVal q)

theorem counterClause309 (q : Nat → Bool) : valuationOf q 309 = false ∨ valuationOf q 317 = true := by
  have hs : count317 q = (countLit q [157, 158, 159]) + (countLit q [160, 161, 162, 163]) := List.countP_append (p := literal q) (l₁ := [157, 158, 159]) (l₂ := [160, 161, 162, 163])
  have hm := merge_left (literal (valuationOf q) (309)) (literal (valuationOf q) (317)) (countLit q [157, 158, 159]) (countLit q [160, 161, 162, 163]) (count317 q) 1 (meaning309 q) (meaning317 q) hs
  change valuationOf q 309 = false ∨ valuationOf q 317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 309 = false ∨ valuation q 317 = true := counterClause309 (baseVal q)

theorem counterClause310 (q : Nat → Bool) : valuationOf q 317 = false ∨ valuationOf q 319 = true := by
  have hs : count319 q = (countLit q [150, 151, 152, 153, 154, 155, 156]) + (countLit q [157, 158, 159, 160, 161, 162, 163]) := List.countP_append (p := literal q) (l₁ := [150, 151, 152, 153, 154, 155, 156]) (l₂ := [157, 158, 159, 160, 161, 162, 163])
  have hm := merge_right (literal (valuationOf q) (317)) (literal (valuationOf q) (319)) (countLit q [150, 151, 152, 153, 154, 155, 156]) (countLit q [157, 158, 159, 160, 161, 162, 163]) (count319 q) 1 (meaning317 q) (meaning319 q) hs
  change valuationOf q 317 = false ∨ valuationOf q 319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 317 = false ∨ valuation q 319 = true := counterClause310 (baseVal q)

theorem counterClause311 (q : Nat → Bool) : valuationOf q 305 = false ∨ valuationOf q 319 = true := by
  have hs : count319 q = (countLit q [150, 151, 152, 153, 154, 155, 156]) + (countLit q [157, 158, 159, 160, 161, 162, 163]) := List.countP_append (p := literal q) (l₁ := [150, 151, 152, 153, 154, 155, 156]) (l₂ := [157, 158, 159, 160, 161, 162, 163])
  have hm := merge_left (literal (valuationOf q) (305)) (literal (valuationOf q) (319)) (countLit q [150, 151, 152, 153, 154, 155, 156]) (countLit q [157, 158, 159, 160, 161, 162, 163]) (count319 q) 1 (meaning305 q) (meaning319 q) hs
  change valuationOf q 305 = false ∨ valuationOf q 319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 305 = false ∨ valuation q 319 = true := counterClause311 (baseVal q)

theorem counterClause312 (q : Nat → Bool) : valuationOf q 319 = false ∨ valuationOf q 321 = true := by
  have hs : count321 q = (countLit q [137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) + (countLit q [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) := List.countP_append (p := literal q) (l₁ := [137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) (l₂ := [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163])
  have hm := merge_right (literal (valuationOf q) (319)) (literal (valuationOf q) (321)) (countLit q [137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) (countLit q [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) (count321 q) 1 (meaning319 q) (meaning321 q) hs
  change valuationOf q 319 = false ∨ valuationOf q 321 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 319 = false ∨ valuation q 321 = true := counterClause312 (baseVal q)

theorem counterClause313 (q : Nat → Bool) : valuationOf q 293 = false ∨ valuationOf q 321 = true := by
  have hs : count321 q = (countLit q [137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) + (countLit q [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) := List.countP_append (p := literal q) (l₁ := [137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) (l₂ := [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163])
  have hm := merge_left (literal (valuationOf q) (293)) (literal (valuationOf q) (321)) (countLit q [137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) (countLit q [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) (count321 q) 1 (meaning293 q) (meaning321 q) hs
  change valuationOf q 293 = false ∨ valuationOf q 321 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 293 = false ∨ valuation q 321 = true := counterClause313 (baseVal q)

theorem counterClause314 (q : Nat → Bool) : valuationOf q 293 = false ∨ valuationOf q 319 = false ∨ valuationOf q 322 = true := by
  have hs : count321 q = (countLit q [137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) + (countLit q [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) := List.countP_append (p := literal q) (l₁ := [137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) (l₂ := [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163])
  have hm := merge_two (literal (valuationOf q) (293)) (literal (valuationOf q) (319)) (literal (valuationOf q) (322)) (countLit q [137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) (countLit q [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) (count321 q) 1 1 (meaning293 q) (meaning319 q) (meaning322 q) hs
  change valuationOf q 293 = false ∨ valuationOf q 319 = false ∨ valuationOf q 322 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 293 = false ∨ valuation q 319 = false ∨ valuation q 322 = true := counterClause314 (baseVal q)

theorem counterClause315 (q : Nat → Bool) : valuationOf q 294 = false ∨ valuationOf q 322 = true := by
  have hs : count321 q = (countLit q [137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) + (countLit q [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) := List.countP_append (p := literal q) (l₁ := [137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) (l₂ := [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163])
  have hm := merge_left (literal (valuationOf q) (294)) (literal (valuationOf q) (322)) (countLit q [137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]) (countLit q [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) (count321 q) 2 (meaning294 q) (meaning322 q) hs
  change valuationOf q 294 = false ∨ valuationOf q 322 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 294 = false ∨ valuation q 322 = true := counterClause315 (baseVal q)

theorem counterClause316 (q : Nat → Bool) : valuationOf q 321 = false ∨ valuationOf q 323 = true := by
  have hs : count323 q = (countLit q [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136]) + (countLit q [137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) := List.countP_append (p := literal q) (l₁ := [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136]) (l₂ := [137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163])
  have hm := merge_right (literal (valuationOf q) (321)) (literal (valuationOf q) (323)) (countLit q [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136]) (countLit q [137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) (count323 q) 1 (meaning321 q) (meaning323 q) hs
  change valuationOf q 321 = false ∨ valuationOf q 323 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 321 = false ∨ valuation q 323 = true := counterClause316 (baseVal q)

theorem counterClause317 (q : Nat → Bool) : valuationOf q 322 = false ∨ valuationOf q 324 = true := by
  have hs : count323 q = (countLit q [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136]) + (countLit q [137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) := List.countP_append (p := literal q) (l₁ := [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136]) (l₂ := [137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163])
  have hm := merge_right (literal (valuationOf q) (322)) (literal (valuationOf q) (324)) (countLit q [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136]) (countLit q [137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) (count323 q) 2 (meaning322 q) (meaning324 q) hs
  change valuationOf q 322 = false ∨ valuationOf q 324 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 322 = false ∨ valuation q 324 = true := counterClause317 (baseVal q)

theorem counterClause318 (q : Nat → Bool) : valuationOf q 269 = false ∨ valuationOf q 323 = true := by
  have hs : count323 q = (countLit q [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136]) + (countLit q [137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) := List.countP_append (p := literal q) (l₁ := [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136]) (l₂ := [137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163])
  have hm := merge_left (literal (valuationOf q) (269)) (literal (valuationOf q) (323)) (countLit q [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136]) (countLit q [137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) (count323 q) 1 (meaning269 q) (meaning323 q) hs
  change valuationOf q 269 = false ∨ valuationOf q 323 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 269 = false ∨ valuation q 323 = true := counterClause318 (baseVal q)

theorem counterClause319 (q : Nat → Bool) : valuationOf q 269 = false ∨ valuationOf q 321 = false ∨ valuationOf q 324 = true := by
  have hs : count323 q = (countLit q [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136]) + (countLit q [137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) := List.countP_append (p := literal q) (l₁ := [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136]) (l₂ := [137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163])
  have hm := merge_two (literal (valuationOf q) (269)) (literal (valuationOf q) (321)) (literal (valuationOf q) (324)) (countLit q [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136]) (countLit q [137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) (count323 q) 1 1 (meaning269 q) (meaning321 q) (meaning324 q) hs
  change valuationOf q 269 = false ∨ valuationOf q 321 = false ∨ valuationOf q 324 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 269 = false ∨ valuation q 321 = false ∨ valuation q 324 = true := counterClause319 (baseVal q)

theorem counterClause320 (q : Nat → Bool) : valuationOf q 270 = false ∨ valuationOf q 324 = true := by
  have hs : count323 q = (countLit q [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136]) + (countLit q [137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) := List.countP_append (p := literal q) (l₁ := [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136]) (l₂ := [137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163])
  have hm := merge_left (literal (valuationOf q) (270)) (literal (valuationOf q) (324)) (countLit q [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136]) (countLit q [137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) (count323 q) 2 (meaning270 q) (meaning324 q) hs
  change valuationOf q 270 = false ∨ valuationOf q 324 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 270 = false ∨ valuation q 324 = true := counterClause320 (baseVal q)

theorem block9 (q : Snake 81) (h : Conditions q) : B112E201.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112201
