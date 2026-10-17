import E112146Semantics
import B112E146Inputs
namespace Snake9.Regrowth.E112146
noncomputable section
local instance blockDec12 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause385 (q : Nat → Bool) : valuationOf q 291 = false ∨ valuationOf q 293 = true := by
  have hs : count293 q = (countLit q [143, 144, 145]) + (countLit q [146, 147, 148, 149]) := List.countP_append (p := literal q) (l₁ := [143, 144, 145]) (l₂ := [146, 147, 148, 149])
  have hm := merge_right (literal (valuationOf q) (291)) (literal (valuationOf q) (293)) (countLit q [143, 144, 145]) (countLit q [146, 147, 148, 149]) (count293 q) 1 (meaning291 q) (meaning293 q) hs
  change valuationOf q 291 = false ∨ valuationOf q 293 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause385 (q : Snake 81) (h : Conditions q) : valuation q 291 = false ∨ valuation q 293 = true := counterClause385 (baseVal q)

theorem counterClause386 (q : Nat → Bool) : valuationOf q 152 = false ∨ valuationOf q 295 = true := by
  have hs : count295 q = (countLit q [151]) + (countLit q [152]) := List.countP_append (p := literal q) (l₁ := [151]) (l₂ := [152])
  have hm := merge_right (literal (valuationOf q) (152)) (literal (valuationOf q) (295)) (countLit q [151]) (countLit q [152]) (count295 q) 1 (meaning152 q) (meaning295 q) hs
  change valuationOf q 152 = false ∨ valuationOf q 295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause386 (q : Snake 81) (h : Conditions q) : valuation q 152 = false ∨ valuation q 295 = true := counterClause386 (baseVal q)

theorem counterClause387 (q : Nat → Bool) : valuationOf q 295 = false ∨ valuationOf q 297 = true := by
  have hs : count297 q = (countLit q [150]) + (countLit q [151, 152]) := List.countP_append (p := literal q) (l₁ := [150]) (l₂ := [151, 152])
  have hm := merge_right (literal (valuationOf q) (295)) (literal (valuationOf q) (297)) (countLit q [150]) (countLit q [151, 152]) (count297 q) 1 (meaning295 q) (meaning297 q) hs
  change valuationOf q 295 = false ∨ valuationOf q 297 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause387 (q : Snake 81) (h : Conditions q) : valuation q 295 = false ∨ valuation q 297 = true := counterClause387 (baseVal q)

theorem counterClause388 (q : Nat → Bool) : valuationOf q 156 = false ∨ valuationOf q 301 = true := by
  have hs : count301 q = (countLit q [155]) + (countLit q [156]) := List.countP_append (p := literal q) (l₁ := [155]) (l₂ := [156])
  have hm := merge_right (literal (valuationOf q) (156)) (literal (valuationOf q) (301)) (countLit q [155]) (countLit q [156]) (count301 q) 1 (meaning156 q) (meaning301 q) hs
  change valuationOf q 156 = false ∨ valuationOf q 301 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause388 (q : Snake 81) (h : Conditions q) : valuation q 156 = false ∨ valuation q 301 = true := counterClause388 (baseVal q)

theorem counterClause389 (q : Nat → Bool) : valuationOf q 301 = false ∨ valuationOf q 303 = true := by
  have hs : count303 q = (countLit q [153, 154]) + (countLit q [155, 156]) := List.countP_append (p := literal q) (l₁ := [153, 154]) (l₂ := [155, 156])
  have hm := merge_right (literal (valuationOf q) (301)) (literal (valuationOf q) (303)) (countLit q [153, 154]) (countLit q [155, 156]) (count303 q) 1 (meaning301 q) (meaning303 q) hs
  change valuationOf q 301 = false ∨ valuationOf q 303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause389 (q : Snake 81) (h : Conditions q) : valuation q 301 = false ∨ valuation q 303 = true := counterClause389 (baseVal q)

theorem counterClause390 (q : Nat → Bool) : valuationOf q 303 = false ∨ valuationOf q 305 = true := by
  have hs : count305 q = (countLit q [150, 151, 152]) + (countLit q [153, 154, 155, 156]) := List.countP_append (p := literal q) (l₁ := [150, 151, 152]) (l₂ := [153, 154, 155, 156])
  have hm := merge_right (literal (valuationOf q) (303)) (literal (valuationOf q) (305)) (countLit q [150, 151, 152]) (countLit q [153, 154, 155, 156]) (count305 q) 1 (meaning303 q) (meaning305 q) hs
  change valuationOf q 303 = false ∨ valuationOf q 305 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause390 (q : Snake 81) (h : Conditions q) : valuation q 303 = false ∨ valuation q 305 = true := counterClause390 (baseVal q)

theorem counterClause391 (q : Nat → Bool) : valuationOf q 297 = false ∨ valuationOf q 305 = true := by
  have hs : count305 q = (countLit q [150, 151, 152]) + (countLit q [153, 154, 155, 156]) := List.countP_append (p := literal q) (l₁ := [150, 151, 152]) (l₂ := [153, 154, 155, 156])
  have hm := merge_left (literal (valuationOf q) (297)) (literal (valuationOf q) (305)) (countLit q [150, 151, 152]) (countLit q [153, 154, 155, 156]) (count305 q) 1 (meaning297 q) (meaning305 q) hs
  change valuationOf q 297 = false ∨ valuationOf q 305 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause391 (q : Snake 81) (h : Conditions q) : valuation q 297 = false ∨ valuation q 305 = true := counterClause391 (baseVal q)

theorem counterClause392 (q : Nat → Bool) : valuationOf q 305 = false ∨ valuationOf q 307 = true := by
  have hs : count307 q = (countLit q [143, 144, 145, 146, 147, 148, 149]) + (countLit q [150, 151, 152, 153, 154, 155, 156]) := List.countP_append (p := literal q) (l₁ := [143, 144, 145, 146, 147, 148, 149]) (l₂ := [150, 151, 152, 153, 154, 155, 156])
  have hm := merge_right (literal (valuationOf q) (305)) (literal (valuationOf q) (307)) (countLit q [143, 144, 145, 146, 147, 148, 149]) (countLit q [150, 151, 152, 153, 154, 155, 156]) (count307 q) 1 (meaning305 q) (meaning307 q) hs
  change valuationOf q 305 = false ∨ valuationOf q 307 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause392 (q : Snake 81) (h : Conditions q) : valuation q 305 = false ∨ valuation q 307 = true := counterClause392 (baseVal q)

theorem counterClause393 (q : Nat → Bool) : valuationOf q 293 = false ∨ valuationOf q 307 = true := by
  have hs : count307 q = (countLit q [143, 144, 145, 146, 147, 148, 149]) + (countLit q [150, 151, 152, 153, 154, 155, 156]) := List.countP_append (p := literal q) (l₁ := [143, 144, 145, 146, 147, 148, 149]) (l₂ := [150, 151, 152, 153, 154, 155, 156])
  have hm := merge_left (literal (valuationOf q) (293)) (literal (valuationOf q) (307)) (countLit q [143, 144, 145, 146, 147, 148, 149]) (countLit q [150, 151, 152, 153, 154, 155, 156]) (count307 q) 1 (meaning293 q) (meaning307 q) hs
  change valuationOf q 293 = false ∨ valuationOf q 307 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause393 (q : Snake 81) (h : Conditions q) : valuation q 293 = false ∨ valuation q 307 = true := counterClause393 (baseVal q)

theorem counterClause394 (q : Nat → Bool) : valuationOf q 293 = false ∨ valuationOf q 305 = false ∨ valuationOf q 308 = true := by
  have hs : count307 q = (countLit q [143, 144, 145, 146, 147, 148, 149]) + (countLit q [150, 151, 152, 153, 154, 155, 156]) := List.countP_append (p := literal q) (l₁ := [143, 144, 145, 146, 147, 148, 149]) (l₂ := [150, 151, 152, 153, 154, 155, 156])
  have hm := merge_two (literal (valuationOf q) (293)) (literal (valuationOf q) (305)) (literal (valuationOf q) (308)) (countLit q [143, 144, 145, 146, 147, 148, 149]) (countLit q [150, 151, 152, 153, 154, 155, 156]) (count307 q) 1 1 (meaning293 q) (meaning305 q) (meaning308 q) hs
  change valuationOf q 293 = false ∨ valuationOf q 305 = false ∨ valuationOf q 308 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause394 (q : Snake 81) (h : Conditions q) : valuation q 293 = false ∨ valuation q 305 = false ∨ valuation q 308 = true := counterClause394 (baseVal q)

theorem counterClause395 (q : Nat → Bool) : valuationOf q 159 = false ∨ valuationOf q 309 = true := by
  have hs : count309 q = (countLit q [158]) + (countLit q [159]) := List.countP_append (p := literal q) (l₁ := [158]) (l₂ := [159])
  have hm := merge_right (literal (valuationOf q) (159)) (literal (valuationOf q) (309)) (countLit q [158]) (countLit q [159]) (count309 q) 1 (meaning159 q) (meaning309 q) hs
  change valuationOf q 159 = false ∨ valuationOf q 309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause395 (q : Snake 81) (h : Conditions q) : valuation q 159 = false ∨ valuation q 309 = true := counterClause395 (baseVal q)

theorem counterClause396 (q : Nat → Bool) : valuationOf q 158 = false ∨ valuationOf q 309 = true := by
  have hs : count309 q = (countLit q [158]) + (countLit q [159]) := List.countP_append (p := literal q) (l₁ := [158]) (l₂ := [159])
  have hm := merge_left (literal (valuationOf q) (158)) (literal (valuationOf q) (309)) (countLit q [158]) (countLit q [159]) (count309 q) 1 (meaning158 q) (meaning309 q) hs
  change valuationOf q 158 = false ∨ valuationOf q 309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause396 (q : Snake 81) (h : Conditions q) : valuation q 158 = false ∨ valuation q 309 = true := counterClause396 (baseVal q)

theorem counterClause397 (q : Nat → Bool) : valuationOf q 158 = false ∨ valuationOf q 159 = false ∨ valuationOf q 310 = true := by
  have hs : count309 q = (countLit q [158]) + (countLit q [159]) := List.countP_append (p := literal q) (l₁ := [158]) (l₂ := [159])
  have hm := merge_two (literal (valuationOf q) (158)) (literal (valuationOf q) (159)) (literal (valuationOf q) (310)) (countLit q [158]) (countLit q [159]) (count309 q) 1 1 (meaning158 q) (meaning159 q) (meaning310 q) hs
  change valuationOf q 158 = false ∨ valuationOf q 159 = false ∨ valuationOf q 310 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause397 (q : Snake 81) (h : Conditions q) : valuation q 158 = false ∨ valuation q 159 = false ∨ valuation q 310 = true := counterClause397 (baseVal q)

theorem counterClause398 (q : Nat → Bool) : valuationOf q 309 = false ∨ valuationOf q 311 = true := by
  have hs : count311 q = (countLit q [157]) + (countLit q [158, 159]) := List.countP_append (p := literal q) (l₁ := [157]) (l₂ := [158, 159])
  have hm := merge_right (literal (valuationOf q) (309)) (literal (valuationOf q) (311)) (countLit q [157]) (countLit q [158, 159]) (count311 q) 1 (meaning309 q) (meaning311 q) hs
  change valuationOf q 309 = false ∨ valuationOf q 311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause398 (q : Snake 81) (h : Conditions q) : valuation q 309 = false ∨ valuation q 311 = true := counterClause398 (baseVal q)

theorem counterClause399 (q : Nat → Bool) : valuationOf q 310 = false ∨ valuationOf q 312 = true := by
  have hs : count311 q = (countLit q [157]) + (countLit q [158, 159]) := List.countP_append (p := literal q) (l₁ := [157]) (l₂ := [158, 159])
  have hm := merge_right (literal (valuationOf q) (310)) (literal (valuationOf q) (312)) (countLit q [157]) (countLit q [158, 159]) (count311 q) 2 (meaning310 q) (meaning312 q) hs
  change valuationOf q 310 = false ∨ valuationOf q 312 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause399 (q : Snake 81) (h : Conditions q) : valuation q 310 = false ∨ valuation q 312 = true := counterClause399 (baseVal q)

theorem counterClause400 (q : Nat → Bool) : valuationOf q 163 = false ∨ valuationOf q 315 = true := by
  have hs : count315 q = (countLit q [162]) + (countLit q [163]) := List.countP_append (p := literal q) (l₁ := [162]) (l₂ := [163])
  have hm := merge_right (literal (valuationOf q) (163)) (literal (valuationOf q) (315)) (countLit q [162]) (countLit q [163]) (count315 q) 1 (meaning163 q) (meaning315 q) hs
  change valuationOf q 163 = false ∨ valuationOf q 315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause400 (q : Snake 81) (h : Conditions q) : valuation q 163 = false ∨ valuation q 315 = true := counterClause400 (baseVal q)

theorem counterClause401 (q : Nat → Bool) : valuationOf q 315 = false ∨ valuationOf q 317 = true := by
  have hs : count317 q = (countLit q [160, 161]) + (countLit q [162, 163]) := List.countP_append (p := literal q) (l₁ := [160, 161]) (l₂ := [162, 163])
  have hm := merge_right (literal (valuationOf q) (315)) (literal (valuationOf q) (317)) (countLit q [160, 161]) (countLit q [162, 163]) (count317 q) 1 (meaning315 q) (meaning317 q) hs
  change valuationOf q 315 = false ∨ valuationOf q 317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause401 (q : Snake 81) (h : Conditions q) : valuation q 315 = false ∨ valuation q 317 = true := counterClause401 (baseVal q)

theorem counterClause402 (q : Nat → Bool) : valuationOf q 311 = false ∨ valuationOf q 319 = true := by
  have hs : count319 q = (countLit q [157, 158, 159]) + (countLit q [160, 161, 162, 163]) := List.countP_append (p := literal q) (l₁ := [157, 158, 159]) (l₂ := [160, 161, 162, 163])
  have hm := merge_left (literal (valuationOf q) (311)) (literal (valuationOf q) (319)) (countLit q [157, 158, 159]) (countLit q [160, 161, 162, 163]) (count319 q) 1 (meaning311 q) (meaning319 q) hs
  change valuationOf q 311 = false ∨ valuationOf q 319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause402 (q : Snake 81) (h : Conditions q) : valuation q 311 = false ∨ valuation q 319 = true := counterClause402 (baseVal q)

theorem counterClause403 (q : Nat → Bool) : valuationOf q 311 = false ∨ valuationOf q 317 = false ∨ valuationOf q 320 = true := by
  have hs : count319 q = (countLit q [157, 158, 159]) + (countLit q [160, 161, 162, 163]) := List.countP_append (p := literal q) (l₁ := [157, 158, 159]) (l₂ := [160, 161, 162, 163])
  have hm := merge_two (literal (valuationOf q) (311)) (literal (valuationOf q) (317)) (literal (valuationOf q) (320)) (countLit q [157, 158, 159]) (countLit q [160, 161, 162, 163]) (count319 q) 1 1 (meaning311 q) (meaning317 q) (meaning320 q) hs
  change valuationOf q 311 = false ∨ valuationOf q 317 = false ∨ valuationOf q 320 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause403 (q : Snake 81) (h : Conditions q) : valuation q 311 = false ∨ valuation q 317 = false ∨ valuation q 320 = true := counterClause403 (baseVal q)

theorem counterClause404 (q : Nat → Bool) : valuationOf q 312 = false ∨ valuationOf q 320 = true := by
  have hs : count319 q = (countLit q [157, 158, 159]) + (countLit q [160, 161, 162, 163]) := List.countP_append (p := literal q) (l₁ := [157, 158, 159]) (l₂ := [160, 161, 162, 163])
  have hm := merge_left (literal (valuationOf q) (312)) (literal (valuationOf q) (320)) (countLit q [157, 158, 159]) (countLit q [160, 161, 162, 163]) (count319 q) 2 (meaning312 q) (meaning320 q) hs
  change valuationOf q 312 = false ∨ valuationOf q 320 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause404 (q : Snake 81) (h : Conditions q) : valuation q 312 = false ∨ valuation q 320 = true := counterClause404 (baseVal q)

theorem counterClause405 (q : Nat → Bool) : valuationOf q 166 = false ∨ valuationOf q 321 = true := by
  have hs : count321 q = (countLit q [165]) + (countLit q [166]) := List.countP_append (p := literal q) (l₁ := [165]) (l₂ := [166])
  have hm := merge_right (literal (valuationOf q) (166)) (literal (valuationOf q) (321)) (countLit q [165]) (countLit q [166]) (count321 q) 1 (meaning166 q) (meaning321 q) hs
  change valuationOf q 166 = false ∨ valuationOf q 321 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause405 (q : Snake 81) (h : Conditions q) : valuation q 166 = false ∨ valuation q 321 = true := counterClause405 (baseVal q)

theorem counterClause406 (q : Nat → Bool) : valuationOf q 321 = false ∨ valuationOf q 323 = true := by
  have hs : count323 q = (countLit q [164]) + (countLit q [165, 166]) := List.countP_append (p := literal q) (l₁ := [164]) (l₂ := [165, 166])
  have hm := merge_right (literal (valuationOf q) (321)) (literal (valuationOf q) (323)) (countLit q [164]) (countLit q [165, 166]) (count323 q) 1 (meaning321 q) (meaning323 q) hs
  change valuationOf q 321 = false ∨ valuationOf q 323 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause406 (q : Snake 81) (h : Conditions q) : valuation q 321 = false ∨ valuation q 323 = true := counterClause406 (baseVal q)

theorem counterClause407 (q : Nat → Bool) : valuationOf q 323 = false ∨ valuationOf q 331 = true := by
  have hs : count331 q = (countLit q [164, 165, 166]) + (countLit q [167, 168, 169, 170]) := List.countP_append (p := literal q) (l₁ := [164, 165, 166]) (l₂ := [167, 168, 169, 170])
  have hm := merge_left (literal (valuationOf q) (323)) (literal (valuationOf q) (331)) (countLit q [164, 165, 166]) (countLit q [167, 168, 169, 170]) (count331 q) 1 (meaning323 q) (meaning331 q) hs
  change valuationOf q 323 = false ∨ valuationOf q 331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause407 (q : Snake 81) (h : Conditions q) : valuation q 323 = false ∨ valuation q 331 = true := counterClause407 (baseVal q)

theorem counterClause408 (q : Nat → Bool) : valuationOf q 331 = false ∨ valuationOf q 333 = true := by
  have hs : count333 q = (countLit q [157, 158, 159, 160, 161, 162, 163]) + (countLit q [164, 165, 166, 167, 168, 169, 170]) := List.countP_append (p := literal q) (l₁ := [157, 158, 159, 160, 161, 162, 163]) (l₂ := [164, 165, 166, 167, 168, 169, 170])
  have hm := merge_right (literal (valuationOf q) (331)) (literal (valuationOf q) (333)) (countLit q [157, 158, 159, 160, 161, 162, 163]) (countLit q [164, 165, 166, 167, 168, 169, 170]) (count333 q) 1 (meaning331 q) (meaning333 q) hs
  change valuationOf q 331 = false ∨ valuationOf q 333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause408 (q : Snake 81) (h : Conditions q) : valuation q 331 = false ∨ valuation q 333 = true := counterClause408 (baseVal q)

theorem counterClause409 (q : Nat → Bool) : valuationOf q 319 = false ∨ valuationOf q 333 = true := by
  have hs : count333 q = (countLit q [157, 158, 159, 160, 161, 162, 163]) + (countLit q [164, 165, 166, 167, 168, 169, 170]) := List.countP_append (p := literal q) (l₁ := [157, 158, 159, 160, 161, 162, 163]) (l₂ := [164, 165, 166, 167, 168, 169, 170])
  have hm := merge_left (literal (valuationOf q) (319)) (literal (valuationOf q) (333)) (countLit q [157, 158, 159, 160, 161, 162, 163]) (countLit q [164, 165, 166, 167, 168, 169, 170]) (count333 q) 1 (meaning319 q) (meaning333 q) hs
  change valuationOf q 319 = false ∨ valuationOf q 333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause409 (q : Snake 81) (h : Conditions q) : valuation q 319 = false ∨ valuation q 333 = true := counterClause409 (baseVal q)

theorem counterClause410 (q : Nat → Bool) : valuationOf q 320 = false ∨ valuationOf q 334 = true := by
  have hs : count333 q = (countLit q [157, 158, 159, 160, 161, 162, 163]) + (countLit q [164, 165, 166, 167, 168, 169, 170]) := List.countP_append (p := literal q) (l₁ := [157, 158, 159, 160, 161, 162, 163]) (l₂ := [164, 165, 166, 167, 168, 169, 170])
  have hm := merge_left (literal (valuationOf q) (320)) (literal (valuationOf q) (334)) (countLit q [157, 158, 159, 160, 161, 162, 163]) (countLit q [164, 165, 166, 167, 168, 169, 170]) (count333 q) 2 (meaning320 q) (meaning334 q) hs
  change valuationOf q 320 = false ∨ valuationOf q 334 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause410 (q : Snake 81) (h : Conditions q) : valuation q 320 = false ∨ valuation q 334 = true := counterClause410 (baseVal q)

theorem counterClause411 (q : Nat → Bool) : valuationOf q 333 = false ∨ valuationOf q 335 = true := by
  have hs : count335 q = (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156]) + (countLit q [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) := List.countP_append (p := literal q) (l₁ := [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156]) (l₂ := [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170])
  have hm := merge_right (literal (valuationOf q) (333)) (literal (valuationOf q) (335)) (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156]) (countLit q [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) (count335 q) 1 (meaning333 q) (meaning335 q) hs
  change valuationOf q 333 = false ∨ valuationOf q 335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause411 (q : Snake 81) (h : Conditions q) : valuation q 333 = false ∨ valuation q 335 = true := counterClause411 (baseVal q)

theorem counterClause412 (q : Nat → Bool) : valuationOf q 334 = false ∨ valuationOf q 336 = true := by
  have hs : count335 q = (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156]) + (countLit q [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) := List.countP_append (p := literal q) (l₁ := [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156]) (l₂ := [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170])
  have hm := merge_right (literal (valuationOf q) (334)) (literal (valuationOf q) (336)) (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156]) (countLit q [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) (count335 q) 2 (meaning334 q) (meaning336 q) hs
  change valuationOf q 334 = false ∨ valuationOf q 336 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause412 (q : Snake 81) (h : Conditions q) : valuation q 334 = false ∨ valuation q 336 = true := counterClause412 (baseVal q)

theorem counterClause413 (q : Nat → Bool) : valuationOf q 307 = false ∨ valuationOf q 335 = true := by
  have hs : count335 q = (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156]) + (countLit q [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) := List.countP_append (p := literal q) (l₁ := [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156]) (l₂ := [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170])
  have hm := merge_left (literal (valuationOf q) (307)) (literal (valuationOf q) (335)) (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156]) (countLit q [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) (count335 q) 1 (meaning307 q) (meaning335 q) hs
  change valuationOf q 307 = false ∨ valuationOf q 335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause413 (q : Snake 81) (h : Conditions q) : valuation q 307 = false ∨ valuation q 335 = true := counterClause413 (baseVal q)

theorem counterClause414 (q : Nat → Bool) : valuationOf q 307 = false ∨ valuationOf q 333 = false ∨ valuationOf q 336 = true := by
  have hs : count335 q = (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156]) + (countLit q [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) := List.countP_append (p := literal q) (l₁ := [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156]) (l₂ := [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170])
  have hm := merge_two (literal (valuationOf q) (307)) (literal (valuationOf q) (333)) (literal (valuationOf q) (336)) (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156]) (countLit q [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) (count335 q) 1 1 (meaning307 q) (meaning333 q) (meaning336 q) hs
  change valuationOf q 307 = false ∨ valuationOf q 333 = false ∨ valuationOf q 336 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause414 (q : Snake 81) (h : Conditions q) : valuation q 307 = false ∨ valuation q 333 = false ∨ valuation q 336 = true := counterClause414 (baseVal q)

theorem counterClause415 (q : Nat → Bool) : valuationOf q 308 = false ∨ valuationOf q 336 = true := by
  have hs : count335 q = (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156]) + (countLit q [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) := List.countP_append (p := literal q) (l₁ := [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156]) (l₂ := [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170])
  have hm := merge_left (literal (valuationOf q) (308)) (literal (valuationOf q) (336)) (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156]) (countLit q [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) (count335 q) 2 (meaning308 q) (meaning336 q) hs
  change valuationOf q 308 = false ∨ valuationOf q 336 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause415 (q : Snake 81) (h : Conditions q) : valuation q 308 = false ∨ valuation q 336 = true := counterClause415 (baseVal q)

theorem counterClause416 (q : Nat → Bool) : valuationOf q 335 = false ∨ valuationOf q 337 = true := by
  have hs : count337 q = (countLit q [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) + (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) := List.countP_append (p := literal q) (l₁ := [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (l₂ := [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170])
  have hm := merge_right (literal (valuationOf q) (335)) (literal (valuationOf q) (337)) (countLit q [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]) (countLit q [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) (count337 q) 1 (meaning335 q) (meaning337 q) hs
  change valuationOf q 335 = false ∨ valuationOf q 337 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause416 (q : Snake 81) (h : Conditions q) : valuation q 335 = false ∨ valuation q 337 = true := counterClause416 (baseVal q)

theorem block12 (q : Snake 81) (h : Conditions q) : B112E146.Block12 (valuation q) :=
  ⟨clause385 q h, clause386 q h, clause387 q h, clause388 q h, clause389 q h, clause390 q h, clause391 q h, clause392 q h, clause393 q h, clause394 q h, clause395 q h, clause396 q h, clause397 q h, clause398 q h, clause399 q h, clause400 q h, clause401 q h, clause402 q h, clause403 q h, clause404 q h, clause405 q h, clause406 q h, clause407 q h, clause408 q h, clause409 q h, clause410 q h, clause411 q h, clause412 q h, clause413 q h, clause414 q h, clause415 q h, clause416 q h⟩

end
end Snake9.Regrowth.E112146
