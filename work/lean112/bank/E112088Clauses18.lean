import E112088Semantics
import B112E088Inputs
namespace Snake9.Regrowth.E112088
noncomputable section
local instance blockDec18 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause577 (q : Nat → Bool) : valuationOf q 299 = false ∨ valuationOf q 301 = true := by
  have hs : count301 q = (countLit q [153]) + (countLit q [154, 155]) := List.countP_append (p := literal q) (l₁ := [153]) (l₂ := [154, 155])
  have hm := merge_right (literal (valuationOf q) (299)) (literal (valuationOf q) (301)) (countLit q [153]) (countLit q [154, 155]) (count301 q) 1 (meaning299 q) (meaning301 q) hs
  change valuationOf q 299 = false ∨ valuationOf q 301 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause577 (q : Snake 81) (h : Conditions q) : valuation q 299 = false ∨ valuation q 301 = true := counterClause577 (baseVal q)

theorem counterClause578 (q : Nat → Bool) : valuationOf q 157 = false ∨ valuationOf q 303 = true := by
  have hs : count303 q = (countLit q [156]) + (countLit q [157]) := List.countP_append (p := literal q) (l₁ := [156]) (l₂ := [157])
  have hm := merge_right (literal (valuationOf q) (157)) (literal (valuationOf q) (303)) (countLit q [156]) (countLit q [157]) (count303 q) 1 (meaning157 q) (meaning303 q) hs
  change valuationOf q 157 = false ∨ valuationOf q 303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause578 (q : Snake 81) (h : Conditions q) : valuation q 157 = false ∨ valuation q 303 = true := counterClause578 (baseVal q)

theorem counterClause579 (q : Nat → Bool) : valuationOf q 159 = false ∨ valuationOf q 305 = true := by
  have hs : count305 q = (countLit q [158]) + (countLit q [159]) := List.countP_append (p := literal q) (l₁ := [158]) (l₂ := [159])
  have hm := merge_right (literal (valuationOf q) (159)) (literal (valuationOf q) (305)) (countLit q [158]) (countLit q [159]) (count305 q) 1 (meaning159 q) (meaning305 q) hs
  change valuationOf q 159 = false ∨ valuationOf q 305 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause579 (q : Snake 81) (h : Conditions q) : valuation q 159 = false ∨ valuation q 305 = true := counterClause579 (baseVal q)

theorem counterClause580 (q : Nat → Bool) : valuationOf q 305 = false ∨ valuationOf q 307 = true := by
  have hs : count307 q = (countLit q [156, 157]) + (countLit q [158, 159]) := List.countP_append (p := literal q) (l₁ := [156, 157]) (l₂ := [158, 159])
  have hm := merge_right (literal (valuationOf q) (305)) (literal (valuationOf q) (307)) (countLit q [156, 157]) (countLit q [158, 159]) (count307 q) 1 (meaning305 q) (meaning307 q) hs
  change valuationOf q 305 = false ∨ valuationOf q 307 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause580 (q : Snake 81) (h : Conditions q) : valuation q 305 = false ∨ valuation q 307 = true := counterClause580 (baseVal q)

theorem counterClause581 (q : Nat → Bool) : valuationOf q 303 = false ∨ valuationOf q 307 = true := by
  have hs : count307 q = (countLit q [156, 157]) + (countLit q [158, 159]) := List.countP_append (p := literal q) (l₁ := [156, 157]) (l₂ := [158, 159])
  have hm := merge_left (literal (valuationOf q) (303)) (literal (valuationOf q) (307)) (countLit q [156, 157]) (countLit q [158, 159]) (count307 q) 1 (meaning303 q) (meaning307 q) hs
  change valuationOf q 303 = false ∨ valuationOf q 307 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause581 (q : Snake 81) (h : Conditions q) : valuation q 303 = false ∨ valuation q 307 = true := counterClause581 (baseVal q)

theorem counterClause582 (q : Nat → Bool) : valuationOf q 307 = false ∨ valuationOf q 309 = true := by
  have hs : count309 q = (countLit q [153, 154, 155]) + (countLit q [156, 157, 158, 159]) := List.countP_append (p := literal q) (l₁ := [153, 154, 155]) (l₂ := [156, 157, 158, 159])
  have hm := merge_right (literal (valuationOf q) (307)) (literal (valuationOf q) (309)) (countLit q [153, 154, 155]) (countLit q [156, 157, 158, 159]) (count309 q) 1 (meaning307 q) (meaning309 q) hs
  change valuationOf q 307 = false ∨ valuationOf q 309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause582 (q : Snake 81) (h : Conditions q) : valuation q 307 = false ∨ valuation q 309 = true := counterClause582 (baseVal q)

theorem counterClause583 (q : Nat → Bool) : valuationOf q 301 = false ∨ valuationOf q 309 = true := by
  have hs : count309 q = (countLit q [153, 154, 155]) + (countLit q [156, 157, 158, 159]) := List.countP_append (p := literal q) (l₁ := [153, 154, 155]) (l₂ := [156, 157, 158, 159])
  have hm := merge_left (literal (valuationOf q) (301)) (literal (valuationOf q) (309)) (countLit q [153, 154, 155]) (countLit q [156, 157, 158, 159]) (count309 q) 1 (meaning301 q) (meaning309 q) hs
  change valuationOf q 301 = false ∨ valuationOf q 309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause583 (q : Snake 81) (h : Conditions q) : valuation q 301 = false ∨ valuation q 309 = true := counterClause583 (baseVal q)

theorem counterClause584 (q : Nat → Bool) : valuationOf q 309 = false ∨ valuationOf q 311 = true := by
  have hs : count311 q = (countLit q [146, 147, 148, 149, 150, 151, 152]) + (countLit q [153, 154, 155, 156, 157, 158, 159]) := List.countP_append (p := literal q) (l₁ := [146, 147, 148, 149, 150, 151, 152]) (l₂ := [153, 154, 155, 156, 157, 158, 159])
  have hm := merge_right (literal (valuationOf q) (309)) (literal (valuationOf q) (311)) (countLit q [146, 147, 148, 149, 150, 151, 152]) (countLit q [153, 154, 155, 156, 157, 158, 159]) (count311 q) 1 (meaning309 q) (meaning311 q) hs
  change valuationOf q 309 = false ∨ valuationOf q 311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause584 (q : Snake 81) (h : Conditions q) : valuation q 309 = false ∨ valuation q 311 = true := counterClause584 (baseVal q)

theorem counterClause585 (q : Nat → Bool) : valuationOf q 297 = false ∨ valuationOf q 311 = true := by
  have hs : count311 q = (countLit q [146, 147, 148, 149, 150, 151, 152]) + (countLit q [153, 154, 155, 156, 157, 158, 159]) := List.countP_append (p := literal q) (l₁ := [146, 147, 148, 149, 150, 151, 152]) (l₂ := [153, 154, 155, 156, 157, 158, 159])
  have hm := merge_left (literal (valuationOf q) (297)) (literal (valuationOf q) (311)) (countLit q [146, 147, 148, 149, 150, 151, 152]) (countLit q [153, 154, 155, 156, 157, 158, 159]) (count311 q) 1 (meaning297 q) (meaning311 q) hs
  change valuationOf q 297 = false ∨ valuationOf q 311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause585 (q : Snake 81) (h : Conditions q) : valuation q 297 = false ∨ valuation q 311 = true := counterClause585 (baseVal q)

theorem counterClause586 (q : Nat → Bool) : valuationOf q 298 = false ∨ valuationOf q 312 = true := by
  have hs : count311 q = (countLit q [146, 147, 148, 149, 150, 151, 152]) + (countLit q [153, 154, 155, 156, 157, 158, 159]) := List.countP_append (p := literal q) (l₁ := [146, 147, 148, 149, 150, 151, 152]) (l₂ := [153, 154, 155, 156, 157, 158, 159])
  have hm := merge_left (literal (valuationOf q) (298)) (literal (valuationOf q) (312)) (countLit q [146, 147, 148, 149, 150, 151, 152]) (countLit q [153, 154, 155, 156, 157, 158, 159]) (count311 q) 2 (meaning298 q) (meaning312 q) hs
  change valuationOf q 298 = false ∨ valuationOf q 312 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause586 (q : Snake 81) (h : Conditions q) : valuation q 298 = false ∨ valuation q 312 = true := counterClause586 (baseVal q)

theorem counterClause587 (q : Nat → Bool) : valuationOf q 162 = false ∨ valuationOf q 313 = true := by
  have hs : count313 q = (countLit q [161]) + (countLit q [162]) := List.countP_append (p := literal q) (l₁ := [161]) (l₂ := [162])
  have hm := merge_right (literal (valuationOf q) (162)) (literal (valuationOf q) (313)) (countLit q [161]) (countLit q [162]) (count313 q) 1 (meaning162 q) (meaning313 q) hs
  change valuationOf q 162 = false ∨ valuationOf q 313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause587 (q : Snake 81) (h : Conditions q) : valuation q 162 = false ∨ valuation q 313 = true := counterClause587 (baseVal q)

theorem counterClause588 (q : Nat → Bool) : valuationOf q 313 = false ∨ valuationOf q 315 = true := by
  have hs : count315 q = (countLit q [160]) + (countLit q [161, 162]) := List.countP_append (p := literal q) (l₁ := [160]) (l₂ := [161, 162])
  have hm := merge_right (literal (valuationOf q) (313)) (literal (valuationOf q) (315)) (countLit q [160]) (countLit q [161, 162]) (count315 q) 1 (meaning313 q) (meaning315 q) hs
  change valuationOf q 313 = false ∨ valuationOf q 315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause588 (q : Snake 81) (h : Conditions q) : valuation q 313 = false ∨ valuation q 315 = true := counterClause588 (baseVal q)

theorem counterClause589 (q : Nat → Bool) : valuationOf q 160 = false ∨ valuationOf q 315 = true := by
  have hs : count315 q = (countLit q [160]) + (countLit q [161, 162]) := List.countP_append (p := literal q) (l₁ := [160]) (l₂ := [161, 162])
  have hm := merge_left (literal (valuationOf q) (160)) (literal (valuationOf q) (315)) (countLit q [160]) (countLit q [161, 162]) (count315 q) 1 (meaning160 q) (meaning315 q) hs
  change valuationOf q 160 = false ∨ valuationOf q 315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause589 (q : Snake 81) (h : Conditions q) : valuation q 160 = false ∨ valuation q 315 = true := counterClause589 (baseVal q)

theorem counterClause590 (q : Nat → Bool) : valuationOf q 166 = false ∨ valuationOf q 319 = true := by
  have hs : count319 q = (countLit q [165]) + (countLit q [166]) := List.countP_append (p := literal q) (l₁ := [165]) (l₂ := [166])
  have hm := merge_right (literal (valuationOf q) (166)) (literal (valuationOf q) (319)) (countLit q [165]) (countLit q [166]) (count319 q) 1 (meaning166 q) (meaning319 q) hs
  change valuationOf q 166 = false ∨ valuationOf q 319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause590 (q : Snake 81) (h : Conditions q) : valuation q 166 = false ∨ valuation q 319 = true := counterClause590 (baseVal q)

theorem counterClause591 (q : Nat → Bool) : valuationOf q 165 = false ∨ valuationOf q 319 = true := by
  have hs : count319 q = (countLit q [165]) + (countLit q [166]) := List.countP_append (p := literal q) (l₁ := [165]) (l₂ := [166])
  have hm := merge_left (literal (valuationOf q) (165)) (literal (valuationOf q) (319)) (countLit q [165]) (countLit q [166]) (count319 q) 1 (meaning165 q) (meaning319 q) hs
  change valuationOf q 165 = false ∨ valuationOf q 319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause591 (q : Snake 81) (h : Conditions q) : valuation q 165 = false ∨ valuation q 319 = true := counterClause591 (baseVal q)

theorem counterClause592 (q : Nat → Bool) : valuationOf q 319 = false ∨ valuationOf q 321 = true := by
  have hs : count321 q = (countLit q [163, 164]) + (countLit q [165, 166]) := List.countP_append (p := literal q) (l₁ := [163, 164]) (l₂ := [165, 166])
  have hm := merge_right (literal (valuationOf q) (319)) (literal (valuationOf q) (321)) (countLit q [163, 164]) (countLit q [165, 166]) (count321 q) 1 (meaning319 q) (meaning321 q) hs
  change valuationOf q 319 = false ∨ valuationOf q 321 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause592 (q : Snake 81) (h : Conditions q) : valuation q 319 = false ∨ valuation q 321 = true := counterClause592 (baseVal q)

theorem counterClause593 (q : Nat → Bool) : valuationOf q 321 = false ∨ valuationOf q 323 = true := by
  have hs : count323 q = (countLit q [160, 161, 162]) + (countLit q [163, 164, 165, 166]) := List.countP_append (p := literal q) (l₁ := [160, 161, 162]) (l₂ := [163, 164, 165, 166])
  have hm := merge_right (literal (valuationOf q) (321)) (literal (valuationOf q) (323)) (countLit q [160, 161, 162]) (countLit q [163, 164, 165, 166]) (count323 q) 1 (meaning321 q) (meaning323 q) hs
  change valuationOf q 321 = false ∨ valuationOf q 323 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause593 (q : Snake 81) (h : Conditions q) : valuation q 321 = false ∨ valuation q 323 = true := counterClause593 (baseVal q)

theorem counterClause594 (q : Nat → Bool) : valuationOf q 315 = false ∨ valuationOf q 323 = true := by
  have hs : count323 q = (countLit q [160, 161, 162]) + (countLit q [163, 164, 165, 166]) := List.countP_append (p := literal q) (l₁ := [160, 161, 162]) (l₂ := [163, 164, 165, 166])
  have hm := merge_left (literal (valuationOf q) (315)) (literal (valuationOf q) (323)) (countLit q [160, 161, 162]) (countLit q [163, 164, 165, 166]) (count323 q) 1 (meaning315 q) (meaning323 q) hs
  change valuationOf q 315 = false ∨ valuationOf q 323 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause594 (q : Snake 81) (h : Conditions q) : valuation q 315 = false ∨ valuation q 323 = true := counterClause594 (baseVal q)

theorem counterClause595 (q : Nat → Bool) : valuationOf q 170 = false ∨ valuationOf q 327 = true := by
  have hs : count327 q = (countLit q [169]) + (countLit q [170]) := List.countP_append (p := literal q) (l₁ := [169]) (l₂ := [170])
  have hm := merge_right (literal (valuationOf q) (170)) (literal (valuationOf q) (327)) (countLit q [169]) (countLit q [170]) (count327 q) 1 (meaning170 q) (meaning327 q) hs
  change valuationOf q 170 = false ∨ valuationOf q 327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause595 (q : Snake 81) (h : Conditions q) : valuation q 170 = false ∨ valuation q 327 = true := counterClause595 (baseVal q)

theorem counterClause596 (q : Nat → Bool) : valuationOf q 169 = false ∨ valuationOf q 327 = true := by
  have hs : count327 q = (countLit q [169]) + (countLit q [170]) := List.countP_append (p := literal q) (l₁ := [169]) (l₂ := [170])
  have hm := merge_left (literal (valuationOf q) (169)) (literal (valuationOf q) (327)) (countLit q [169]) (countLit q [170]) (count327 q) 1 (meaning169 q) (meaning327 q) hs
  change valuationOf q 169 = false ∨ valuationOf q 327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause596 (q : Snake 81) (h : Conditions q) : valuation q 169 = false ∨ valuation q 327 = true := counterClause596 (baseVal q)

theorem counterClause597 (q : Nat → Bool) : valuationOf q 169 = false ∨ valuationOf q 170 = false ∨ valuationOf q 328 = true := by
  have hs : count327 q = (countLit q [169]) + (countLit q [170]) := List.countP_append (p := literal q) (l₁ := [169]) (l₂ := [170])
  have hm := merge_two (literal (valuationOf q) (169)) (literal (valuationOf q) (170)) (literal (valuationOf q) (328)) (countLit q [169]) (countLit q [170]) (count327 q) 1 1 (meaning169 q) (meaning170 q) (meaning328 q) hs
  change valuationOf q 169 = false ∨ valuationOf q 170 = false ∨ valuationOf q 328 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause597 (q : Snake 81) (h : Conditions q) : valuation q 169 = false ∨ valuation q 170 = false ∨ valuation q 328 = true := counterClause597 (baseVal q)

theorem counterClause598 (q : Nat → Bool) : valuationOf q 327 = false ∨ valuationOf q 329 = true := by
  have hs : count329 q = (countLit q [167, 168]) + (countLit q [169, 170]) := List.countP_append (p := literal q) (l₁ := [167, 168]) (l₂ := [169, 170])
  have hm := merge_right (literal (valuationOf q) (327)) (literal (valuationOf q) (329)) (countLit q [167, 168]) (countLit q [169, 170]) (count329 q) 1 (meaning327 q) (meaning329 q) hs
  change valuationOf q 327 = false ∨ valuationOf q 329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause598 (q : Snake 81) (h : Conditions q) : valuation q 327 = false ∨ valuation q 329 = true := counterClause598 (baseVal q)

theorem counterClause599 (q : Nat → Bool) : valuationOf q 328 = false ∨ valuationOf q 330 = true := by
  have hs : count329 q = (countLit q [167, 168]) + (countLit q [169, 170]) := List.countP_append (p := literal q) (l₁ := [167, 168]) (l₂ := [169, 170])
  have hm := merge_right (literal (valuationOf q) (328)) (literal (valuationOf q) (330)) (countLit q [167, 168]) (countLit q [169, 170]) (count329 q) 2 (meaning328 q) (meaning330 q) hs
  change valuationOf q 328 = false ∨ valuationOf q 330 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause599 (q : Snake 81) (h : Conditions q) : valuation q 328 = false ∨ valuation q 330 = true := counterClause599 (baseVal q)

theorem counterClause600 (q : Nat → Bool) : valuationOf q 174 = false ∨ valuationOf q 333 = true := by
  have hs : count333 q = (countLit q [173]) + (countLit q [174]) := List.countP_append (p := literal q) (l₁ := [173]) (l₂ := [174])
  have hm := merge_right (literal (valuationOf q) (174)) (literal (valuationOf q) (333)) (countLit q [173]) (countLit q [174]) (count333 q) 1 (meaning174 q) (meaning333 q) hs
  change valuationOf q 174 = false ∨ valuationOf q 333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause600 (q : Snake 81) (h : Conditions q) : valuation q 174 = false ∨ valuation q 333 = true := counterClause600 (baseVal q)

theorem counterClause601 (q : Nat → Bool) : valuationOf q 333 = false ∨ valuationOf q 335 = true := by
  have hs : count335 q = (countLit q [171, 172]) + (countLit q [173, 174]) := List.countP_append (p := literal q) (l₁ := [171, 172]) (l₂ := [173, 174])
  have hm := merge_right (literal (valuationOf q) (333)) (literal (valuationOf q) (335)) (countLit q [171, 172]) (countLit q [173, 174]) (count335 q) 1 (meaning333 q) (meaning335 q) hs
  change valuationOf q 333 = false ∨ valuationOf q 335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause601 (q : Snake 81) (h : Conditions q) : valuation q 333 = false ∨ valuation q 335 = true := counterClause601 (baseVal q)

theorem counterClause602 (q : Nat → Bool) : valuationOf q 335 = false ∨ valuationOf q 337 = true := by
  have hs : count337 q = (countLit q [167, 168, 169, 170]) + (countLit q [171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [167, 168, 169, 170]) (l₂ := [171, 172, 173, 174])
  have hm := merge_right (literal (valuationOf q) (335)) (literal (valuationOf q) (337)) (countLit q [167, 168, 169, 170]) (countLit q [171, 172, 173, 174]) (count337 q) 1 (meaning335 q) (meaning337 q) hs
  change valuationOf q 335 = false ∨ valuationOf q 337 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause602 (q : Snake 81) (h : Conditions q) : valuation q 335 = false ∨ valuation q 337 = true := counterClause602 (baseVal q)

theorem counterClause603 (q : Nat → Bool) : valuationOf q 329 = false ∨ valuationOf q 337 = true := by
  have hs : count337 q = (countLit q [167, 168, 169, 170]) + (countLit q [171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [167, 168, 169, 170]) (l₂ := [171, 172, 173, 174])
  have hm := merge_left (literal (valuationOf q) (329)) (literal (valuationOf q) (337)) (countLit q [167, 168, 169, 170]) (countLit q [171, 172, 173, 174]) (count337 q) 1 (meaning329 q) (meaning337 q) hs
  change valuationOf q 329 = false ∨ valuationOf q 337 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause603 (q : Snake 81) (h : Conditions q) : valuation q 329 = false ∨ valuation q 337 = true := counterClause603 (baseVal q)

theorem counterClause604 (q : Nat → Bool) : valuationOf q 329 = false ∨ valuationOf q 335 = false ∨ valuationOf q 338 = true := by
  have hs : count337 q = (countLit q [167, 168, 169, 170]) + (countLit q [171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [167, 168, 169, 170]) (l₂ := [171, 172, 173, 174])
  have hm := merge_two (literal (valuationOf q) (329)) (literal (valuationOf q) (335)) (literal (valuationOf q) (338)) (countLit q [167, 168, 169, 170]) (countLit q [171, 172, 173, 174]) (count337 q) 1 1 (meaning329 q) (meaning335 q) (meaning338 q) hs
  change valuationOf q 329 = false ∨ valuationOf q 335 = false ∨ valuationOf q 338 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause604 (q : Snake 81) (h : Conditions q) : valuation q 329 = false ∨ valuation q 335 = false ∨ valuation q 338 = true := counterClause604 (baseVal q)

theorem counterClause605 (q : Nat → Bool) : valuationOf q 330 = false ∨ valuationOf q 338 = true := by
  have hs : count337 q = (countLit q [167, 168, 169, 170]) + (countLit q [171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [167, 168, 169, 170]) (l₂ := [171, 172, 173, 174])
  have hm := merge_left (literal (valuationOf q) (330)) (literal (valuationOf q) (338)) (countLit q [167, 168, 169, 170]) (countLit q [171, 172, 173, 174]) (count337 q) 2 (meaning330 q) (meaning338 q) hs
  change valuationOf q 330 = false ∨ valuationOf q 338 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause605 (q : Snake 81) (h : Conditions q) : valuation q 330 = false ∨ valuation q 338 = true := counterClause605 (baseVal q)

theorem counterClause606 (q : Nat → Bool) : valuationOf q 337 = false ∨ valuationOf q 339 = true := by
  have hs : count339 q = (countLit q [160, 161, 162, 163, 164, 165, 166]) + (countLit q [167, 168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [160, 161, 162, 163, 164, 165, 166]) (l₂ := [167, 168, 169, 170, 171, 172, 173, 174])
  have hm := merge_right (literal (valuationOf q) (337)) (literal (valuationOf q) (339)) (countLit q [160, 161, 162, 163, 164, 165, 166]) (countLit q [167, 168, 169, 170, 171, 172, 173, 174]) (count339 q) 1 (meaning337 q) (meaning339 q) hs
  change valuationOf q 337 = false ∨ valuationOf q 339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause606 (q : Snake 81) (h : Conditions q) : valuation q 337 = false ∨ valuation q 339 = true := counterClause606 (baseVal q)

theorem counterClause607 (q : Nat → Bool) : valuationOf q 338 = false ∨ valuationOf q 340 = true := by
  have hs : count339 q = (countLit q [160, 161, 162, 163, 164, 165, 166]) + (countLit q [167, 168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [160, 161, 162, 163, 164, 165, 166]) (l₂ := [167, 168, 169, 170, 171, 172, 173, 174])
  have hm := merge_right (literal (valuationOf q) (338)) (literal (valuationOf q) (340)) (countLit q [160, 161, 162, 163, 164, 165, 166]) (countLit q [167, 168, 169, 170, 171, 172, 173, 174]) (count339 q) 2 (meaning338 q) (meaning340 q) hs
  change valuationOf q 338 = false ∨ valuationOf q 340 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause607 (q : Snake 81) (h : Conditions q) : valuation q 338 = false ∨ valuation q 340 = true := counterClause607 (baseVal q)

theorem counterClause608 (q : Nat → Bool) : valuationOf q 323 = false ∨ valuationOf q 339 = true := by
  have hs : count339 q = (countLit q [160, 161, 162, 163, 164, 165, 166]) + (countLit q [167, 168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [160, 161, 162, 163, 164, 165, 166]) (l₂ := [167, 168, 169, 170, 171, 172, 173, 174])
  have hm := merge_left (literal (valuationOf q) (323)) (literal (valuationOf q) (339)) (countLit q [160, 161, 162, 163, 164, 165, 166]) (countLit q [167, 168, 169, 170, 171, 172, 173, 174]) (count339 q) 1 (meaning323 q) (meaning339 q) hs
  change valuationOf q 323 = false ∨ valuationOf q 339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause608 (q : Snake 81) (h : Conditions q) : valuation q 323 = false ∨ valuation q 339 = true := counterClause608 (baseVal q)

theorem block18 (q : Snake 81) (h : Conditions q) : B112E088.Block18 (valuation q) :=
  ⟨clause577 q h, clause578 q h, clause579 q h, clause580 q h, clause581 q h, clause582 q h, clause583 q h, clause584 q h, clause585 q h, clause586 q h, clause587 q h, clause588 q h, clause589 q h, clause590 q h, clause591 q h, clause592 q h, clause593 q h, clause594 q h, clause595 q h, clause596 q h, clause597 q h, clause598 q h, clause599 q h, clause600 q h, clause601 q h, clause602 q h, clause603 q h, clause604 q h, clause605 q h, clause606 q h, clause607 q h, clause608 q h⟩

end
end Snake9.Regrowth.E112088
