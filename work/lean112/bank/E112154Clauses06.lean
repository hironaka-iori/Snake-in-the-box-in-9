import E112154Semantics
import B112E154Inputs
namespace Snake9.Regrowth.E112154
noncomputable section
local instance blockDec6 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause193 (q : Nat → Bool) : valuationOf q 156 = false ∨ valuationOf q 305 = true := by
  have hs : count305 q = (countLit q [156]) + (countLit q [157]) := List.countP_append (p := literal q) (l₁ := [156]) (l₂ := [157])
  have hm := merge_left (literal (valuationOf q) (156)) (literal (valuationOf q) (305)) (countLit q [156]) (countLit q [157]) (count305 q) 1 (meaning156 q) (meaning305 q) hs
  change valuationOf q 156 = false ∨ valuationOf q 305 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause193 (q : Snake 81) (h : Conditions q) : valuation q 156 = false ∨ valuation q 305 = true := counterClause193 (baseVal q)

theorem counterClause194 (q : Nat → Bool) : valuationOf q 305 = false ∨ valuationOf q 307 = true := by
  have hs : count307 q = (countLit q [155]) + (countLit q [156, 157]) := List.countP_append (p := literal q) (l₁ := [155]) (l₂ := [156, 157])
  have hm := merge_right (literal (valuationOf q) (305)) (literal (valuationOf q) (307)) (countLit q [155]) (countLit q [156, 157]) (count307 q) 1 (meaning305 q) (meaning307 q) hs
  change valuationOf q 305 = false ∨ valuationOf q 307 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause194 (q : Snake 81) (h : Conditions q) : valuation q 305 = false ∨ valuation q 307 = true := counterClause194 (baseVal q)

theorem counterClause195 (q : Nat → Bool) : valuationOf q 307 = false ∨ valuationOf q 309 = true := by
  have hs : count309 q = (countLit q [152, 153, 154]) + (countLit q [155, 156, 157]) := List.countP_append (p := literal q) (l₁ := [152, 153, 154]) (l₂ := [155, 156, 157])
  have hm := merge_right (literal (valuationOf q) (307)) (literal (valuationOf q) (309)) (countLit q [152, 153, 154]) (countLit q [155, 156, 157]) (count309 q) 1 (meaning307 q) (meaning309 q) hs
  change valuationOf q 307 = false ∨ valuationOf q 309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause195 (q : Snake 81) (h : Conditions q) : valuation q 307 = false ∨ valuation q 309 = true := counterClause195 (baseVal q)

theorem counterClause196 (q : Nat → Bool) : valuationOf q 303 = false ∨ valuationOf q 309 = true := by
  have hs : count309 q = (countLit q [152, 153, 154]) + (countLit q [155, 156, 157]) := List.countP_append (p := literal q) (l₁ := [152, 153, 154]) (l₂ := [155, 156, 157])
  have hm := merge_left (literal (valuationOf q) (303)) (literal (valuationOf q) (309)) (countLit q [152, 153, 154]) (countLit q [155, 156, 157]) (count309 q) 1 (meaning303 q) (meaning309 q) hs
  change valuationOf q 303 = false ∨ valuationOf q 309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause196 (q : Snake 81) (h : Conditions q) : valuation q 303 = false ∨ valuation q 309 = true := counterClause196 (baseVal q)

theorem counterClause197 (q : Nat → Bool) : valuationOf q 158 = false ∨ valuationOf q 313 = true := by
  have hs : count313 q = (countLit q [158]) + (countLit q [159, 160]) := List.countP_append (p := literal q) (l₁ := [158]) (l₂ := [159, 160])
  have hm := merge_left (literal (valuationOf q) (158)) (literal (valuationOf q) (313)) (countLit q [158]) (countLit q [159, 160]) (count313 q) 1 (meaning158 q) (meaning313 q) hs
  change valuationOf q 158 = false ∨ valuationOf q 313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause197 (q : Snake 81) (h : Conditions q) : valuation q 158 = false ∨ valuation q 313 = true := counterClause197 (baseVal q)

theorem counterClause198 (q : Nat → Bool) : valuationOf q 162 = false ∨ valuationOf q 315 = true := by
  have hs : count315 q = (countLit q [162]) + (countLit q [163]) := List.countP_append (p := literal q) (l₁ := [162]) (l₂ := [163])
  have hm := merge_left (literal (valuationOf q) (162)) (literal (valuationOf q) (315)) (countLit q [162]) (countLit q [163]) (count315 q) 1 (meaning162 q) (meaning315 q) hs
  change valuationOf q 162 = false ∨ valuationOf q 315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause198 (q : Snake 81) (h : Conditions q) : valuation q 162 = false ∨ valuation q 315 = true := counterClause198 (baseVal q)

theorem counterClause199 (q : Nat → Bool) : valuationOf q 315 = false ∨ valuationOf q 317 = true := by
  have hs : count317 q = (countLit q [161]) + (countLit q [162, 163]) := List.countP_append (p := literal q) (l₁ := [161]) (l₂ := [162, 163])
  have hm := merge_right (literal (valuationOf q) (315)) (literal (valuationOf q) (317)) (countLit q [161]) (countLit q [162, 163]) (count317 q) 1 (meaning315 q) (meaning317 q) hs
  change valuationOf q 315 = false ∨ valuationOf q 317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause199 (q : Snake 81) (h : Conditions q) : valuation q 315 = false ∨ valuation q 317 = true := counterClause199 (baseVal q)

theorem counterClause200 (q : Nat → Bool) : valuationOf q 317 = false ∨ valuationOf q 319 = true := by
  have hs : count319 q = (countLit q [158, 159, 160]) + (countLit q [161, 162, 163]) := List.countP_append (p := literal q) (l₁ := [158, 159, 160]) (l₂ := [161, 162, 163])
  have hm := merge_right (literal (valuationOf q) (317)) (literal (valuationOf q) (319)) (countLit q [158, 159, 160]) (countLit q [161, 162, 163]) (count319 q) 1 (meaning317 q) (meaning319 q) hs
  change valuationOf q 317 = false ∨ valuationOf q 319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause200 (q : Snake 81) (h : Conditions q) : valuation q 317 = false ∨ valuation q 319 = true := counterClause200 (baseVal q)

theorem counterClause201 (q : Nat → Bool) : valuationOf q 313 = false ∨ valuationOf q 319 = true := by
  have hs : count319 q = (countLit q [158, 159, 160]) + (countLit q [161, 162, 163]) := List.countP_append (p := literal q) (l₁ := [158, 159, 160]) (l₂ := [161, 162, 163])
  have hm := merge_left (literal (valuationOf q) (313)) (literal (valuationOf q) (319)) (countLit q [158, 159, 160]) (countLit q [161, 162, 163]) (count319 q) 1 (meaning313 q) (meaning319 q) hs
  change valuationOf q 313 = false ∨ valuationOf q 319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause201 (q : Snake 81) (h : Conditions q) : valuation q 313 = false ∨ valuation q 319 = true := counterClause201 (baseVal q)

theorem counterClause202 (q : Nat → Bool) : valuationOf q 319 = false ∨ valuationOf q 321 = true := by
  have hs : count321 q = (countLit q [152, 153, 154, 155, 156, 157]) + (countLit q [158, 159, 160, 161, 162, 163]) := List.countP_append (p := literal q) (l₁ := [152, 153, 154, 155, 156, 157]) (l₂ := [158, 159, 160, 161, 162, 163])
  have hm := merge_right (literal (valuationOf q) (319)) (literal (valuationOf q) (321)) (countLit q [152, 153, 154, 155, 156, 157]) (countLit q [158, 159, 160, 161, 162, 163]) (count321 q) 1 (meaning319 q) (meaning321 q) hs
  change valuationOf q 319 = false ∨ valuationOf q 321 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause202 (q : Snake 81) (h : Conditions q) : valuation q 319 = false ∨ valuation q 321 = true := counterClause202 (baseVal q)

theorem counterClause203 (q : Nat → Bool) : valuationOf q 309 = false ∨ valuationOf q 321 = true := by
  have hs : count321 q = (countLit q [152, 153, 154, 155, 156, 157]) + (countLit q [158, 159, 160, 161, 162, 163]) := List.countP_append (p := literal q) (l₁ := [152, 153, 154, 155, 156, 157]) (l₂ := [158, 159, 160, 161, 162, 163])
  have hm := merge_left (literal (valuationOf q) (309)) (literal (valuationOf q) (321)) (countLit q [152, 153, 154, 155, 156, 157]) (countLit q [158, 159, 160, 161, 162, 163]) (count321 q) 1 (meaning309 q) (meaning321 q) hs
  change valuationOf q 309 = false ∨ valuationOf q 321 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause203 (q : Snake 81) (h : Conditions q) : valuation q 309 = false ∨ valuation q 321 = true := counterClause203 (baseVal q)

theorem counterClause204 (q : Nat → Bool) : valuationOf q 165 = false ∨ valuationOf q 323 = true := by
  have hs : count323 q = (countLit q [165]) + (countLit q [166]) := List.countP_append (p := literal q) (l₁ := [165]) (l₂ := [166])
  have hm := merge_left (literal (valuationOf q) (165)) (literal (valuationOf q) (323)) (countLit q [165]) (countLit q [166]) (count323 q) 1 (meaning165 q) (meaning323 q) hs
  change valuationOf q 165 = false ∨ valuationOf q 323 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause204 (q : Snake 81) (h : Conditions q) : valuation q 165 = false ∨ valuation q 323 = true := counterClause204 (baseVal q)

theorem counterClause205 (q : Nat → Bool) : valuationOf q 323 = false ∨ valuationOf q 325 = true := by
  have hs : count325 q = (countLit q [164]) + (countLit q [165, 166]) := List.countP_append (p := literal q) (l₁ := [164]) (l₂ := [165, 166])
  have hm := merge_right (literal (valuationOf q) (323)) (literal (valuationOf q) (325)) (countLit q [164]) (countLit q [165, 166]) (count325 q) 1 (meaning323 q) (meaning325 q) hs
  change valuationOf q 323 = false ∨ valuationOf q 325 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause205 (q : Snake 81) (h : Conditions q) : valuation q 323 = false ∨ valuation q 325 = true := counterClause205 (baseVal q)

theorem counterClause206 (q : Nat → Bool) : valuationOf q 164 = false ∨ valuationOf q 325 = true := by
  have hs : count325 q = (countLit q [164]) + (countLit q [165, 166]) := List.countP_append (p := literal q) (l₁ := [164]) (l₂ := [165, 166])
  have hm := merge_left (literal (valuationOf q) (164)) (literal (valuationOf q) (325)) (countLit q [164]) (countLit q [165, 166]) (count325 q) 1 (meaning164 q) (meaning325 q) hs
  change valuationOf q 164 = false ∨ valuationOf q 325 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause206 (q : Snake 81) (h : Conditions q) : valuation q 164 = false ∨ valuation q 325 = true := counterClause206 (baseVal q)

theorem counterClause207 (q : Nat → Bool) : valuationOf q 167 = false ∨ valuationOf q 329 = true := by
  have hs : count329 q = (countLit q [167]) + (countLit q [168, 170]) := List.countP_append (p := literal q) (l₁ := [167]) (l₂ := [168, 170])
  have hm := merge_left (literal (valuationOf q) (167)) (literal (valuationOf q) (329)) (countLit q [167]) (countLit q [168, 170]) (count329 q) 1 (meaning167 q) (meaning329 q) hs
  change valuationOf q 167 = false ∨ valuationOf q 329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause207 (q : Snake 81) (h : Conditions q) : valuation q 167 = false ∨ valuation q 329 = true := counterClause207 (baseVal q)

theorem counterClause208 (q : Nat → Bool) : valuationOf q 329 = false ∨ valuationOf q 331 = true := by
  have hs : count331 q = (countLit q [164, 165, 166]) + (countLit q [167, 168, 170]) := List.countP_append (p := literal q) (l₁ := [164, 165, 166]) (l₂ := [167, 168, 170])
  have hm := merge_right (literal (valuationOf q) (329)) (literal (valuationOf q) (331)) (countLit q [164, 165, 166]) (countLit q [167, 168, 170]) (count331 q) 1 (meaning329 q) (meaning331 q) hs
  change valuationOf q 329 = false ∨ valuationOf q 331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause208 (q : Snake 81) (h : Conditions q) : valuation q 329 = false ∨ valuation q 331 = true := counterClause208 (baseVal q)

theorem counterClause209 (q : Nat → Bool) : valuationOf q 325 = false ∨ valuationOf q 331 = true := by
  have hs : count331 q = (countLit q [164, 165, 166]) + (countLit q [167, 168, 170]) := List.countP_append (p := literal q) (l₁ := [164, 165, 166]) (l₂ := [167, 168, 170])
  have hm := merge_left (literal (valuationOf q) (325)) (literal (valuationOf q) (331)) (countLit q [164, 165, 166]) (countLit q [167, 168, 170]) (count331 q) 1 (meaning325 q) (meaning331 q) hs
  change valuationOf q 325 = false ∨ valuationOf q 331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause209 (q : Snake 81) (h : Conditions q) : valuation q 325 = false ∨ valuation q 331 = true := counterClause209 (baseVal q)

theorem counterClause210 (q : Nat → Bool) : valuationOf q 172 = false ∨ valuationOf q 333 = true := by
  have hs : count333 q = (countLit q [172]) + (countLit q [173]) := List.countP_append (p := literal q) (l₁ := [172]) (l₂ := [173])
  have hm := merge_left (literal (valuationOf q) (172)) (literal (valuationOf q) (333)) (countLit q [172]) (countLit q [173]) (count333 q) 1 (meaning172 q) (meaning333 q) hs
  change valuationOf q 172 = false ∨ valuationOf q 333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause210 (q : Snake 81) (h : Conditions q) : valuation q 172 = false ∨ valuation q 333 = true := counterClause210 (baseVal q)

theorem counterClause211 (q : Nat → Bool) : valuationOf q 333 = false ∨ valuationOf q 335 = true := by
  have hs : count335 q = (countLit q [171]) + (countLit q [172, 173]) := List.countP_append (p := literal q) (l₁ := [171]) (l₂ := [172, 173])
  have hm := merge_right (literal (valuationOf q) (333)) (literal (valuationOf q) (335)) (countLit q [171]) (countLit q [172, 173]) (count335 q) 1 (meaning333 q) (meaning335 q) hs
  change valuationOf q 333 = false ∨ valuationOf q 335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause211 (q : Snake 81) (h : Conditions q) : valuation q 333 = false ∨ valuation q 335 = true := counterClause211 (baseVal q)

theorem counterClause212 (q : Nat → Bool) : valuationOf q 171 = false ∨ valuationOf q 335 = true := by
  have hs : count335 q = (countLit q [171]) + (countLit q [172, 173]) := List.countP_append (p := literal q) (l₁ := [171]) (l₂ := [172, 173])
  have hm := merge_left (literal (valuationOf q) (171)) (literal (valuationOf q) (335)) (countLit q [171]) (countLit q [172, 173]) (count335 q) 1 (meaning171 q) (meaning335 q) hs
  change valuationOf q 171 = false ∨ valuationOf q 335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause212 (q : Snake 81) (h : Conditions q) : valuation q 171 = false ∨ valuation q 335 = true := counterClause212 (baseVal q)

theorem counterClause213 (q : Nat → Bool) : valuationOf q 175 = false ∨ valuationOf q 337 = true := by
  have hs : count337 q = (countLit q [174]) + (countLit q [175]) := List.countP_append (p := literal q) (l₁ := [174]) (l₂ := [175])
  have hm := merge_right (literal (valuationOf q) (175)) (literal (valuationOf q) (337)) (countLit q [174]) (countLit q [175]) (count337 q) 1 (meaning175 q) (meaning337 q) hs
  change valuationOf q 175 = false ∨ valuationOf q 337 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause213 (q : Snake 81) (h : Conditions q) : valuation q 175 = false ∨ valuation q 337 = true := counterClause213 (baseVal q)

theorem counterClause214 (q : Nat → Bool) : valuationOf q 337 = false ∨ valuationOf q 341 = true := by
  have hs : count341 q = (countLit q [174, 175]) + (countLit q [176, 177]) := List.countP_append (p := literal q) (l₁ := [174, 175]) (l₂ := [176, 177])
  have hm := merge_left (literal (valuationOf q) (337)) (literal (valuationOf q) (341)) (countLit q [174, 175]) (countLit q [176, 177]) (count341 q) 1 (meaning337 q) (meaning341 q) hs
  change valuationOf q 337 = false ∨ valuationOf q 341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause214 (q : Snake 81) (h : Conditions q) : valuation q 337 = false ∨ valuation q 341 = true := counterClause214 (baseVal q)

theorem counterClause215 (q : Nat → Bool) : valuationOf q 341 = false ∨ valuationOf q 343 = true := by
  have hs : count343 q = (countLit q [171, 172, 173]) + (countLit q [174, 175, 176, 177]) := List.countP_append (p := literal q) (l₁ := [171, 172, 173]) (l₂ := [174, 175, 176, 177])
  have hm := merge_right (literal (valuationOf q) (341)) (literal (valuationOf q) (343)) (countLit q [171, 172, 173]) (countLit q [174, 175, 176, 177]) (count343 q) 1 (meaning341 q) (meaning343 q) hs
  change valuationOf q 341 = false ∨ valuationOf q 343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause215 (q : Snake 81) (h : Conditions q) : valuation q 341 = false ∨ valuation q 343 = true := counterClause215 (baseVal q)

theorem counterClause216 (q : Nat → Bool) : valuationOf q 335 = false ∨ valuationOf q 343 = true := by
  have hs : count343 q = (countLit q [171, 172, 173]) + (countLit q [174, 175, 176, 177]) := List.countP_append (p := literal q) (l₁ := [171, 172, 173]) (l₂ := [174, 175, 176, 177])
  have hm := merge_left (literal (valuationOf q) (335)) (literal (valuationOf q) (343)) (countLit q [171, 172, 173]) (countLit q [174, 175, 176, 177]) (count343 q) 1 (meaning335 q) (meaning343 q) hs
  change valuationOf q 335 = false ∨ valuationOf q 343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause216 (q : Snake 81) (h : Conditions q) : valuation q 335 = false ∨ valuation q 343 = true := counterClause216 (baseVal q)

theorem counterClause217 (q : Nat → Bool) : valuationOf q 343 = false ∨ valuationOf q 345 = true := by
  have hs : count345 q = (countLit q [164, 165, 166, 167, 168, 170]) + (countLit q [171, 172, 173, 174, 175, 176, 177]) := List.countP_append (p := literal q) (l₁ := [164, 165, 166, 167, 168, 170]) (l₂ := [171, 172, 173, 174, 175, 176, 177])
  have hm := merge_right (literal (valuationOf q) (343)) (literal (valuationOf q) (345)) (countLit q [164, 165, 166, 167, 168, 170]) (countLit q [171, 172, 173, 174, 175, 176, 177]) (count345 q) 1 (meaning343 q) (meaning345 q) hs
  change valuationOf q 343 = false ∨ valuationOf q 345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause217 (q : Snake 81) (h : Conditions q) : valuation q 343 = false ∨ valuation q 345 = true := counterClause217 (baseVal q)

theorem counterClause218 (q : Nat → Bool) : valuationOf q 331 = false ∨ valuationOf q 345 = true := by
  have hs : count345 q = (countLit q [164, 165, 166, 167, 168, 170]) + (countLit q [171, 172, 173, 174, 175, 176, 177]) := List.countP_append (p := literal q) (l₁ := [164, 165, 166, 167, 168, 170]) (l₂ := [171, 172, 173, 174, 175, 176, 177])
  have hm := merge_left (literal (valuationOf q) (331)) (literal (valuationOf q) (345)) (countLit q [164, 165, 166, 167, 168, 170]) (countLit q [171, 172, 173, 174, 175, 176, 177]) (count345 q) 1 (meaning331 q) (meaning345 q) hs
  change valuationOf q 331 = false ∨ valuationOf q 345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause218 (q : Snake 81) (h : Conditions q) : valuation q 331 = false ∨ valuation q 345 = true := counterClause218 (baseVal q)

theorem counterClause219 (q : Nat → Bool) : valuationOf q 331 = false ∨ valuationOf q 343 = false ∨ valuationOf q 346 = true := by
  have hs : count345 q = (countLit q [164, 165, 166, 167, 168, 170]) + (countLit q [171, 172, 173, 174, 175, 176, 177]) := List.countP_append (p := literal q) (l₁ := [164, 165, 166, 167, 168, 170]) (l₂ := [171, 172, 173, 174, 175, 176, 177])
  have hm := merge_two (literal (valuationOf q) (331)) (literal (valuationOf q) (343)) (literal (valuationOf q) (346)) (countLit q [164, 165, 166, 167, 168, 170]) (countLit q [171, 172, 173, 174, 175, 176, 177]) (count345 q) 1 1 (meaning331 q) (meaning343 q) (meaning346 q) hs
  change valuationOf q 331 = false ∨ valuationOf q 343 = false ∨ valuationOf q 346 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause219 (q : Snake 81) (h : Conditions q) : valuation q 331 = false ∨ valuation q 343 = false ∨ valuation q 346 = true := counterClause219 (baseVal q)

theorem counterClause220 (q : Nat → Bool) : valuationOf q 345 = false ∨ valuationOf q 347 = true := by
  have hs : count347 q = (countLit q [152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) + (countLit q [164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177]) := List.countP_append (p := literal q) (l₁ := [152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) (l₂ := [164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177])
  have hm := merge_right (literal (valuationOf q) (345)) (literal (valuationOf q) (347)) (countLit q [152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) (countLit q [164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177]) (count347 q) 1 (meaning345 q) (meaning347 q) hs
  change valuationOf q 345 = false ∨ valuationOf q 347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause220 (q : Snake 81) (h : Conditions q) : valuation q 345 = false ∨ valuation q 347 = true := counterClause220 (baseVal q)

theorem counterClause221 (q : Nat → Bool) : valuationOf q 346 = false ∨ valuationOf q 348 = true := by
  have hs : count347 q = (countLit q [152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) + (countLit q [164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177]) := List.countP_append (p := literal q) (l₁ := [152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) (l₂ := [164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177])
  have hm := merge_right (literal (valuationOf q) (346)) (literal (valuationOf q) (348)) (countLit q [152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) (countLit q [164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177]) (count347 q) 2 (meaning346 q) (meaning348 q) hs
  change valuationOf q 346 = false ∨ valuationOf q 348 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause221 (q : Snake 81) (h : Conditions q) : valuation q 346 = false ∨ valuation q 348 = true := counterClause221 (baseVal q)

theorem counterClause222 (q : Nat → Bool) : valuationOf q 321 = false ∨ valuationOf q 347 = true := by
  have hs : count347 q = (countLit q [152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) + (countLit q [164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177]) := List.countP_append (p := literal q) (l₁ := [152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) (l₂ := [164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177])
  have hm := merge_left (literal (valuationOf q) (321)) (literal (valuationOf q) (347)) (countLit q [152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) (countLit q [164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177]) (count347 q) 1 (meaning321 q) (meaning347 q) hs
  change valuationOf q 321 = false ∨ valuationOf q 347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause222 (q : Snake 81) (h : Conditions q) : valuation q 321 = false ∨ valuation q 347 = true := counterClause222 (baseVal q)

theorem counterClause223 (q : Nat → Bool) : valuationOf q 321 = false ∨ valuationOf q 345 = false ∨ valuationOf q 348 = true := by
  have hs : count347 q = (countLit q [152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) + (countLit q [164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177]) := List.countP_append (p := literal q) (l₁ := [152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) (l₂ := [164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177])
  have hm := merge_two (literal (valuationOf q) (321)) (literal (valuationOf q) (345)) (literal (valuationOf q) (348)) (countLit q [152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) (countLit q [164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177]) (count347 q) 1 1 (meaning321 q) (meaning345 q) (meaning348 q) hs
  change valuationOf q 321 = false ∨ valuationOf q 345 = false ∨ valuationOf q 348 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause223 (q : Snake 81) (h : Conditions q) : valuation q 321 = false ∨ valuation q 345 = false ∨ valuation q 348 = true := counterClause223 (baseVal q)

theorem counterClause224 (q : Nat → Bool) : valuationOf q 178 = false ∨ valuationOf q 351 = true := by
  have hs : count351 q = (countLit q [178]) + (countLit q [179, 180]) := List.countP_append (p := literal q) (l₁ := [178]) (l₂ := [179, 180])
  have hm := merge_left (literal (valuationOf q) (178)) (literal (valuationOf q) (351)) (countLit q [178]) (countLit q [179, 180]) (count351 q) 1 (meaning178 q) (meaning351 q) hs
  change valuationOf q 178 = false ∨ valuationOf q 351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause224 (q : Snake 81) (h : Conditions q) : valuation q 178 = false ∨ valuation q 351 = true := counterClause224 (baseVal q)

theorem block6 (q : Snake 81) (h : Conditions q) : B112E154.Block6 (valuation q) :=
  ⟨clause193 q h, clause194 q h, clause195 q h, clause196 q h, clause197 q h, clause198 q h, clause199 q h, clause200 q h, clause201 q h, clause202 q h, clause203 q h, clause204 q h, clause205 q h, clause206 q h, clause207 q h, clause208 q h, clause209 q h, clause210 q h, clause211 q h, clause212 q h, clause213 q h, clause214 q h, clause215 q h, clause216 q h, clause217 q h, clause218 q h, clause219 q h, clause220 q h, clause221 q h, clause222 q h, clause223 q h, clause224 q h⟩

end
end Snake9.Regrowth.E112154
