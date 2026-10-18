import E112115Semantics
import B112E115Inputs
namespace Snake9.Regrowth.E112115
noncomputable section
local instance blockDec19 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause609 (q : Nat → Bool) : valuationOf q 151 = false ∨ valuationOf q 295 = true := by
  have hs : count295 q = (countLit q [150]) + (countLit q [151]) := List.countP_append (p := literal q) (l₁ := [150]) (l₂ := [151])
  have hm := merge_right (literal (valuationOf q) (151)) (literal (valuationOf q) (295)) (countLit q [150]) (countLit q [151]) (count295 q) 1 (meaning151 q) (meaning295 q) hs
  change valuationOf q 151 = false ∨ valuationOf q 295 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause609 (q : Snake 81) (h : Conditions q) : valuation q 151 = false ∨ valuation q 295 = true := counterClause609 (baseVal q)

theorem counterClause610 (q : Nat → Bool) : valuationOf q 153 = false ∨ valuationOf q 297 = true := by
  have hs : count297 q = (countLit q [152]) + (countLit q [153]) := List.countP_append (p := literal q) (l₁ := [152]) (l₂ := [153])
  have hm := merge_right (literal (valuationOf q) (153)) (literal (valuationOf q) (297)) (countLit q [152]) (countLit q [153]) (count297 q) 1 (meaning153 q) (meaning297 q) hs
  change valuationOf q 153 = false ∨ valuationOf q 297 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause610 (q : Snake 81) (h : Conditions q) : valuation q 153 = false ∨ valuation q 297 = true := counterClause610 (baseVal q)

theorem counterClause611 (q : Nat → Bool) : valuationOf q 152 = false ∨ valuationOf q 297 = true := by
  have hs : count297 q = (countLit q [152]) + (countLit q [153]) := List.countP_append (p := literal q) (l₁ := [152]) (l₂ := [153])
  have hm := merge_left (literal (valuationOf q) (152)) (literal (valuationOf q) (297)) (countLit q [152]) (countLit q [153]) (count297 q) 1 (meaning152 q) (meaning297 q) hs
  change valuationOf q 152 = false ∨ valuationOf q 297 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause611 (q : Snake 81) (h : Conditions q) : valuation q 152 = false ∨ valuation q 297 = true := counterClause611 (baseVal q)

theorem counterClause612 (q : Nat → Bool) : valuationOf q 297 = false ∨ valuationOf q 299 = true := by
  have hs : count299 q = (countLit q [150, 151]) + (countLit q [152, 153]) := List.countP_append (p := literal q) (l₁ := [150, 151]) (l₂ := [152, 153])
  have hm := merge_right (literal (valuationOf q) (297)) (literal (valuationOf q) (299)) (countLit q [150, 151]) (countLit q [152, 153]) (count299 q) 1 (meaning297 q) (meaning299 q) hs
  change valuationOf q 297 = false ∨ valuationOf q 299 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause612 (q : Snake 81) (h : Conditions q) : valuation q 297 = false ∨ valuation q 299 = true := counterClause612 (baseVal q)

theorem counterClause613 (q : Nat → Bool) : valuationOf q 295 = false ∨ valuationOf q 299 = true := by
  have hs : count299 q = (countLit q [150, 151]) + (countLit q [152, 153]) := List.countP_append (p := literal q) (l₁ := [150, 151]) (l₂ := [152, 153])
  have hm := merge_left (literal (valuationOf q) (295)) (literal (valuationOf q) (299)) (countLit q [150, 151]) (countLit q [152, 153]) (count299 q) 1 (meaning295 q) (meaning299 q) hs
  change valuationOf q 295 = false ∨ valuationOf q 299 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause613 (q : Snake 81) (h : Conditions q) : valuation q 295 = false ∨ valuation q 299 = true := counterClause613 (baseVal q)

theorem counterClause614 (q : Nat → Bool) : valuationOf q 299 = false ∨ valuationOf q 301 = true := by
  have hs : count301 q = (countLit q [147, 148, 149]) + (countLit q [150, 151, 152, 153]) := List.countP_append (p := literal q) (l₁ := [147, 148, 149]) (l₂ := [150, 151, 152, 153])
  have hm := merge_right (literal (valuationOf q) (299)) (literal (valuationOf q) (301)) (countLit q [147, 148, 149]) (countLit q [150, 151, 152, 153]) (count301 q) 1 (meaning299 q) (meaning301 q) hs
  change valuationOf q 299 = false ∨ valuationOf q 301 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause614 (q : Snake 81) (h : Conditions q) : valuation q 299 = false ∨ valuation q 301 = true := counterClause614 (baseVal q)

theorem counterClause615 (q : Nat → Bool) : valuationOf q 293 = false ∨ valuationOf q 301 = true := by
  have hs : count301 q = (countLit q [147, 148, 149]) + (countLit q [150, 151, 152, 153]) := List.countP_append (p := literal q) (l₁ := [147, 148, 149]) (l₂ := [150, 151, 152, 153])
  have hm := merge_left (literal (valuationOf q) (293)) (literal (valuationOf q) (301)) (countLit q [147, 148, 149]) (countLit q [150, 151, 152, 153]) (count301 q) 1 (meaning293 q) (meaning301 q) hs
  change valuationOf q 293 = false ∨ valuationOf q 301 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause615 (q : Snake 81) (h : Conditions q) : valuation q 293 = false ∨ valuation q 301 = true := counterClause615 (baseVal q)

theorem counterClause616 (q : Nat → Bool) : valuationOf q 293 = false ∨ valuationOf q 299 = false ∨ valuationOf q 302 = true := by
  have hs : count301 q = (countLit q [147, 148, 149]) + (countLit q [150, 151, 152, 153]) := List.countP_append (p := literal q) (l₁ := [147, 148, 149]) (l₂ := [150, 151, 152, 153])
  have hm := merge_two (literal (valuationOf q) (293)) (literal (valuationOf q) (299)) (literal (valuationOf q) (302)) (countLit q [147, 148, 149]) (countLit q [150, 151, 152, 153]) (count301 q) 1 1 (meaning293 q) (meaning299 q) (meaning302 q) hs
  change valuationOf q 293 = false ∨ valuationOf q 299 = false ∨ valuationOf q 302 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause616 (q : Snake 81) (h : Conditions q) : valuation q 293 = false ∨ valuation q 299 = false ∨ valuation q 302 = true := counterClause616 (baseVal q)

theorem counterClause617 (q : Nat → Bool) : valuationOf q 154 = false ∨ valuationOf q 305 = true := by
  have hs : count305 q = (countLit q [154]) + (countLit q [155, 156]) := List.countP_append (p := literal q) (l₁ := [154]) (l₂ := [155, 156])
  have hm := merge_left (literal (valuationOf q) (154)) (literal (valuationOf q) (305)) (countLit q [154]) (countLit q [155, 156]) (count305 q) 1 (meaning154 q) (meaning305 q) hs
  change valuationOf q 154 = false ∨ valuationOf q 305 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause617 (q : Snake 81) (h : Conditions q) : valuation q 154 = false ∨ valuation q 305 = true := counterClause617 (baseVal q)

theorem counterClause618 (q : Nat → Bool) : valuationOf q 158 = false ∨ valuationOf q 307 = true := by
  have hs : count307 q = (countLit q [157]) + (countLit q [158]) := List.countP_append (p := literal q) (l₁ := [157]) (l₂ := [158])
  have hm := merge_right (literal (valuationOf q) (158)) (literal (valuationOf q) (307)) (countLit q [157]) (countLit q [158]) (count307 q) 1 (meaning158 q) (meaning307 q) hs
  change valuationOf q 158 = false ∨ valuationOf q 307 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause618 (q : Snake 81) (h : Conditions q) : valuation q 158 = false ∨ valuation q 307 = true := counterClause618 (baseVal q)

theorem counterClause619 (q : Nat → Bool) : valuationOf q 159 = false ∨ valuationOf q 309 = true := by
  have hs : count309 q = (countLit q [159]) + (countLit q [160]) := List.countP_append (p := literal q) (l₁ := [159]) (l₂ := [160])
  have hm := merge_left (literal (valuationOf q) (159)) (literal (valuationOf q) (309)) (countLit q [159]) (countLit q [160]) (count309 q) 1 (meaning159 q) (meaning309 q) hs
  change valuationOf q 159 = false ∨ valuationOf q 309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause619 (q : Snake 81) (h : Conditions q) : valuation q 159 = false ∨ valuation q 309 = true := counterClause619 (baseVal q)

theorem counterClause620 (q : Nat → Bool) : valuationOf q 309 = false ∨ valuationOf q 311 = true := by
  have hs : count311 q = (countLit q [157, 158]) + (countLit q [159, 160]) := List.countP_append (p := literal q) (l₁ := [157, 158]) (l₂ := [159, 160])
  have hm := merge_right (literal (valuationOf q) (309)) (literal (valuationOf q) (311)) (countLit q [157, 158]) (countLit q [159, 160]) (count311 q) 1 (meaning309 q) (meaning311 q) hs
  change valuationOf q 309 = false ∨ valuationOf q 311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause620 (q : Snake 81) (h : Conditions q) : valuation q 309 = false ∨ valuation q 311 = true := counterClause620 (baseVal q)

theorem counterClause621 (q : Nat → Bool) : valuationOf q 307 = false ∨ valuationOf q 311 = true := by
  have hs : count311 q = (countLit q [157, 158]) + (countLit q [159, 160]) := List.countP_append (p := literal q) (l₁ := [157, 158]) (l₂ := [159, 160])
  have hm := merge_left (literal (valuationOf q) (307)) (literal (valuationOf q) (311)) (countLit q [157, 158]) (countLit q [159, 160]) (count311 q) 1 (meaning307 q) (meaning311 q) hs
  change valuationOf q 307 = false ∨ valuationOf q 311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause621 (q : Snake 81) (h : Conditions q) : valuation q 307 = false ∨ valuation q 311 = true := counterClause621 (baseVal q)

theorem counterClause622 (q : Nat → Bool) : valuationOf q 311 = false ∨ valuationOf q 313 = true := by
  have hs : count313 q = (countLit q [154, 155, 156]) + (countLit q [157, 158, 159, 160]) := List.countP_append (p := literal q) (l₁ := [154, 155, 156]) (l₂ := [157, 158, 159, 160])
  have hm := merge_right (literal (valuationOf q) (311)) (literal (valuationOf q) (313)) (countLit q [154, 155, 156]) (countLit q [157, 158, 159, 160]) (count313 q) 1 (meaning311 q) (meaning313 q) hs
  change valuationOf q 311 = false ∨ valuationOf q 313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause622 (q : Snake 81) (h : Conditions q) : valuation q 311 = false ∨ valuation q 313 = true := counterClause622 (baseVal q)

theorem counterClause623 (q : Nat → Bool) : valuationOf q 305 = false ∨ valuationOf q 313 = true := by
  have hs : count313 q = (countLit q [154, 155, 156]) + (countLit q [157, 158, 159, 160]) := List.countP_append (p := literal q) (l₁ := [154, 155, 156]) (l₂ := [157, 158, 159, 160])
  have hm := merge_left (literal (valuationOf q) (305)) (literal (valuationOf q) (313)) (countLit q [154, 155, 156]) (countLit q [157, 158, 159, 160]) (count313 q) 1 (meaning305 q) (meaning313 q) hs
  change valuationOf q 305 = false ∨ valuationOf q 313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause623 (q : Snake 81) (h : Conditions q) : valuation q 305 = false ∨ valuation q 313 = true := counterClause623 (baseVal q)

theorem counterClause624 (q : Nat → Bool) : valuationOf q 305 = false ∨ valuationOf q 311 = false ∨ valuationOf q 314 = true := by
  have hs : count313 q = (countLit q [154, 155, 156]) + (countLit q [157, 158, 159, 160]) := List.countP_append (p := literal q) (l₁ := [154, 155, 156]) (l₂ := [157, 158, 159, 160])
  have hm := merge_two (literal (valuationOf q) (305)) (literal (valuationOf q) (311)) (literal (valuationOf q) (314)) (countLit q [154, 155, 156]) (countLit q [157, 158, 159, 160]) (count313 q) 1 1 (meaning305 q) (meaning311 q) (meaning314 q) hs
  change valuationOf q 305 = false ∨ valuationOf q 311 = false ∨ valuationOf q 314 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause624 (q : Snake 81) (h : Conditions q) : valuation q 305 = false ∨ valuation q 311 = false ∨ valuation q 314 = true := counterClause624 (baseVal q)

theorem counterClause625 (q : Nat → Bool) : valuationOf q 313 = false ∨ valuationOf q 315 = true := by
  have hs : count315 q = (countLit q [147, 148, 149, 150, 151, 152, 153]) + (countLit q [154, 155, 156, 157, 158, 159, 160]) := List.countP_append (p := literal q) (l₁ := [147, 148, 149, 150, 151, 152, 153]) (l₂ := [154, 155, 156, 157, 158, 159, 160])
  have hm := merge_right (literal (valuationOf q) (313)) (literal (valuationOf q) (315)) (countLit q [147, 148, 149, 150, 151, 152, 153]) (countLit q [154, 155, 156, 157, 158, 159, 160]) (count315 q) 1 (meaning313 q) (meaning315 q) hs
  change valuationOf q 313 = false ∨ valuationOf q 315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause625 (q : Snake 81) (h : Conditions q) : valuation q 313 = false ∨ valuation q 315 = true := counterClause625 (baseVal q)

theorem counterClause626 (q : Nat → Bool) : valuationOf q 314 = false ∨ valuationOf q 316 = true := by
  have hs : count315 q = (countLit q [147, 148, 149, 150, 151, 152, 153]) + (countLit q [154, 155, 156, 157, 158, 159, 160]) := List.countP_append (p := literal q) (l₁ := [147, 148, 149, 150, 151, 152, 153]) (l₂ := [154, 155, 156, 157, 158, 159, 160])
  have hm := merge_right (literal (valuationOf q) (314)) (literal (valuationOf q) (316)) (countLit q [147, 148, 149, 150, 151, 152, 153]) (countLit q [154, 155, 156, 157, 158, 159, 160]) (count315 q) 2 (meaning314 q) (meaning316 q) hs
  change valuationOf q 314 = false ∨ valuationOf q 316 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause626 (q : Snake 81) (h : Conditions q) : valuation q 314 = false ∨ valuation q 316 = true := counterClause626 (baseVal q)

theorem counterClause627 (q : Nat → Bool) : valuationOf q 301 = false ∨ valuationOf q 315 = true := by
  have hs : count315 q = (countLit q [147, 148, 149, 150, 151, 152, 153]) + (countLit q [154, 155, 156, 157, 158, 159, 160]) := List.countP_append (p := literal q) (l₁ := [147, 148, 149, 150, 151, 152, 153]) (l₂ := [154, 155, 156, 157, 158, 159, 160])
  have hm := merge_left (literal (valuationOf q) (301)) (literal (valuationOf q) (315)) (countLit q [147, 148, 149, 150, 151, 152, 153]) (countLit q [154, 155, 156, 157, 158, 159, 160]) (count315 q) 1 (meaning301 q) (meaning315 q) hs
  change valuationOf q 301 = false ∨ valuationOf q 315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause627 (q : Snake 81) (h : Conditions q) : valuation q 301 = false ∨ valuation q 315 = true := counterClause627 (baseVal q)

theorem counterClause628 (q : Nat → Bool) : valuationOf q 301 = false ∨ valuationOf q 313 = false ∨ valuationOf q 316 = true := by
  have hs : count315 q = (countLit q [147, 148, 149, 150, 151, 152, 153]) + (countLit q [154, 155, 156, 157, 158, 159, 160]) := List.countP_append (p := literal q) (l₁ := [147, 148, 149, 150, 151, 152, 153]) (l₂ := [154, 155, 156, 157, 158, 159, 160])
  have hm := merge_two (literal (valuationOf q) (301)) (literal (valuationOf q) (313)) (literal (valuationOf q) (316)) (countLit q [147, 148, 149, 150, 151, 152, 153]) (countLit q [154, 155, 156, 157, 158, 159, 160]) (count315 q) 1 1 (meaning301 q) (meaning313 q) (meaning316 q) hs
  change valuationOf q 301 = false ∨ valuationOf q 313 = false ∨ valuationOf q 316 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause628 (q : Snake 81) (h : Conditions q) : valuation q 301 = false ∨ valuation q 313 = false ∨ valuation q 316 = true := counterClause628 (baseVal q)

theorem counterClause629 (q : Nat → Bool) : valuationOf q 302 = false ∨ valuationOf q 316 = true := by
  have hs : count315 q = (countLit q [147, 148, 149, 150, 151, 152, 153]) + (countLit q [154, 155, 156, 157, 158, 159, 160]) := List.countP_append (p := literal q) (l₁ := [147, 148, 149, 150, 151, 152, 153]) (l₂ := [154, 155, 156, 157, 158, 159, 160])
  have hm := merge_left (literal (valuationOf q) (302)) (literal (valuationOf q) (316)) (countLit q [147, 148, 149, 150, 151, 152, 153]) (countLit q [154, 155, 156, 157, 158, 159, 160]) (count315 q) 2 (meaning302 q) (meaning316 q) hs
  change valuationOf q 302 = false ∨ valuationOf q 316 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause629 (q : Snake 81) (h : Conditions q) : valuation q 302 = false ∨ valuation q 316 = true := counterClause629 (baseVal q)

theorem counterClause630 (q : Nat → Bool) : valuationOf q 162 = false ∨ valuationOf q 317 = true := by
  have hs : count317 q = (countLit q [162]) + (countLit q [163]) := List.countP_append (p := literal q) (l₁ := [162]) (l₂ := [163])
  have hm := merge_left (literal (valuationOf q) (162)) (literal (valuationOf q) (317)) (countLit q [162]) (countLit q [163]) (count317 q) 1 (meaning162 q) (meaning317 q) hs
  change valuationOf q 162 = false ∨ valuationOf q 317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause630 (q : Snake 81) (h : Conditions q) : valuation q 162 = false ∨ valuation q 317 = true := counterClause630 (baseVal q)

theorem counterClause631 (q : Nat → Bool) : valuationOf q 317 = false ∨ valuationOf q 319 = true := by
  have hs : count319 q = (countLit q [161]) + (countLit q [162, 163]) := List.countP_append (p := literal q) (l₁ := [161]) (l₂ := [162, 163])
  have hm := merge_right (literal (valuationOf q) (317)) (literal (valuationOf q) (319)) (countLit q [161]) (countLit q [162, 163]) (count319 q) 1 (meaning317 q) (meaning319 q) hs
  change valuationOf q 317 = false ∨ valuationOf q 319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause631 (q : Snake 81) (h : Conditions q) : valuation q 317 = false ∨ valuation q 319 = true := counterClause631 (baseVal q)

theorem counterClause632 (q : Nat → Bool) : valuationOf q 161 = false ∨ valuationOf q 319 = true := by
  have hs : count319 q = (countLit q [161]) + (countLit q [162, 163]) := List.countP_append (p := literal q) (l₁ := [161]) (l₂ := [162, 163])
  have hm := merge_left (literal (valuationOf q) (161)) (literal (valuationOf q) (319)) (countLit q [161]) (countLit q [162, 163]) (count319 q) 1 (meaning161 q) (meaning319 q) hs
  change valuationOf q 161 = false ∨ valuationOf q 319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause632 (q : Snake 81) (h : Conditions q) : valuation q 161 = false ∨ valuation q 319 = true := counterClause632 (baseVal q)

theorem counterClause633 (q : Nat → Bool) : valuationOf q 164 = false ∨ valuationOf q 321 = true := by
  have hs : count321 q = (countLit q [164]) + (countLit q [165]) := List.countP_append (p := literal q) (l₁ := [164]) (l₂ := [165])
  have hm := merge_left (literal (valuationOf q) (164)) (literal (valuationOf q) (321)) (countLit q [164]) (countLit q [165]) (count321 q) 1 (meaning164 q) (meaning321 q) hs
  change valuationOf q 164 = false ∨ valuationOf q 321 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause633 (q : Snake 81) (h : Conditions q) : valuation q 164 = false ∨ valuation q 321 = true := counterClause633 (baseVal q)

theorem counterClause634 (q : Nat → Bool) : valuationOf q 321 = false ∨ valuationOf q 325 = true := by
  have hs : count325 q = (countLit q [164, 165]) + (countLit q [166, 167]) := List.countP_append (p := literal q) (l₁ := [164, 165]) (l₂ := [166, 167])
  have hm := merge_left (literal (valuationOf q) (321)) (literal (valuationOf q) (325)) (countLit q [164, 165]) (countLit q [166, 167]) (count325 q) 1 (meaning321 q) (meaning325 q) hs
  change valuationOf q 321 = false ∨ valuationOf q 325 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause634 (q : Snake 81) (h : Conditions q) : valuation q 321 = false ∨ valuation q 325 = true := counterClause634 (baseVal q)

theorem counterClause635 (q : Nat → Bool) : valuationOf q 325 = false ∨ valuationOf q 327 = true := by
  have hs : count327 q = (countLit q [161, 162, 163]) + (countLit q [164, 165, 166, 167]) := List.countP_append (p := literal q) (l₁ := [161, 162, 163]) (l₂ := [164, 165, 166, 167])
  have hm := merge_right (literal (valuationOf q) (325)) (literal (valuationOf q) (327)) (countLit q [161, 162, 163]) (countLit q [164, 165, 166, 167]) (count327 q) 1 (meaning325 q) (meaning327 q) hs
  change valuationOf q 325 = false ∨ valuationOf q 327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause635 (q : Snake 81) (h : Conditions q) : valuation q 325 = false ∨ valuation q 327 = true := counterClause635 (baseVal q)

theorem counterClause636 (q : Nat → Bool) : valuationOf q 319 = false ∨ valuationOf q 327 = true := by
  have hs : count327 q = (countLit q [161, 162, 163]) + (countLit q [164, 165, 166, 167]) := List.countP_append (p := literal q) (l₁ := [161, 162, 163]) (l₂ := [164, 165, 166, 167])
  have hm := merge_left (literal (valuationOf q) (319)) (literal (valuationOf q) (327)) (countLit q [161, 162, 163]) (countLit q [164, 165, 166, 167]) (count327 q) 1 (meaning319 q) (meaning327 q) hs
  change valuationOf q 319 = false ∨ valuationOf q 327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause636 (q : Snake 81) (h : Conditions q) : valuation q 319 = false ∨ valuation q 327 = true := counterClause636 (baseVal q)

theorem counterClause637 (q : Nat → Bool) : valuationOf q 171 = false ∨ valuationOf q 331 = true := by
  have hs : count331 q = (countLit q [170]) + (countLit q [171]) := List.countP_append (p := literal q) (l₁ := [170]) (l₂ := [171])
  have hm := merge_right (literal (valuationOf q) (171)) (literal (valuationOf q) (331)) (countLit q [170]) (countLit q [171]) (count331 q) 1 (meaning171 q) (meaning331 q) hs
  change valuationOf q 171 = false ∨ valuationOf q 331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause637 (q : Snake 81) (h : Conditions q) : valuation q 171 = false ∨ valuation q 331 = true := counterClause637 (baseVal q)

theorem counterClause638 (q : Nat → Bool) : valuationOf q 170 = false ∨ valuationOf q 331 = true := by
  have hs : count331 q = (countLit q [170]) + (countLit q [171]) := List.countP_append (p := literal q) (l₁ := [170]) (l₂ := [171])
  have hm := merge_left (literal (valuationOf q) (170)) (literal (valuationOf q) (331)) (countLit q [170]) (countLit q [171]) (count331 q) 1 (meaning170 q) (meaning331 q) hs
  change valuationOf q 170 = false ∨ valuationOf q 331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause638 (q : Snake 81) (h : Conditions q) : valuation q 170 = false ∨ valuation q 331 = true := counterClause638 (baseVal q)

theorem counterClause639 (q : Nat → Bool) : valuationOf q 331 = false ∨ valuationOf q 333 = true := by
  have hs : count333 q = (countLit q [168, 169]) + (countLit q [170, 171]) := List.countP_append (p := literal q) (l₁ := [168, 169]) (l₂ := [170, 171])
  have hm := merge_right (literal (valuationOf q) (331)) (literal (valuationOf q) (333)) (countLit q [168, 169]) (countLit q [170, 171]) (count333 q) 1 (meaning331 q) (meaning333 q) hs
  change valuationOf q 331 = false ∨ valuationOf q 333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause639 (q : Snake 81) (h : Conditions q) : valuation q 331 = false ∨ valuation q 333 = true := counterClause639 (baseVal q)

theorem counterClause640 (q : Nat → Bool) : valuationOf q 175 = false ∨ valuationOf q 337 = true := by
  have hs : count337 q = (countLit q [174]) + (countLit q [175]) := List.countP_append (p := literal q) (l₁ := [174]) (l₂ := [175])
  have hm := merge_right (literal (valuationOf q) (175)) (literal (valuationOf q) (337)) (countLit q [174]) (countLit q [175]) (count337 q) 1 (meaning175 q) (meaning337 q) hs
  change valuationOf q 175 = false ∨ valuationOf q 337 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause640 (q : Snake 81) (h : Conditions q) : valuation q 175 = false ∨ valuation q 337 = true := counterClause640 (baseVal q)

theorem block19 (q : Snake 81) (h : Conditions q) : B112E115.Block19 (valuation q) :=
  ⟨clause609 q h, clause610 q h, clause611 q h, clause612 q h, clause613 q h, clause614 q h, clause615 q h, clause616 q h, clause617 q h, clause618 q h, clause619 q h, clause620 q h, clause621 q h, clause622 q h, clause623 q h, clause624 q h, clause625 q h, clause626 q h, clause627 q h, clause628 q h, clause629 q h, clause630 q h, clause631 q h, clause632 q h, clause633 q h, clause634 q h, clause635 q h, clause636 q h, clause637 q h, clause638 q h, clause639 q h, clause640 q h⟩

end
end Snake9.Regrowth.E112115
