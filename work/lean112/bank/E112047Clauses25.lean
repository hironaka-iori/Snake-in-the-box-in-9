import E112047Semantics
import B112E047Inputs
namespace Snake9.Regrowth.E112047
noncomputable section
local instance blockDec25 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause801 (q : Nat → Bool) : valuationOf q 299 = false ∨ valuationOf q 301 = true := by
  have hs : count301 q = (countLit q [151, 152]) + (countLit q [153, 154]) := List.countP_append (p := literal q) (l₁ := [151, 152]) (l₂ := [153, 154])
  have hm := merge_right (literal (valuationOf q) (299)) (literal (valuationOf q) (301)) (countLit q [151, 152]) (countLit q [153, 154]) (count301 q) 1 (meaning299 q) (meaning301 q) hs
  change valuationOf q 299 = false ∨ valuationOf q 301 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause801 (q : Snake 81) (h : Conditions q) : valuation q 299 = false ∨ valuation q 301 = true := counterClause801 (baseVal q)

theorem counterClause802 (q : Nat → Bool) : valuationOf q 297 = false ∨ valuationOf q 301 = true := by
  have hs : count301 q = (countLit q [151, 152]) + (countLit q [153, 154]) := List.countP_append (p := literal q) (l₁ := [151, 152]) (l₂ := [153, 154])
  have hm := merge_left (literal (valuationOf q) (297)) (literal (valuationOf q) (301)) (countLit q [151, 152]) (countLit q [153, 154]) (count301 q) 1 (meaning297 q) (meaning301 q) hs
  change valuationOf q 297 = false ∨ valuationOf q 301 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause802 (q : Snake 81) (h : Conditions q) : valuation q 297 = false ∨ valuation q 301 = true := counterClause802 (baseVal q)

theorem counterClause803 (q : Nat → Bool) : valuationOf q 301 = false ∨ valuationOf q 303 = true := by
  have hs : count303 q = (countLit q [148, 149, 150]) + (countLit q [151, 152, 153, 154]) := List.countP_append (p := literal q) (l₁ := [148, 149, 150]) (l₂ := [151, 152, 153, 154])
  have hm := merge_right (literal (valuationOf q) (301)) (literal (valuationOf q) (303)) (countLit q [148, 149, 150]) (countLit q [151, 152, 153, 154]) (count303 q) 1 (meaning301 q) (meaning303 q) hs
  change valuationOf q 301 = false ∨ valuationOf q 303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause803 (q : Snake 81) (h : Conditions q) : valuation q 301 = false ∨ valuation q 303 = true := counterClause803 (baseVal q)

theorem counterClause804 (q : Nat → Bool) : valuationOf q 295 = false ∨ valuationOf q 303 = true := by
  have hs : count303 q = (countLit q [148, 149, 150]) + (countLit q [151, 152, 153, 154]) := List.countP_append (p := literal q) (l₁ := [148, 149, 150]) (l₂ := [151, 152, 153, 154])
  have hm := merge_left (literal (valuationOf q) (295)) (literal (valuationOf q) (303)) (countLit q [148, 149, 150]) (countLit q [151, 152, 153, 154]) (count303 q) 1 (meaning295 q) (meaning303 q) hs
  change valuationOf q 295 = false ∨ valuationOf q 303 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause804 (q : Snake 81) (h : Conditions q) : valuation q 295 = false ∨ valuation q 303 = true := counterClause804 (baseVal q)

theorem counterClause805 (q : Nat → Bool) : valuationOf q 295 = false ∨ valuationOf q 301 = false ∨ valuationOf q 304 = true := by
  have hs : count303 q = (countLit q [148, 149, 150]) + (countLit q [151, 152, 153, 154]) := List.countP_append (p := literal q) (l₁ := [148, 149, 150]) (l₂ := [151, 152, 153, 154])
  have hm := merge_two (literal (valuationOf q) (295)) (literal (valuationOf q) (301)) (literal (valuationOf q) (304)) (countLit q [148, 149, 150]) (countLit q [151, 152, 153, 154]) (count303 q) 1 1 (meaning295 q) (meaning301 q) (meaning304 q) hs
  change valuationOf q 295 = false ∨ valuationOf q 301 = false ∨ valuationOf q 304 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause805 (q : Snake 81) (h : Conditions q) : valuation q 295 = false ∨ valuation q 301 = false ∨ valuation q 304 = true := counterClause805 (baseVal q)

theorem counterClause806 (q : Nat → Bool) : valuationOf q 155 = false ∨ valuationOf q 307 = true := by
  have hs : count307 q = (countLit q [155]) + (countLit q [156, 157]) := List.countP_append (p := literal q) (l₁ := [155]) (l₂ := [156, 157])
  have hm := merge_left (literal (valuationOf q) (155)) (literal (valuationOf q) (307)) (countLit q [155]) (countLit q [156, 157]) (count307 q) 1 (meaning155 q) (meaning307 q) hs
  change valuationOf q 155 = false ∨ valuationOf q 307 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause806 (q : Snake 81) (h : Conditions q) : valuation q 155 = false ∨ valuation q 307 = true := counterClause806 (baseVal q)

theorem counterClause807 (q : Nat → Bool) : valuationOf q 158 = false ∨ valuationOf q 309 = true := by
  have hs : count309 q = (countLit q [158]) + (countLit q [159]) := List.countP_append (p := literal q) (l₁ := [158]) (l₂ := [159])
  have hm := merge_left (literal (valuationOf q) (158)) (literal (valuationOf q) (309)) (countLit q [158]) (countLit q [159]) (count309 q) 1 (meaning158 q) (meaning309 q) hs
  change valuationOf q 158 = false ∨ valuationOf q 309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause807 (q : Snake 81) (h : Conditions q) : valuation q 158 = false ∨ valuation q 309 = true := counterClause807 (baseVal q)

theorem counterClause808 (q : Nat → Bool) : valuationOf q 161 = false ∨ valuationOf q 311 = true := by
  have hs : count311 q = (countLit q [160]) + (countLit q [161]) := List.countP_append (p := literal q) (l₁ := [160]) (l₂ := [161])
  have hm := merge_right (literal (valuationOf q) (161)) (literal (valuationOf q) (311)) (countLit q [160]) (countLit q [161]) (count311 q) 1 (meaning161 q) (meaning311 q) hs
  change valuationOf q 161 = false ∨ valuationOf q 311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause808 (q : Snake 81) (h : Conditions q) : valuation q 161 = false ∨ valuation q 311 = true := counterClause808 (baseVal q)

theorem counterClause809 (q : Nat → Bool) : valuationOf q 160 = false ∨ valuationOf q 311 = true := by
  have hs : count311 q = (countLit q [160]) + (countLit q [161]) := List.countP_append (p := literal q) (l₁ := [160]) (l₂ := [161])
  have hm := merge_left (literal (valuationOf q) (160)) (literal (valuationOf q) (311)) (countLit q [160]) (countLit q [161]) (count311 q) 1 (meaning160 q) (meaning311 q) hs
  change valuationOf q 160 = false ∨ valuationOf q 311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause809 (q : Snake 81) (h : Conditions q) : valuation q 160 = false ∨ valuation q 311 = true := counterClause809 (baseVal q)

theorem counterClause810 (q : Nat → Bool) : valuationOf q 311 = false ∨ valuationOf q 313 = true := by
  have hs : count313 q = (countLit q [158, 159]) + (countLit q [160, 161]) := List.countP_append (p := literal q) (l₁ := [158, 159]) (l₂ := [160, 161])
  have hm := merge_right (literal (valuationOf q) (311)) (literal (valuationOf q) (313)) (countLit q [158, 159]) (countLit q [160, 161]) (count313 q) 1 (meaning311 q) (meaning313 q) hs
  change valuationOf q 311 = false ∨ valuationOf q 313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause810 (q : Snake 81) (h : Conditions q) : valuation q 311 = false ∨ valuation q 313 = true := counterClause810 (baseVal q)

theorem counterClause811 (q : Nat → Bool) : valuationOf q 309 = false ∨ valuationOf q 313 = true := by
  have hs : count313 q = (countLit q [158, 159]) + (countLit q [160, 161]) := List.countP_append (p := literal q) (l₁ := [158, 159]) (l₂ := [160, 161])
  have hm := merge_left (literal (valuationOf q) (309)) (literal (valuationOf q) (313)) (countLit q [158, 159]) (countLit q [160, 161]) (count313 q) 1 (meaning309 q) (meaning313 q) hs
  change valuationOf q 309 = false ∨ valuationOf q 313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause811 (q : Snake 81) (h : Conditions q) : valuation q 309 = false ∨ valuation q 313 = true := counterClause811 (baseVal q)

theorem counterClause812 (q : Nat → Bool) : valuationOf q 309 = false ∨ valuationOf q 311 = false ∨ valuationOf q 314 = true := by
  have hs : count313 q = (countLit q [158, 159]) + (countLit q [160, 161]) := List.countP_append (p := literal q) (l₁ := [158, 159]) (l₂ := [160, 161])
  have hm := merge_two (literal (valuationOf q) (309)) (literal (valuationOf q) (311)) (literal (valuationOf q) (314)) (countLit q [158, 159]) (countLit q [160, 161]) (count313 q) 1 1 (meaning309 q) (meaning311 q) (meaning314 q) hs
  change valuationOf q 309 = false ∨ valuationOf q 311 = false ∨ valuationOf q 314 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause812 (q : Snake 81) (h : Conditions q) : valuation q 309 = false ∨ valuation q 311 = false ∨ valuation q 314 = true := counterClause812 (baseVal q)

theorem counterClause813 (q : Nat → Bool) : valuationOf q 313 = false ∨ valuationOf q 315 = true := by
  have hs : count315 q = (countLit q [155, 156, 157]) + (countLit q [158, 159, 160, 161]) := List.countP_append (p := literal q) (l₁ := [155, 156, 157]) (l₂ := [158, 159, 160, 161])
  have hm := merge_right (literal (valuationOf q) (313)) (literal (valuationOf q) (315)) (countLit q [155, 156, 157]) (countLit q [158, 159, 160, 161]) (count315 q) 1 (meaning313 q) (meaning315 q) hs
  change valuationOf q 313 = false ∨ valuationOf q 315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause813 (q : Snake 81) (h : Conditions q) : valuation q 313 = false ∨ valuation q 315 = true := counterClause813 (baseVal q)

theorem counterClause814 (q : Nat → Bool) : valuationOf q 314 = false ∨ valuationOf q 316 = true := by
  have hs : count315 q = (countLit q [155, 156, 157]) + (countLit q [158, 159, 160, 161]) := List.countP_append (p := literal q) (l₁ := [155, 156, 157]) (l₂ := [158, 159, 160, 161])
  have hm := merge_right (literal (valuationOf q) (314)) (literal (valuationOf q) (316)) (countLit q [155, 156, 157]) (countLit q [158, 159, 160, 161]) (count315 q) 2 (meaning314 q) (meaning316 q) hs
  change valuationOf q 314 = false ∨ valuationOf q 316 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause814 (q : Snake 81) (h : Conditions q) : valuation q 314 = false ∨ valuation q 316 = true := counterClause814 (baseVal q)

theorem counterClause815 (q : Nat → Bool) : valuationOf q 307 = false ∨ valuationOf q 315 = true := by
  have hs : count315 q = (countLit q [155, 156, 157]) + (countLit q [158, 159, 160, 161]) := List.countP_append (p := literal q) (l₁ := [155, 156, 157]) (l₂ := [158, 159, 160, 161])
  have hm := merge_left (literal (valuationOf q) (307)) (literal (valuationOf q) (315)) (countLit q [155, 156, 157]) (countLit q [158, 159, 160, 161]) (count315 q) 1 (meaning307 q) (meaning315 q) hs
  change valuationOf q 307 = false ∨ valuationOf q 315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause815 (q : Snake 81) (h : Conditions q) : valuation q 307 = false ∨ valuation q 315 = true := counterClause815 (baseVal q)

theorem counterClause816 (q : Nat → Bool) : valuationOf q 315 = false ∨ valuationOf q 317 = true := by
  have hs : count317 q = (countLit q [148, 149, 150, 151, 152, 153, 154]) + (countLit q [155, 156, 157, 158, 159, 160, 161]) := List.countP_append (p := literal q) (l₁ := [148, 149, 150, 151, 152, 153, 154]) (l₂ := [155, 156, 157, 158, 159, 160, 161])
  have hm := merge_right (literal (valuationOf q) (315)) (literal (valuationOf q) (317)) (countLit q [148, 149, 150, 151, 152, 153, 154]) (countLit q [155, 156, 157, 158, 159, 160, 161]) (count317 q) 1 (meaning315 q) (meaning317 q) hs
  change valuationOf q 315 = false ∨ valuationOf q 317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause816 (q : Snake 81) (h : Conditions q) : valuation q 315 = false ∨ valuation q 317 = true := counterClause816 (baseVal q)

theorem counterClause817 (q : Nat → Bool) : valuationOf q 316 = false ∨ valuationOf q 318 = true := by
  have hs : count317 q = (countLit q [148, 149, 150, 151, 152, 153, 154]) + (countLit q [155, 156, 157, 158, 159, 160, 161]) := List.countP_append (p := literal q) (l₁ := [148, 149, 150, 151, 152, 153, 154]) (l₂ := [155, 156, 157, 158, 159, 160, 161])
  have hm := merge_right (literal (valuationOf q) (316)) (literal (valuationOf q) (318)) (countLit q [148, 149, 150, 151, 152, 153, 154]) (countLit q [155, 156, 157, 158, 159, 160, 161]) (count317 q) 2 (meaning316 q) (meaning318 q) hs
  change valuationOf q 316 = false ∨ valuationOf q 318 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause817 (q : Snake 81) (h : Conditions q) : valuation q 316 = false ∨ valuation q 318 = true := counterClause817 (baseVal q)

theorem counterClause818 (q : Nat → Bool) : valuationOf q 303 = false ∨ valuationOf q 317 = true := by
  have hs : count317 q = (countLit q [148, 149, 150, 151, 152, 153, 154]) + (countLit q [155, 156, 157, 158, 159, 160, 161]) := List.countP_append (p := literal q) (l₁ := [148, 149, 150, 151, 152, 153, 154]) (l₂ := [155, 156, 157, 158, 159, 160, 161])
  have hm := merge_left (literal (valuationOf q) (303)) (literal (valuationOf q) (317)) (countLit q [148, 149, 150, 151, 152, 153, 154]) (countLit q [155, 156, 157, 158, 159, 160, 161]) (count317 q) 1 (meaning303 q) (meaning317 q) hs
  change valuationOf q 303 = false ∨ valuationOf q 317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause818 (q : Snake 81) (h : Conditions q) : valuation q 303 = false ∨ valuation q 317 = true := counterClause818 (baseVal q)

theorem counterClause819 (q : Nat → Bool) : valuationOf q 303 = false ∨ valuationOf q 315 = false ∨ valuationOf q 318 = true := by
  have hs : count317 q = (countLit q [148, 149, 150, 151, 152, 153, 154]) + (countLit q [155, 156, 157, 158, 159, 160, 161]) := List.countP_append (p := literal q) (l₁ := [148, 149, 150, 151, 152, 153, 154]) (l₂ := [155, 156, 157, 158, 159, 160, 161])
  have hm := merge_two (literal (valuationOf q) (303)) (literal (valuationOf q) (315)) (literal (valuationOf q) (318)) (countLit q [148, 149, 150, 151, 152, 153, 154]) (countLit q [155, 156, 157, 158, 159, 160, 161]) (count317 q) 1 1 (meaning303 q) (meaning315 q) (meaning318 q) hs
  change valuationOf q 303 = false ∨ valuationOf q 315 = false ∨ valuationOf q 318 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause819 (q : Snake 81) (h : Conditions q) : valuation q 303 = false ∨ valuation q 315 = false ∨ valuation q 318 = true := counterClause819 (baseVal q)

theorem counterClause820 (q : Nat → Bool) : valuationOf q 304 = false ∨ valuationOf q 318 = true := by
  have hs : count317 q = (countLit q [148, 149, 150, 151, 152, 153, 154]) + (countLit q [155, 156, 157, 158, 159, 160, 161]) := List.countP_append (p := literal q) (l₁ := [148, 149, 150, 151, 152, 153, 154]) (l₂ := [155, 156, 157, 158, 159, 160, 161])
  have hm := merge_left (literal (valuationOf q) (304)) (literal (valuationOf q) (318)) (countLit q [148, 149, 150, 151, 152, 153, 154]) (countLit q [155, 156, 157, 158, 159, 160, 161]) (count317 q) 2 (meaning304 q) (meaning318 q) hs
  change valuationOf q 304 = false ∨ valuationOf q 318 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause820 (q : Snake 81) (h : Conditions q) : valuation q 304 = false ∨ valuation q 318 = true := counterClause820 (baseVal q)

theorem counterClause821 (q : Nat → Bool) : valuationOf q 164 = false ∨ valuationOf q 319 = true := by
  have hs : count319 q = (countLit q [163]) + (countLit q [164]) := List.countP_append (p := literal q) (l₁ := [163]) (l₂ := [164])
  have hm := merge_right (literal (valuationOf q) (164)) (literal (valuationOf q) (319)) (countLit q [163]) (countLit q [164]) (count319 q) 1 (meaning164 q) (meaning319 q) hs
  change valuationOf q 164 = false ∨ valuationOf q 319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause821 (q : Snake 81) (h : Conditions q) : valuation q 164 = false ∨ valuation q 319 = true := counterClause821 (baseVal q)

theorem counterClause822 (q : Nat → Bool) : valuationOf q 319 = false ∨ valuationOf q 321 = true := by
  have hs : count321 q = (countLit q [162]) + (countLit q [163, 164]) := List.countP_append (p := literal q) (l₁ := [162]) (l₂ := [163, 164])
  have hm := merge_right (literal (valuationOf q) (319)) (literal (valuationOf q) (321)) (countLit q [162]) (countLit q [163, 164]) (count321 q) 1 (meaning319 q) (meaning321 q) hs
  change valuationOf q 319 = false ∨ valuationOf q 321 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause822 (q : Snake 81) (h : Conditions q) : valuation q 319 = false ∨ valuation q 321 = true := counterClause822 (baseVal q)

theorem counterClause823 (q : Nat → Bool) : valuationOf q 165 = false ∨ valuationOf q 323 = true := by
  have hs : count323 q = (countLit q [165]) + (countLit q [166]) := List.countP_append (p := literal q) (l₁ := [165]) (l₂ := [166])
  have hm := merge_left (literal (valuationOf q) (165)) (literal (valuationOf q) (323)) (countLit q [165]) (countLit q [166]) (count323 q) 1 (meaning165 q) (meaning323 q) hs
  change valuationOf q 165 = false ∨ valuationOf q 323 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause823 (q : Snake 81) (h : Conditions q) : valuation q 165 = false ∨ valuation q 323 = true := counterClause823 (baseVal q)

theorem counterClause824 (q : Nat → Bool) : valuationOf q 323 = false ∨ valuationOf q 327 = true := by
  have hs : count327 q = (countLit q [165, 166]) + (countLit q [167, 168]) := List.countP_append (p := literal q) (l₁ := [165, 166]) (l₂ := [167, 168])
  have hm := merge_left (literal (valuationOf q) (323)) (literal (valuationOf q) (327)) (countLit q [165, 166]) (countLit q [167, 168]) (count327 q) 1 (meaning323 q) (meaning327 q) hs
  change valuationOf q 323 = false ∨ valuationOf q 327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause824 (q : Snake 81) (h : Conditions q) : valuation q 323 = false ∨ valuation q 327 = true := counterClause824 (baseVal q)

theorem counterClause825 (q : Nat → Bool) : valuationOf q 327 = false ∨ valuationOf q 329 = true := by
  have hs : count329 q = (countLit q [162, 163, 164]) + (countLit q [165, 166, 167, 168]) := List.countP_append (p := literal q) (l₁ := [162, 163, 164]) (l₂ := [165, 166, 167, 168])
  have hm := merge_right (literal (valuationOf q) (327)) (literal (valuationOf q) (329)) (countLit q [162, 163, 164]) (countLit q [165, 166, 167, 168]) (count329 q) 1 (meaning327 q) (meaning329 q) hs
  change valuationOf q 327 = false ∨ valuationOf q 329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause825 (q : Snake 81) (h : Conditions q) : valuation q 327 = false ∨ valuation q 329 = true := counterClause825 (baseVal q)

theorem counterClause826 (q : Nat → Bool) : valuationOf q 321 = false ∨ valuationOf q 329 = true := by
  have hs : count329 q = (countLit q [162, 163, 164]) + (countLit q [165, 166, 167, 168]) := List.countP_append (p := literal q) (l₁ := [162, 163, 164]) (l₂ := [165, 166, 167, 168])
  have hm := merge_left (literal (valuationOf q) (321)) (literal (valuationOf q) (329)) (countLit q [162, 163, 164]) (countLit q [165, 166, 167, 168]) (count329 q) 1 (meaning321 q) (meaning329 q) hs
  change valuationOf q 321 = false ∨ valuationOf q 329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause826 (q : Snake 81) (h : Conditions q) : valuation q 321 = false ∨ valuation q 329 = true := counterClause826 (baseVal q)

theorem counterClause827 (q : Nat → Bool) : valuationOf q 170 = false ∨ valuationOf q 331 = true := by
  have hs : count331 q = (countLit q [169]) + (countLit q [170]) := List.countP_append (p := literal q) (l₁ := [169]) (l₂ := [170])
  have hm := merge_right (literal (valuationOf q) (170)) (literal (valuationOf q) (331)) (countLit q [169]) (countLit q [170]) (count331 q) 1 (meaning170 q) (meaning331 q) hs
  change valuationOf q 170 = false ∨ valuationOf q 331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause827 (q : Snake 81) (h : Conditions q) : valuation q 170 = false ∨ valuation q 331 = true := counterClause827 (baseVal q)

theorem counterClause828 (q : Nat → Bool) : valuationOf q 169 = false ∨ valuationOf q 331 = true := by
  have hs : count331 q = (countLit q [169]) + (countLit q [170]) := List.countP_append (p := literal q) (l₁ := [169]) (l₂ := [170])
  have hm := merge_left (literal (valuationOf q) (169)) (literal (valuationOf q) (331)) (countLit q [169]) (countLit q [170]) (count331 q) 1 (meaning169 q) (meaning331 q) hs
  change valuationOf q 169 = false ∨ valuationOf q 331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause828 (q : Snake 81) (h : Conditions q) : valuation q 169 = false ∨ valuation q 331 = true := counterClause828 (baseVal q)

theorem counterClause829 (q : Nat → Bool) : valuationOf q 169 = false ∨ valuationOf q 170 = false ∨ valuationOf q 332 = true := by
  have hs : count331 q = (countLit q [169]) + (countLit q [170]) := List.countP_append (p := literal q) (l₁ := [169]) (l₂ := [170])
  have hm := merge_two (literal (valuationOf q) (169)) (literal (valuationOf q) (170)) (literal (valuationOf q) (332)) (countLit q [169]) (countLit q [170]) (count331 q) 1 1 (meaning169 q) (meaning170 q) (meaning332 q) hs
  change valuationOf q 169 = false ∨ valuationOf q 170 = false ∨ valuationOf q 332 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause829 (q : Snake 81) (h : Conditions q) : valuation q 169 = false ∨ valuation q 170 = false ∨ valuation q 332 = true := counterClause829 (baseVal q)

theorem counterClause830 (q : Nat → Bool) : valuationOf q 172 = false ∨ valuationOf q 333 = true := by
  have hs : count333 q = (countLit q [171]) + (countLit q [172]) := List.countP_append (p := literal q) (l₁ := [171]) (l₂ := [172])
  have hm := merge_right (literal (valuationOf q) (172)) (literal (valuationOf q) (333)) (countLit q [171]) (countLit q [172]) (count333 q) 1 (meaning172 q) (meaning333 q) hs
  change valuationOf q 172 = false ∨ valuationOf q 333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause830 (q : Snake 81) (h : Conditions q) : valuation q 172 = false ∨ valuation q 333 = true := counterClause830 (baseVal q)

theorem counterClause831 (q : Nat → Bool) : valuationOf q 333 = false ∨ valuationOf q 335 = true := by
  have hs : count335 q = (countLit q [169, 170]) + (countLit q [171, 172]) := List.countP_append (p := literal q) (l₁ := [169, 170]) (l₂ := [171, 172])
  have hm := merge_right (literal (valuationOf q) (333)) (literal (valuationOf q) (335)) (countLit q [169, 170]) (countLit q [171, 172]) (count335 q) 1 (meaning333 q) (meaning335 q) hs
  change valuationOf q 333 = false ∨ valuationOf q 335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause831 (q : Snake 81) (h : Conditions q) : valuation q 333 = false ∨ valuation q 335 = true := counterClause831 (baseVal q)

theorem counterClause832 (q : Nat → Bool) : valuationOf q 331 = false ∨ valuationOf q 335 = true := by
  have hs : count335 q = (countLit q [169, 170]) + (countLit q [171, 172]) := List.countP_append (p := literal q) (l₁ := [169, 170]) (l₂ := [171, 172])
  have hm := merge_left (literal (valuationOf q) (331)) (literal (valuationOf q) (335)) (countLit q [169, 170]) (countLit q [171, 172]) (count335 q) 1 (meaning331 q) (meaning335 q) hs
  change valuationOf q 331 = false ∨ valuationOf q 335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause832 (q : Snake 81) (h : Conditions q) : valuation q 331 = false ∨ valuation q 335 = true := counterClause832 (baseVal q)

theorem block25 (q : Snake 81) (h : Conditions q) : B112E047.Block25 (valuation q) :=
  ⟨clause801 q h, clause802 q h, clause803 q h, clause804 q h, clause805 q h, clause806 q h, clause807 q h, clause808 q h, clause809 q h, clause810 q h, clause811 q h, clause812 q h, clause813 q h, clause814 q h, clause815 q h, clause816 q h, clause817 q h, clause818 q h, clause819 q h, clause820 q h, clause821 q h, clause822 q h, clause823 q h, clause824 q h, clause825 q h, clause826 q h, clause827 q h, clause828 q h, clause829 q h, clause830 q h, clause831 q h, clause832 q h⟩

end
end Snake9.Regrowth.E112047
