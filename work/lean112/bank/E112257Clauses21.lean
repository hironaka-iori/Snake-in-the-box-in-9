import E112257Semantics
import B112E257Inputs
namespace Snake9.Regrowth.E112257
noncomputable section
local instance blockDec21 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause673 (q : Nat → Bool) : valuationOf q 289 = false ∨ valuationOf q 295 = false ∨ valuationOf q 298 = true := by
  have hs : count297 q = (countLit q [145, 146, 147]) + (countLit q [148, 149, 150, 151]) := List.countP_append (p := literal q) (l₁ := [145, 146, 147]) (l₂ := [148, 149, 150, 151])
  have hm := merge_two (literal (valuationOf q) (289)) (literal (valuationOf q) (295)) (literal (valuationOf q) (298)) (countLit q [145, 146, 147]) (countLit q [148, 149, 150, 151]) (count297 q) 1 1 (meaning289 q) (meaning295 q) (meaning298 q) hs
  change valuationOf q 289 = false ∨ valuationOf q 295 = false ∨ valuationOf q 298 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause673 (q : Snake 81) (h : Conditions q) : valuation q 289 = false ∨ valuation q 295 = false ∨ valuation q 298 = true := counterClause673 (baseVal q)

theorem counterClause674 (q : Nat → Bool) : valuationOf q 154 = false ∨ valuationOf q 299 = true := by
  have hs : count299 q = (countLit q [153]) + (countLit q [154]) := List.countP_append (p := literal q) (l₁ := [153]) (l₂ := [154])
  have hm := merge_right (literal (valuationOf q) (154)) (literal (valuationOf q) (299)) (countLit q [153]) (countLit q [154]) (count299 q) 1 (meaning154 q) (meaning299 q) hs
  change valuationOf q 154 = false ∨ valuationOf q 299 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause674 (q : Snake 81) (h : Conditions q) : valuation q 154 = false ∨ valuation q 299 = true := counterClause674 (baseVal q)

theorem counterClause675 (q : Nat → Bool) : valuationOf q 153 = false ∨ valuationOf q 299 = true := by
  have hs : count299 q = (countLit q [153]) + (countLit q [154]) := List.countP_append (p := literal q) (l₁ := [153]) (l₂ := [154])
  have hm := merge_left (literal (valuationOf q) (153)) (literal (valuationOf q) (299)) (countLit q [153]) (countLit q [154]) (count299 q) 1 (meaning153 q) (meaning299 q) hs
  change valuationOf q 153 = false ∨ valuationOf q 299 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause675 (q : Snake 81) (h : Conditions q) : valuation q 153 = false ∨ valuation q 299 = true := counterClause675 (baseVal q)

theorem counterClause676 (q : Nat → Bool) : valuationOf q 299 = false ∨ valuationOf q 301 = true := by
  have hs : count301 q = (countLit q [152]) + (countLit q [153, 154]) := List.countP_append (p := literal q) (l₁ := [152]) (l₂ := [153, 154])
  have hm := merge_right (literal (valuationOf q) (299)) (literal (valuationOf q) (301)) (countLit q [152]) (countLit q [153, 154]) (count301 q) 1 (meaning299 q) (meaning301 q) hs
  change valuationOf q 299 = false ∨ valuationOf q 301 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause676 (q : Snake 81) (h : Conditions q) : valuation q 299 = false ∨ valuation q 301 = true := counterClause676 (baseVal q)

theorem counterClause677 (q : Nat → Bool) : valuationOf q 152 = false ∨ valuationOf q 301 = true := by
  have hs : count301 q = (countLit q [152]) + (countLit q [153, 154]) := List.countP_append (p := literal q) (l₁ := [152]) (l₂ := [153, 154])
  have hm := merge_left (literal (valuationOf q) (152)) (literal (valuationOf q) (301)) (countLit q [152]) (countLit q [153, 154]) (count301 q) 1 (meaning152 q) (meaning301 q) hs
  change valuationOf q 152 = false ∨ valuationOf q 301 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause677 (q : Snake 81) (h : Conditions q) : valuation q 152 = false ∨ valuation q 301 = true := counterClause677 (baseVal q)

theorem counterClause678 (q : Nat → Bool) : valuationOf q 152 = false ∨ valuationOf q 299 = false ∨ valuationOf q 302 = true := by
  have hs : count301 q = (countLit q [152]) + (countLit q [153, 154]) := List.countP_append (p := literal q) (l₁ := [152]) (l₂ := [153, 154])
  have hm := merge_two (literal (valuationOf q) (152)) (literal (valuationOf q) (299)) (literal (valuationOf q) (302)) (countLit q [152]) (countLit q [153, 154]) (count301 q) 1 1 (meaning152 q) (meaning299 q) (meaning302 q) hs
  change valuationOf q 152 = false ∨ valuationOf q 299 = false ∨ valuationOf q 302 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause678 (q : Snake 81) (h : Conditions q) : valuation q 152 = false ∨ valuation q 299 = false ∨ valuation q 302 = true := counterClause678 (baseVal q)

theorem counterClause679 (q : Nat → Bool) : valuationOf q 157 = false ∨ valuationOf q 305 = true := by
  have hs : count305 q = (countLit q [157]) + (countLit q [158]) := List.countP_append (p := literal q) (l₁ := [157]) (l₂ := [158])
  have hm := merge_left (literal (valuationOf q) (157)) (literal (valuationOf q) (305)) (countLit q [157]) (countLit q [158]) (count305 q) 1 (meaning157 q) (meaning305 q) hs
  change valuationOf q 157 = false ∨ valuationOf q 305 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause679 (q : Snake 81) (h : Conditions q) : valuation q 157 = false ∨ valuation q 305 = true := counterClause679 (baseVal q)

theorem counterClause680 (q : Nat → Bool) : valuationOf q 305 = false ∨ valuationOf q 307 = true := by
  have hs : count307 q = (countLit q [155, 156]) + (countLit q [157, 158]) := List.countP_append (p := literal q) (l₁ := [155, 156]) (l₂ := [157, 158])
  have hm := merge_right (literal (valuationOf q) (305)) (literal (valuationOf q) (307)) (countLit q [155, 156]) (countLit q [157, 158]) (count307 q) 1 (meaning305 q) (meaning307 q) hs
  change valuationOf q 305 = false ∨ valuationOf q 307 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause680 (q : Snake 81) (h : Conditions q) : valuation q 305 = false ∨ valuation q 307 = true := counterClause680 (baseVal q)

theorem counterClause681 (q : Nat → Bool) : valuationOf q 307 = false ∨ valuationOf q 309 = true := by
  have hs : count309 q = (countLit q [152, 153, 154]) + (countLit q [155, 156, 157, 158]) := List.countP_append (p := literal q) (l₁ := [152, 153, 154]) (l₂ := [155, 156, 157, 158])
  have hm := merge_right (literal (valuationOf q) (307)) (literal (valuationOf q) (309)) (countLit q [152, 153, 154]) (countLit q [155, 156, 157, 158]) (count309 q) 1 (meaning307 q) (meaning309 q) hs
  change valuationOf q 307 = false ∨ valuationOf q 309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause681 (q : Snake 81) (h : Conditions q) : valuation q 307 = false ∨ valuation q 309 = true := counterClause681 (baseVal q)

theorem counterClause682 (q : Nat → Bool) : valuationOf q 301 = false ∨ valuationOf q 309 = true := by
  have hs : count309 q = (countLit q [152, 153, 154]) + (countLit q [155, 156, 157, 158]) := List.countP_append (p := literal q) (l₁ := [152, 153, 154]) (l₂ := [155, 156, 157, 158])
  have hm := merge_left (literal (valuationOf q) (301)) (literal (valuationOf q) (309)) (countLit q [152, 153, 154]) (countLit q [155, 156, 157, 158]) (count309 q) 1 (meaning301 q) (meaning309 q) hs
  change valuationOf q 301 = false ∨ valuationOf q 309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause682 (q : Snake 81) (h : Conditions q) : valuation q 301 = false ∨ valuation q 309 = true := counterClause682 (baseVal q)

theorem counterClause683 (q : Nat → Bool) : valuationOf q 301 = false ∨ valuationOf q 307 = false ∨ valuationOf q 310 = true := by
  have hs : count309 q = (countLit q [152, 153, 154]) + (countLit q [155, 156, 157, 158]) := List.countP_append (p := literal q) (l₁ := [152, 153, 154]) (l₂ := [155, 156, 157, 158])
  have hm := merge_two (literal (valuationOf q) (301)) (literal (valuationOf q) (307)) (literal (valuationOf q) (310)) (countLit q [152, 153, 154]) (countLit q [155, 156, 157, 158]) (count309 q) 1 1 (meaning301 q) (meaning307 q) (meaning310 q) hs
  change valuationOf q 301 = false ∨ valuationOf q 307 = false ∨ valuationOf q 310 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause683 (q : Snake 81) (h : Conditions q) : valuation q 301 = false ∨ valuation q 307 = false ∨ valuation q 310 = true := counterClause683 (baseVal q)

theorem counterClause684 (q : Nat → Bool) : valuationOf q 302 = false ∨ valuationOf q 310 = true := by
  have hs : count309 q = (countLit q [152, 153, 154]) + (countLit q [155, 156, 157, 158]) := List.countP_append (p := literal q) (l₁ := [152, 153, 154]) (l₂ := [155, 156, 157, 158])
  have hm := merge_left (literal (valuationOf q) (302)) (literal (valuationOf q) (310)) (countLit q [152, 153, 154]) (countLit q [155, 156, 157, 158]) (count309 q) 2 (meaning302 q) (meaning310 q) hs
  change valuationOf q 302 = false ∨ valuationOf q 310 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause684 (q : Snake 81) (h : Conditions q) : valuation q 302 = false ∨ valuation q 310 = true := counterClause684 (baseVal q)

theorem counterClause685 (q : Nat → Bool) : valuationOf q 309 = false ∨ valuationOf q 311 = true := by
  have hs : count311 q = (countLit q [145, 146, 147, 148, 149, 150, 151]) + (countLit q [152, 153, 154, 155, 156, 157, 158]) := List.countP_append (p := literal q) (l₁ := [145, 146, 147, 148, 149, 150, 151]) (l₂ := [152, 153, 154, 155, 156, 157, 158])
  have hm := merge_right (literal (valuationOf q) (309)) (literal (valuationOf q) (311)) (countLit q [145, 146, 147, 148, 149, 150, 151]) (countLit q [152, 153, 154, 155, 156, 157, 158]) (count311 q) 1 (meaning309 q) (meaning311 q) hs
  change valuationOf q 309 = false ∨ valuationOf q 311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause685 (q : Snake 81) (h : Conditions q) : valuation q 309 = false ∨ valuation q 311 = true := counterClause685 (baseVal q)

theorem counterClause686 (q : Nat → Bool) : valuationOf q 310 = false ∨ valuationOf q 312 = true := by
  have hs : count311 q = (countLit q [145, 146, 147, 148, 149, 150, 151]) + (countLit q [152, 153, 154, 155, 156, 157, 158]) := List.countP_append (p := literal q) (l₁ := [145, 146, 147, 148, 149, 150, 151]) (l₂ := [152, 153, 154, 155, 156, 157, 158])
  have hm := merge_right (literal (valuationOf q) (310)) (literal (valuationOf q) (312)) (countLit q [145, 146, 147, 148, 149, 150, 151]) (countLit q [152, 153, 154, 155, 156, 157, 158]) (count311 q) 2 (meaning310 q) (meaning312 q) hs
  change valuationOf q 310 = false ∨ valuationOf q 312 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause686 (q : Snake 81) (h : Conditions q) : valuation q 310 = false ∨ valuation q 312 = true := counterClause686 (baseVal q)

theorem counterClause687 (q : Nat → Bool) : valuationOf q 297 = false ∨ valuationOf q 311 = true := by
  have hs : count311 q = (countLit q [145, 146, 147, 148, 149, 150, 151]) + (countLit q [152, 153, 154, 155, 156, 157, 158]) := List.countP_append (p := literal q) (l₁ := [145, 146, 147, 148, 149, 150, 151]) (l₂ := [152, 153, 154, 155, 156, 157, 158])
  have hm := merge_left (literal (valuationOf q) (297)) (literal (valuationOf q) (311)) (countLit q [145, 146, 147, 148, 149, 150, 151]) (countLit q [152, 153, 154, 155, 156, 157, 158]) (count311 q) 1 (meaning297 q) (meaning311 q) hs
  change valuationOf q 297 = false ∨ valuationOf q 311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause687 (q : Snake 81) (h : Conditions q) : valuation q 297 = false ∨ valuation q 311 = true := counterClause687 (baseVal q)

theorem counterClause688 (q : Nat → Bool) : valuationOf q 297 = false ∨ valuationOf q 309 = false ∨ valuationOf q 312 = true := by
  have hs : count311 q = (countLit q [145, 146, 147, 148, 149, 150, 151]) + (countLit q [152, 153, 154, 155, 156, 157, 158]) := List.countP_append (p := literal q) (l₁ := [145, 146, 147, 148, 149, 150, 151]) (l₂ := [152, 153, 154, 155, 156, 157, 158])
  have hm := merge_two (literal (valuationOf q) (297)) (literal (valuationOf q) (309)) (literal (valuationOf q) (312)) (countLit q [145, 146, 147, 148, 149, 150, 151]) (countLit q [152, 153, 154, 155, 156, 157, 158]) (count311 q) 1 1 (meaning297 q) (meaning309 q) (meaning312 q) hs
  change valuationOf q 297 = false ∨ valuationOf q 309 = false ∨ valuationOf q 312 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause688 (q : Snake 81) (h : Conditions q) : valuation q 297 = false ∨ valuation q 309 = false ∨ valuation q 312 = true := counterClause688 (baseVal q)

theorem counterClause689 (q : Nat → Bool) : valuationOf q 298 = false ∨ valuationOf q 312 = true := by
  have hs : count311 q = (countLit q [145, 146, 147, 148, 149, 150, 151]) + (countLit q [152, 153, 154, 155, 156, 157, 158]) := List.countP_append (p := literal q) (l₁ := [145, 146, 147, 148, 149, 150, 151]) (l₂ := [152, 153, 154, 155, 156, 157, 158])
  have hm := merge_left (literal (valuationOf q) (298)) (literal (valuationOf q) (312)) (countLit q [145, 146, 147, 148, 149, 150, 151]) (countLit q [152, 153, 154, 155, 156, 157, 158]) (count311 q) 2 (meaning298 q) (meaning312 q) hs
  change valuationOf q 298 = false ∨ valuationOf q 312 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause689 (q : Snake 81) (h : Conditions q) : valuation q 298 = false ∨ valuation q 312 = true := counterClause689 (baseVal q)

theorem counterClause690 (q : Nat → Bool) : valuationOf q 159 = false ∨ valuationOf q 315 = true := by
  have hs : count315 q = (countLit q [159]) + (countLit q [160, 161]) := List.countP_append (p := literal q) (l₁ := [159]) (l₂ := [160, 161])
  have hm := merge_left (literal (valuationOf q) (159)) (literal (valuationOf q) (315)) (countLit q [159]) (countLit q [160, 161]) (count315 q) 1 (meaning159 q) (meaning315 q) hs
  change valuationOf q 159 = false ∨ valuationOf q 315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause690 (q : Snake 81) (h : Conditions q) : valuation q 159 = false ∨ valuation q 315 = true := counterClause690 (baseVal q)

theorem counterClause691 (q : Nat → Bool) : valuationOf q 163 = false ∨ valuationOf q 317 = true := by
  have hs : count317 q = (countLit q [162]) + (countLit q [163]) := List.countP_append (p := literal q) (l₁ := [162]) (l₂ := [163])
  have hm := merge_right (literal (valuationOf q) (163)) (literal (valuationOf q) (317)) (countLit q [162]) (countLit q [163]) (count317 q) 1 (meaning163 q) (meaning317 q) hs
  change valuationOf q 163 = false ∨ valuationOf q 317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause691 (q : Snake 81) (h : Conditions q) : valuation q 163 = false ∨ valuation q 317 = true := counterClause691 (baseVal q)

theorem counterClause692 (q : Nat → Bool) : valuationOf q 317 = false ∨ valuationOf q 321 = true := by
  have hs : count321 q = (countLit q [162, 163]) + (countLit q [164, 165]) := List.countP_append (p := literal q) (l₁ := [162, 163]) (l₂ := [164, 165])
  have hm := merge_left (literal (valuationOf q) (317)) (literal (valuationOf q) (321)) (countLit q [162, 163]) (countLit q [164, 165]) (count321 q) 1 (meaning317 q) (meaning321 q) hs
  change valuationOf q 317 = false ∨ valuationOf q 321 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause692 (q : Snake 81) (h : Conditions q) : valuation q 317 = false ∨ valuation q 321 = true := counterClause692 (baseVal q)

theorem counterClause693 (q : Nat → Bool) : valuationOf q 321 = false ∨ valuationOf q 323 = true := by
  have hs : count323 q = (countLit q [159, 160, 161]) + (countLit q [162, 163, 164, 165]) := List.countP_append (p := literal q) (l₁ := [159, 160, 161]) (l₂ := [162, 163, 164, 165])
  have hm := merge_right (literal (valuationOf q) (321)) (literal (valuationOf q) (323)) (countLit q [159, 160, 161]) (countLit q [162, 163, 164, 165]) (count323 q) 1 (meaning321 q) (meaning323 q) hs
  change valuationOf q 321 = false ∨ valuationOf q 323 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause693 (q : Snake 81) (h : Conditions q) : valuation q 321 = false ∨ valuation q 323 = true := counterClause693 (baseVal q)

theorem counterClause694 (q : Nat → Bool) : valuationOf q 315 = false ∨ valuationOf q 323 = true := by
  have hs : count323 q = (countLit q [159, 160, 161]) + (countLit q [162, 163, 164, 165]) := List.countP_append (p := literal q) (l₁ := [159, 160, 161]) (l₂ := [162, 163, 164, 165])
  have hm := merge_left (literal (valuationOf q) (315)) (literal (valuationOf q) (323)) (countLit q [159, 160, 161]) (countLit q [162, 163, 164, 165]) (count323 q) 1 (meaning315 q) (meaning323 q) hs
  change valuationOf q 315 = false ∨ valuationOf q 323 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause694 (q : Snake 81) (h : Conditions q) : valuation q 315 = false ∨ valuation q 323 = true := counterClause694 (baseVal q)

theorem counterClause695 (q : Nat → Bool) : valuationOf q 167 = false ∨ valuationOf q 325 = true := by
  have hs : count325 q = (countLit q [166]) + (countLit q [167]) := List.countP_append (p := literal q) (l₁ := [166]) (l₂ := [167])
  have hm := merge_right (literal (valuationOf q) (167)) (literal (valuationOf q) (325)) (countLit q [166]) (countLit q [167]) (count325 q) 1 (meaning167 q) (meaning325 q) hs
  change valuationOf q 167 = false ∨ valuationOf q 325 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause695 (q : Snake 81) (h : Conditions q) : valuation q 167 = false ∨ valuation q 325 = true := counterClause695 (baseVal q)

theorem counterClause696 (q : Nat → Bool) : valuationOf q 169 = false ∨ valuationOf q 327 = true := by
  have hs : count327 q = (countLit q [168]) + (countLit q [169]) := List.countP_append (p := literal q) (l₁ := [168]) (l₂ := [169])
  have hm := merge_right (literal (valuationOf q) (169)) (literal (valuationOf q) (327)) (countLit q [168]) (countLit q [169]) (count327 q) 1 (meaning169 q) (meaning327 q) hs
  change valuationOf q 169 = false ∨ valuationOf q 327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause696 (q : Snake 81) (h : Conditions q) : valuation q 169 = false ∨ valuation q 327 = true := counterClause696 (baseVal q)

theorem counterClause697 (q : Nat → Bool) : valuationOf q 327 = false ∨ valuationOf q 329 = true := by
  have hs : count329 q = (countLit q [166, 167]) + (countLit q [168, 169]) := List.countP_append (p := literal q) (l₁ := [166, 167]) (l₂ := [168, 169])
  have hm := merge_right (literal (valuationOf q) (327)) (literal (valuationOf q) (329)) (countLit q [166, 167]) (countLit q [168, 169]) (count329 q) 1 (meaning327 q) (meaning329 q) hs
  change valuationOf q 327 = false ∨ valuationOf q 329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause697 (q : Snake 81) (h : Conditions q) : valuation q 327 = false ∨ valuation q 329 = true := counterClause697 (baseVal q)

theorem counterClause698 (q : Nat → Bool) : valuationOf q 325 = false ∨ valuationOf q 329 = true := by
  have hs : count329 q = (countLit q [166, 167]) + (countLit q [168, 169]) := List.countP_append (p := literal q) (l₁ := [166, 167]) (l₂ := [168, 169])
  have hm := merge_left (literal (valuationOf q) (325)) (literal (valuationOf q) (329)) (countLit q [166, 167]) (countLit q [168, 169]) (count329 q) 1 (meaning325 q) (meaning329 q) hs
  change valuationOf q 325 = false ∨ valuationOf q 329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause698 (q : Snake 81) (h : Conditions q) : valuation q 325 = false ∨ valuation q 329 = true := counterClause698 (baseVal q)

theorem counterClause699 (q : Nat → Bool) : valuationOf q 171 = false ∨ valuationOf q 331 = true := by
  have hs : count331 q = (countLit q [170]) + (countLit q [171]) := List.countP_append (p := literal q) (l₁ := [170]) (l₂ := [171])
  have hm := merge_right (literal (valuationOf q) (171)) (literal (valuationOf q) (331)) (countLit q [170]) (countLit q [171]) (count331 q) 1 (meaning171 q) (meaning331 q) hs
  change valuationOf q 171 = false ∨ valuationOf q 331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause699 (q : Snake 81) (h : Conditions q) : valuation q 171 = false ∨ valuation q 331 = true := counterClause699 (baseVal q)

theorem counterClause700 (q : Nat → Bool) : valuationOf q 173 = false ∨ valuationOf q 333 = true := by
  have hs : count333 q = (countLit q [172]) + (countLit q [173]) := List.countP_append (p := literal q) (l₁ := [172]) (l₂ := [173])
  have hm := merge_right (literal (valuationOf q) (173)) (literal (valuationOf q) (333)) (countLit q [172]) (countLit q [173]) (count333 q) 1 (meaning173 q) (meaning333 q) hs
  change valuationOf q 173 = false ∨ valuationOf q 333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause700 (q : Snake 81) (h : Conditions q) : valuation q 173 = false ∨ valuation q 333 = true := counterClause700 (baseVal q)

theorem counterClause701 (q : Nat → Bool) : valuationOf q 172 = false ∨ valuationOf q 333 = true := by
  have hs : count333 q = (countLit q [172]) + (countLit q [173]) := List.countP_append (p := literal q) (l₁ := [172]) (l₂ := [173])
  have hm := merge_left (literal (valuationOf q) (172)) (literal (valuationOf q) (333)) (countLit q [172]) (countLit q [173]) (count333 q) 1 (meaning172 q) (meaning333 q) hs
  change valuationOf q 172 = false ∨ valuationOf q 333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause701 (q : Snake 81) (h : Conditions q) : valuation q 172 = false ∨ valuation q 333 = true := counterClause701 (baseVal q)

theorem counterClause702 (q : Nat → Bool) : valuationOf q 333 = false ∨ valuationOf q 335 = true := by
  have hs : count335 q = (countLit q [170, 171]) + (countLit q [172, 173]) := List.countP_append (p := literal q) (l₁ := [170, 171]) (l₂ := [172, 173])
  have hm := merge_right (literal (valuationOf q) (333)) (literal (valuationOf q) (335)) (countLit q [170, 171]) (countLit q [172, 173]) (count335 q) 1 (meaning333 q) (meaning335 q) hs
  change valuationOf q 333 = false ∨ valuationOf q 335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause702 (q : Snake 81) (h : Conditions q) : valuation q 333 = false ∨ valuation q 335 = true := counterClause702 (baseVal q)

theorem counterClause703 (q : Nat → Bool) : valuationOf q 331 = false ∨ valuationOf q 335 = true := by
  have hs : count335 q = (countLit q [170, 171]) + (countLit q [172, 173]) := List.countP_append (p := literal q) (l₁ := [170, 171]) (l₂ := [172, 173])
  have hm := merge_left (literal (valuationOf q) (331)) (literal (valuationOf q) (335)) (countLit q [170, 171]) (countLit q [172, 173]) (count335 q) 1 (meaning331 q) (meaning335 q) hs
  change valuationOf q 331 = false ∨ valuationOf q 335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause703 (q : Snake 81) (h : Conditions q) : valuation q 331 = false ∨ valuation q 335 = true := counterClause703 (baseVal q)

theorem counterClause704 (q : Nat → Bool) : valuationOf q 335 = false ∨ valuationOf q 337 = true := by
  have hs : count337 q = (countLit q [166, 167, 168, 169]) + (countLit q [170, 171, 172, 173]) := List.countP_append (p := literal q) (l₁ := [166, 167, 168, 169]) (l₂ := [170, 171, 172, 173])
  have hm := merge_right (literal (valuationOf q) (335)) (literal (valuationOf q) (337)) (countLit q [166, 167, 168, 169]) (countLit q [170, 171, 172, 173]) (count337 q) 1 (meaning335 q) (meaning337 q) hs
  change valuationOf q 335 = false ∨ valuationOf q 337 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause704 (q : Snake 81) (h : Conditions q) : valuation q 335 = false ∨ valuation q 337 = true := counterClause704 (baseVal q)

theorem block21 (q : Snake 81) (h : Conditions q) : B112E257.Block21 (valuation q) :=
  ⟨clause673 q h, clause674 q h, clause675 q h, clause676 q h, clause677 q h, clause678 q h, clause679 q h, clause680 q h, clause681 q h, clause682 q h, clause683 q h, clause684 q h, clause685 q h, clause686 q h, clause687 q h, clause688 q h, clause689 q h, clause690 q h, clause691 q h, clause692 q h, clause693 q h, clause694 q h, clause695 q h, clause696 q h, clause697 q h, clause698 q h, clause699 q h, clause700 q h, clause701 q h, clause702 q h, clause703 q h, clause704 q h⟩

end
end Snake9.Regrowth.E112257
