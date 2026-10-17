import E112207Semantics
import B112E207Inputs
namespace Snake9.Regrowth.E112207
noncomputable section
local instance blockDec23 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause737 (q : Nat → Bool) : valuationOf q 304 = false ∨ valuationOf q 306 = true := by
  have hs : count305 q = (countLit q [154]) + (countLit q [155, 156]) := List.countP_append (p := literal q) (l₁ := [154]) (l₂ := [155, 156])
  have hm := merge_right (literal (valuationOf q) (304)) (literal (valuationOf q) (306)) (countLit q [154]) (countLit q [155, 156]) (count305 q) 2 (meaning304 q) (meaning306 q) hs
  change valuationOf q 304 = false ∨ valuationOf q 306 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause737 (q : Snake 81) (h : Conditions q) : valuation q 304 = false ∨ valuation q 306 = true := counterClause737 (baseVal q)

theorem counterClause738 (q : Nat → Bool) : valuationOf q 154 = false ∨ valuationOf q 305 = true := by
  have hs : count305 q = (countLit q [154]) + (countLit q [155, 156]) := List.countP_append (p := literal q) (l₁ := [154]) (l₂ := [155, 156])
  have hm := merge_left (literal (valuationOf q) (154)) (literal (valuationOf q) (305)) (countLit q [154]) (countLit q [155, 156]) (count305 q) 1 (meaning154 q) (meaning305 q) hs
  change valuationOf q 154 = false ∨ valuationOf q 305 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause738 (q : Snake 81) (h : Conditions q) : valuation q 154 = false ∨ valuation q 305 = true := counterClause738 (baseVal q)

theorem counterClause739 (q : Nat → Bool) : valuationOf q 160 = false ∨ valuationOf q 309 = true := by
  have hs : count309 q = (countLit q [159]) + (countLit q [160]) := List.countP_append (p := literal q) (l₁ := [159]) (l₂ := [160])
  have hm := merge_right (literal (valuationOf q) (160)) (literal (valuationOf q) (309)) (countLit q [159]) (countLit q [160]) (count309 q) 1 (meaning160 q) (meaning309 q) hs
  change valuationOf q 160 = false ∨ valuationOf q 309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause739 (q : Snake 81) (h : Conditions q) : valuation q 160 = false ∨ valuation q 309 = true := counterClause739 (baseVal q)

theorem counterClause740 (q : Nat → Bool) : valuationOf q 309 = false ∨ valuationOf q 311 = true := by
  have hs : count311 q = (countLit q [157, 158]) + (countLit q [159, 160]) := List.countP_append (p := literal q) (l₁ := [157, 158]) (l₂ := [159, 160])
  have hm := merge_right (literal (valuationOf q) (309)) (literal (valuationOf q) (311)) (countLit q [157, 158]) (countLit q [159, 160]) (count311 q) 1 (meaning309 q) (meaning311 q) hs
  change valuationOf q 309 = false ∨ valuationOf q 311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause740 (q : Snake 81) (h : Conditions q) : valuation q 309 = false ∨ valuation q 311 = true := counterClause740 (baseVal q)

theorem counterClause741 (q : Nat → Bool) : valuationOf q 311 = false ∨ valuationOf q 313 = true := by
  have hs : count313 q = (countLit q [154, 155, 156]) + (countLit q [157, 158, 159, 160]) := List.countP_append (p := literal q) (l₁ := [154, 155, 156]) (l₂ := [157, 158, 159, 160])
  have hm := merge_right (literal (valuationOf q) (311)) (literal (valuationOf q) (313)) (countLit q [154, 155, 156]) (countLit q [157, 158, 159, 160]) (count313 q) 1 (meaning311 q) (meaning313 q) hs
  change valuationOf q 311 = false ∨ valuationOf q 313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause741 (q : Snake 81) (h : Conditions q) : valuation q 311 = false ∨ valuation q 313 = true := counterClause741 (baseVal q)

theorem counterClause742 (q : Nat → Bool) : valuationOf q 305 = false ∨ valuationOf q 313 = true := by
  have hs : count313 q = (countLit q [154, 155, 156]) + (countLit q [157, 158, 159, 160]) := List.countP_append (p := literal q) (l₁ := [154, 155, 156]) (l₂ := [157, 158, 159, 160])
  have hm := merge_left (literal (valuationOf q) (305)) (literal (valuationOf q) (313)) (countLit q [154, 155, 156]) (countLit q [157, 158, 159, 160]) (count313 q) 1 (meaning305 q) (meaning313 q) hs
  change valuationOf q 305 = false ∨ valuationOf q 313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause742 (q : Snake 81) (h : Conditions q) : valuation q 305 = false ∨ valuation q 313 = true := counterClause742 (baseVal q)

theorem counterClause743 (q : Nat → Bool) : valuationOf q 305 = false ∨ valuationOf q 311 = false ∨ valuationOf q 314 = true := by
  have hs : count313 q = (countLit q [154, 155, 156]) + (countLit q [157, 158, 159, 160]) := List.countP_append (p := literal q) (l₁ := [154, 155, 156]) (l₂ := [157, 158, 159, 160])
  have hm := merge_two (literal (valuationOf q) (305)) (literal (valuationOf q) (311)) (literal (valuationOf q) (314)) (countLit q [154, 155, 156]) (countLit q [157, 158, 159, 160]) (count313 q) 1 1 (meaning305 q) (meaning311 q) (meaning314 q) hs
  change valuationOf q 305 = false ∨ valuationOf q 311 = false ∨ valuationOf q 314 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause743 (q : Snake 81) (h : Conditions q) : valuation q 305 = false ∨ valuation q 311 = false ∨ valuation q 314 = true := counterClause743 (baseVal q)

theorem counterClause744 (q : Nat → Bool) : valuationOf q 306 = false ∨ valuationOf q 314 = true := by
  have hs : count313 q = (countLit q [154, 155, 156]) + (countLit q [157, 158, 159, 160]) := List.countP_append (p := literal q) (l₁ := [154, 155, 156]) (l₂ := [157, 158, 159, 160])
  have hm := merge_left (literal (valuationOf q) (306)) (literal (valuationOf q) (314)) (countLit q [154, 155, 156]) (countLit q [157, 158, 159, 160]) (count313 q) 2 (meaning306 q) (meaning314 q) hs
  change valuationOf q 306 = false ∨ valuationOf q 314 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause744 (q : Snake 81) (h : Conditions q) : valuation q 306 = false ∨ valuation q 314 = true := counterClause744 (baseVal q)

theorem counterClause745 (q : Nat → Bool) : valuationOf q 313 = false ∨ valuationOf q 315 = true := by
  have hs : count315 q = (countLit q [147, 148, 149, 150, 151, 152, 153]) + (countLit q [154, 155, 156, 157, 158, 159, 160]) := List.countP_append (p := literal q) (l₁ := [147, 148, 149, 150, 151, 152, 153]) (l₂ := [154, 155, 156, 157, 158, 159, 160])
  have hm := merge_right (literal (valuationOf q) (313)) (literal (valuationOf q) (315)) (countLit q [147, 148, 149, 150, 151, 152, 153]) (countLit q [154, 155, 156, 157, 158, 159, 160]) (count315 q) 1 (meaning313 q) (meaning315 q) hs
  change valuationOf q 313 = false ∨ valuationOf q 315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause745 (q : Snake 81) (h : Conditions q) : valuation q 313 = false ∨ valuation q 315 = true := counterClause745 (baseVal q)

theorem counterClause746 (q : Nat → Bool) : valuationOf q 314 = false ∨ valuationOf q 316 = true := by
  have hs : count315 q = (countLit q [147, 148, 149, 150, 151, 152, 153]) + (countLit q [154, 155, 156, 157, 158, 159, 160]) := List.countP_append (p := literal q) (l₁ := [147, 148, 149, 150, 151, 152, 153]) (l₂ := [154, 155, 156, 157, 158, 159, 160])
  have hm := merge_right (literal (valuationOf q) (314)) (literal (valuationOf q) (316)) (countLit q [147, 148, 149, 150, 151, 152, 153]) (countLit q [154, 155, 156, 157, 158, 159, 160]) (count315 q) 2 (meaning314 q) (meaning316 q) hs
  change valuationOf q 314 = false ∨ valuationOf q 316 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause746 (q : Snake 81) (h : Conditions q) : valuation q 314 = false ∨ valuation q 316 = true := counterClause746 (baseVal q)

theorem counterClause747 (q : Nat → Bool) : valuationOf q 301 = false ∨ valuationOf q 315 = true := by
  have hs : count315 q = (countLit q [147, 148, 149, 150, 151, 152, 153]) + (countLit q [154, 155, 156, 157, 158, 159, 160]) := List.countP_append (p := literal q) (l₁ := [147, 148, 149, 150, 151, 152, 153]) (l₂ := [154, 155, 156, 157, 158, 159, 160])
  have hm := merge_left (literal (valuationOf q) (301)) (literal (valuationOf q) (315)) (countLit q [147, 148, 149, 150, 151, 152, 153]) (countLit q [154, 155, 156, 157, 158, 159, 160]) (count315 q) 1 (meaning301 q) (meaning315 q) hs
  change valuationOf q 301 = false ∨ valuationOf q 315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause747 (q : Snake 81) (h : Conditions q) : valuation q 301 = false ∨ valuation q 315 = true := counterClause747 (baseVal q)

theorem counterClause748 (q : Nat → Bool) : valuationOf q 301 = false ∨ valuationOf q 313 = false ∨ valuationOf q 316 = true := by
  have hs : count315 q = (countLit q [147, 148, 149, 150, 151, 152, 153]) + (countLit q [154, 155, 156, 157, 158, 159, 160]) := List.countP_append (p := literal q) (l₁ := [147, 148, 149, 150, 151, 152, 153]) (l₂ := [154, 155, 156, 157, 158, 159, 160])
  have hm := merge_two (literal (valuationOf q) (301)) (literal (valuationOf q) (313)) (literal (valuationOf q) (316)) (countLit q [147, 148, 149, 150, 151, 152, 153]) (countLit q [154, 155, 156, 157, 158, 159, 160]) (count315 q) 1 1 (meaning301 q) (meaning313 q) (meaning316 q) hs
  change valuationOf q 301 = false ∨ valuationOf q 313 = false ∨ valuationOf q 316 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause748 (q : Snake 81) (h : Conditions q) : valuation q 301 = false ∨ valuation q 313 = false ∨ valuation q 316 = true := counterClause748 (baseVal q)

theorem counterClause749 (q : Nat → Bool) : valuationOf q 302 = false ∨ valuationOf q 316 = true := by
  have hs : count315 q = (countLit q [147, 148, 149, 150, 151, 152, 153]) + (countLit q [154, 155, 156, 157, 158, 159, 160]) := List.countP_append (p := literal q) (l₁ := [147, 148, 149, 150, 151, 152, 153]) (l₂ := [154, 155, 156, 157, 158, 159, 160])
  have hm := merge_left (literal (valuationOf q) (302)) (literal (valuationOf q) (316)) (countLit q [147, 148, 149, 150, 151, 152, 153]) (countLit q [154, 155, 156, 157, 158, 159, 160]) (count315 q) 2 (meaning302 q) (meaning316 q) hs
  change valuationOf q 302 = false ∨ valuationOf q 316 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause749 (q : Snake 81) (h : Conditions q) : valuation q 302 = false ∨ valuation q 316 = true := counterClause749 (baseVal q)

theorem counterClause750 (q : Nat → Bool) : valuationOf q 162 = false ∨ valuationOf q 317 = true := by
  have hs : count317 q = (countLit q [162]) + (countLit q [163]) := List.countP_append (p := literal q) (l₁ := [162]) (l₂ := [163])
  have hm := merge_left (literal (valuationOf q) (162)) (literal (valuationOf q) (317)) (countLit q [162]) (countLit q [163]) (count317 q) 1 (meaning162 q) (meaning317 q) hs
  change valuationOf q 162 = false ∨ valuationOf q 317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause750 (q : Snake 81) (h : Conditions q) : valuation q 162 = false ∨ valuation q 317 = true := counterClause750 (baseVal q)

theorem counterClause751 (q : Nat → Bool) : valuationOf q 317 = false ∨ valuationOf q 319 = true := by
  have hs : count319 q = (countLit q [161]) + (countLit q [162, 163]) := List.countP_append (p := literal q) (l₁ := [161]) (l₂ := [162, 163])
  have hm := merge_right (literal (valuationOf q) (317)) (literal (valuationOf q) (319)) (countLit q [161]) (countLit q [162, 163]) (count319 q) 1 (meaning317 q) (meaning319 q) hs
  change valuationOf q 317 = false ∨ valuationOf q 319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause751 (q : Snake 81) (h : Conditions q) : valuation q 317 = false ∨ valuation q 319 = true := counterClause751 (baseVal q)

theorem counterClause752 (q : Nat → Bool) : valuationOf q 167 = false ∨ valuationOf q 323 = true := by
  have hs : count323 q = (countLit q [166]) + (countLit q [167]) := List.countP_append (p := literal q) (l₁ := [166]) (l₂ := [167])
  have hm := merge_right (literal (valuationOf q) (167)) (literal (valuationOf q) (323)) (countLit q [166]) (countLit q [167]) (count323 q) 1 (meaning167 q) (meaning323 q) hs
  change valuationOf q 167 = false ∨ valuationOf q 323 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause752 (q : Snake 81) (h : Conditions q) : valuation q 167 = false ∨ valuation q 323 = true := counterClause752 (baseVal q)

theorem counterClause753 (q : Nat → Bool) : valuationOf q 166 = false ∨ valuationOf q 323 = true := by
  have hs : count323 q = (countLit q [166]) + (countLit q [167]) := List.countP_append (p := literal q) (l₁ := [166]) (l₂ := [167])
  have hm := merge_left (literal (valuationOf q) (166)) (literal (valuationOf q) (323)) (countLit q [166]) (countLit q [167]) (count323 q) 1 (meaning166 q) (meaning323 q) hs
  change valuationOf q 166 = false ∨ valuationOf q 323 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause753 (q : Snake 81) (h : Conditions q) : valuation q 166 = false ∨ valuation q 323 = true := counterClause753 (baseVal q)

theorem counterClause754 (q : Nat → Bool) : valuationOf q 166 = false ∨ valuationOf q 167 = false ∨ valuationOf q 324 = true := by
  have hs : count323 q = (countLit q [166]) + (countLit q [167]) := List.countP_append (p := literal q) (l₁ := [166]) (l₂ := [167])
  have hm := merge_two (literal (valuationOf q) (166)) (literal (valuationOf q) (167)) (literal (valuationOf q) (324)) (countLit q [166]) (countLit q [167]) (count323 q) 1 1 (meaning166 q) (meaning167 q) (meaning324 q) hs
  change valuationOf q 166 = false ∨ valuationOf q 167 = false ∨ valuationOf q 324 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause754 (q : Snake 81) (h : Conditions q) : valuation q 166 = false ∨ valuation q 167 = false ∨ valuation q 324 = true := counterClause754 (baseVal q)

theorem counterClause755 (q : Nat → Bool) : valuationOf q 323 = false ∨ valuationOf q 325 = true := by
  have hs : count325 q = (countLit q [164, 165]) + (countLit q [166, 167]) := List.countP_append (p := literal q) (l₁ := [164, 165]) (l₂ := [166, 167])
  have hm := merge_right (literal (valuationOf q) (323)) (literal (valuationOf q) (325)) (countLit q [164, 165]) (countLit q [166, 167]) (count325 q) 1 (meaning323 q) (meaning325 q) hs
  change valuationOf q 323 = false ∨ valuationOf q 325 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause755 (q : Snake 81) (h : Conditions q) : valuation q 323 = false ∨ valuation q 325 = true := counterClause755 (baseVal q)

theorem counterClause756 (q : Nat → Bool) : valuationOf q 324 = false ∨ valuationOf q 326 = true := by
  have hs : count325 q = (countLit q [164, 165]) + (countLit q [166, 167]) := List.countP_append (p := literal q) (l₁ := [164, 165]) (l₂ := [166, 167])
  have hm := merge_right (literal (valuationOf q) (324)) (literal (valuationOf q) (326)) (countLit q [164, 165]) (countLit q [166, 167]) (count325 q) 2 (meaning324 q) (meaning326 q) hs
  change valuationOf q 324 = false ∨ valuationOf q 326 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause756 (q : Snake 81) (h : Conditions q) : valuation q 324 = false ∨ valuation q 326 = true := counterClause756 (baseVal q)

theorem counterClause757 (q : Nat → Bool) : valuationOf q 325 = false ∨ valuationOf q 327 = true := by
  have hs : count327 q = (countLit q [161, 162, 163]) + (countLit q [164, 165, 166, 167]) := List.countP_append (p := literal q) (l₁ := [161, 162, 163]) (l₂ := [164, 165, 166, 167])
  have hm := merge_right (literal (valuationOf q) (325)) (literal (valuationOf q) (327)) (countLit q [161, 162, 163]) (countLit q [164, 165, 166, 167]) (count327 q) 1 (meaning325 q) (meaning327 q) hs
  change valuationOf q 325 = false ∨ valuationOf q 327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause757 (q : Snake 81) (h : Conditions q) : valuation q 325 = false ∨ valuation q 327 = true := counterClause757 (baseVal q)

theorem counterClause758 (q : Nat → Bool) : valuationOf q 326 = false ∨ valuationOf q 328 = true := by
  have hs : count327 q = (countLit q [161, 162, 163]) + (countLit q [164, 165, 166, 167]) := List.countP_append (p := literal q) (l₁ := [161, 162, 163]) (l₂ := [164, 165, 166, 167])
  have hm := merge_right (literal (valuationOf q) (326)) (literal (valuationOf q) (328)) (countLit q [161, 162, 163]) (countLit q [164, 165, 166, 167]) (count327 q) 2 (meaning326 q) (meaning328 q) hs
  change valuationOf q 326 = false ∨ valuationOf q 328 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause758 (q : Snake 81) (h : Conditions q) : valuation q 326 = false ∨ valuation q 328 = true := counterClause758 (baseVal q)

theorem counterClause759 (q : Nat → Bool) : valuationOf q 319 = false ∨ valuationOf q 327 = true := by
  have hs : count327 q = (countLit q [161, 162, 163]) + (countLit q [164, 165, 166, 167]) := List.countP_append (p := literal q) (l₁ := [161, 162, 163]) (l₂ := [164, 165, 166, 167])
  have hm := merge_left (literal (valuationOf q) (319)) (literal (valuationOf q) (327)) (countLit q [161, 162, 163]) (countLit q [164, 165, 166, 167]) (count327 q) 1 (meaning319 q) (meaning327 q) hs
  change valuationOf q 319 = false ∨ valuationOf q 327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause759 (q : Snake 81) (h : Conditions q) : valuation q 319 = false ∨ valuation q 327 = true := counterClause759 (baseVal q)

theorem counterClause760 (q : Nat → Bool) : valuationOf q 170 = false ∨ valuationOf q 331 = true := by
  have hs : count331 q = (countLit q [170]) + (countLit q [171]) := List.countP_append (p := literal q) (l₁ := [170]) (l₂ := [171])
  have hm := merge_left (literal (valuationOf q) (170)) (literal (valuationOf q) (331)) (countLit q [170]) (countLit q [171]) (count331 q) 1 (meaning170 q) (meaning331 q) hs
  change valuationOf q 170 = false ∨ valuationOf q 331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause760 (q : Snake 81) (h : Conditions q) : valuation q 170 = false ∨ valuation q 331 = true := counterClause760 (baseVal q)

theorem counterClause761 (q : Nat → Bool) : valuationOf q 331 = false ∨ valuationOf q 333 = true := by
  have hs : count333 q = (countLit q [168, 169]) + (countLit q [170, 171]) := List.countP_append (p := literal q) (l₁ := [168, 169]) (l₂ := [170, 171])
  have hm := merge_right (literal (valuationOf q) (331)) (literal (valuationOf q) (333)) (countLit q [168, 169]) (countLit q [170, 171]) (count333 q) 1 (meaning331 q) (meaning333 q) hs
  change valuationOf q 331 = false ∨ valuationOf q 333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause761 (q : Snake 81) (h : Conditions q) : valuation q 331 = false ∨ valuation q 333 = true := counterClause761 (baseVal q)

theorem counterClause762 (q : Nat → Bool) : valuationOf q 172 = false ∨ valuationOf q 335 = true := by
  have hs : count335 q = (countLit q [172]) + (countLit q [173]) := List.countP_append (p := literal q) (l₁ := [172]) (l₂ := [173])
  have hm := merge_left (literal (valuationOf q) (172)) (literal (valuationOf q) (335)) (countLit q [172]) (countLit q [173]) (count335 q) 1 (meaning172 q) (meaning335 q) hs
  change valuationOf q 172 = false ∨ valuationOf q 335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause762 (q : Snake 81) (h : Conditions q) : valuation q 172 = false ∨ valuation q 335 = true := counterClause762 (baseVal q)

theorem counterClause763 (q : Nat → Bool) : valuationOf q 335 = false ∨ valuationOf q 339 = true := by
  have hs : count339 q = (countLit q [172, 173]) + (countLit q [174, 175]) := List.countP_append (p := literal q) (l₁ := [172, 173]) (l₂ := [174, 175])
  have hm := merge_left (literal (valuationOf q) (335)) (literal (valuationOf q) (339)) (countLit q [172, 173]) (countLit q [174, 175]) (count339 q) 1 (meaning335 q) (meaning339 q) hs
  change valuationOf q 335 = false ∨ valuationOf q 339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause763 (q : Snake 81) (h : Conditions q) : valuation q 335 = false ∨ valuation q 339 = true := counterClause763 (baseVal q)

theorem counterClause764 (q : Nat → Bool) : valuationOf q 339 = false ∨ valuationOf q 341 = true := by
  have hs : count341 q = (countLit q [168, 169, 170, 171]) + (countLit q [172, 173, 174, 175]) := List.countP_append (p := literal q) (l₁ := [168, 169, 170, 171]) (l₂ := [172, 173, 174, 175])
  have hm := merge_right (literal (valuationOf q) (339)) (literal (valuationOf q) (341)) (countLit q [168, 169, 170, 171]) (countLit q [172, 173, 174, 175]) (count341 q) 1 (meaning339 q) (meaning341 q) hs
  change valuationOf q 339 = false ∨ valuationOf q 341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause764 (q : Snake 81) (h : Conditions q) : valuation q 339 = false ∨ valuation q 341 = true := counterClause764 (baseVal q)

theorem counterClause765 (q : Nat → Bool) : valuationOf q 333 = false ∨ valuationOf q 341 = true := by
  have hs : count341 q = (countLit q [168, 169, 170, 171]) + (countLit q [172, 173, 174, 175]) := List.countP_append (p := literal q) (l₁ := [168, 169, 170, 171]) (l₂ := [172, 173, 174, 175])
  have hm := merge_left (literal (valuationOf q) (333)) (literal (valuationOf q) (341)) (countLit q [168, 169, 170, 171]) (countLit q [172, 173, 174, 175]) (count341 q) 1 (meaning333 q) (meaning341 q) hs
  change valuationOf q 333 = false ∨ valuationOf q 341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause765 (q : Snake 81) (h : Conditions q) : valuation q 333 = false ∨ valuation q 341 = true := counterClause765 (baseVal q)

theorem counterClause766 (q : Nat → Bool) : valuationOf q 333 = false ∨ valuationOf q 339 = false ∨ valuationOf q 342 = true := by
  have hs : count341 q = (countLit q [168, 169, 170, 171]) + (countLit q [172, 173, 174, 175]) := List.countP_append (p := literal q) (l₁ := [168, 169, 170, 171]) (l₂ := [172, 173, 174, 175])
  have hm := merge_two (literal (valuationOf q) (333)) (literal (valuationOf q) (339)) (literal (valuationOf q) (342)) (countLit q [168, 169, 170, 171]) (countLit q [172, 173, 174, 175]) (count341 q) 1 1 (meaning333 q) (meaning339 q) (meaning342 q) hs
  change valuationOf q 333 = false ∨ valuationOf q 339 = false ∨ valuationOf q 342 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause766 (q : Snake 81) (h : Conditions q) : valuation q 333 = false ∨ valuation q 339 = false ∨ valuation q 342 = true := counterClause766 (baseVal q)

theorem counterClause767 (q : Nat → Bool) : valuationOf q 341 = false ∨ valuationOf q 343 = true := by
  have hs : count343 q = (countLit q [161, 162, 163, 164, 165, 166, 167]) + (countLit q [168, 169, 170, 171, 172, 173, 174, 175]) := List.countP_append (p := literal q) (l₁ := [161, 162, 163, 164, 165, 166, 167]) (l₂ := [168, 169, 170, 171, 172, 173, 174, 175])
  have hm := merge_right (literal (valuationOf q) (341)) (literal (valuationOf q) (343)) (countLit q [161, 162, 163, 164, 165, 166, 167]) (countLit q [168, 169, 170, 171, 172, 173, 174, 175]) (count343 q) 1 (meaning341 q) (meaning343 q) hs
  change valuationOf q 341 = false ∨ valuationOf q 343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause767 (q : Snake 81) (h : Conditions q) : valuation q 341 = false ∨ valuation q 343 = true := counterClause767 (baseVal q)

theorem counterClause768 (q : Nat → Bool) : valuationOf q 342 = false ∨ valuationOf q 344 = true := by
  have hs : count343 q = (countLit q [161, 162, 163, 164, 165, 166, 167]) + (countLit q [168, 169, 170, 171, 172, 173, 174, 175]) := List.countP_append (p := literal q) (l₁ := [161, 162, 163, 164, 165, 166, 167]) (l₂ := [168, 169, 170, 171, 172, 173, 174, 175])
  have hm := merge_right (literal (valuationOf q) (342)) (literal (valuationOf q) (344)) (countLit q [161, 162, 163, 164, 165, 166, 167]) (countLit q [168, 169, 170, 171, 172, 173, 174, 175]) (count343 q) 2 (meaning342 q) (meaning344 q) hs
  change valuationOf q 342 = false ∨ valuationOf q 344 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause768 (q : Snake 81) (h : Conditions q) : valuation q 342 = false ∨ valuation q 344 = true := counterClause768 (baseVal q)

theorem block23 (q : Snake 81) (h : Conditions q) : B112E207.Block23 (valuation q) :=
  ⟨clause737 q h, clause738 q h, clause739 q h, clause740 q h, clause741 q h, clause742 q h, clause743 q h, clause744 q h, clause745 q h, clause746 q h, clause747 q h, clause748 q h, clause749 q h, clause750 q h, clause751 q h, clause752 q h, clause753 q h, clause754 q h, clause755 q h, clause756 q h, clause757 q h, clause758 q h, clause759 q h, clause760 q h, clause761 q h, clause762 q h, clause763 q h, clause764 q h, clause765 q h, clause766 q h, clause767 q h, clause768 q h⟩

end
end Snake9.Regrowth.E112207
