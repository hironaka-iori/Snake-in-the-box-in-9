import E112186Semantics
import B112E186Inputs
namespace Snake9.Regrowth.E112186
noncomputable section
local instance blockDec23 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause737 (q : Nat → Bool) : valuationOf q 287 = false ∨ valuationOf q 301 = false ∨ valuationOf q 304 = true := by
  have hs : count303 q = (countLit q [141, 142, 143, 144, 145, 146, 147]) + (countLit q [148, 149, 150, 151, 152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [141, 142, 143, 144, 145, 146, 147]) (l₂ := [148, 149, 150, 151, 152, 153, 154, 155])
  have hm := merge_two (literal (valuationOf q) (287)) (literal (valuationOf q) (301)) (literal (valuationOf q) (304)) (countLit q [141, 142, 143, 144, 145, 146, 147]) (countLit q [148, 149, 150, 151, 152, 153, 154, 155]) (count303 q) 1 1 (meaning287 q) (meaning301 q) (meaning304 q) hs
  change valuationOf q 287 = false ∨ valuationOf q 301 = false ∨ valuationOf q 304 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause737 (q : Snake 81) (h : Conditions q) : valuation q 287 = false ∨ valuation q 301 = false ∨ valuation q 304 = true := counterClause737 (baseVal q)

theorem counterClause738 (q : Nat → Bool) : valuationOf q 303 = false ∨ valuationOf q 305 = true := by
  have hs : count305 q = (countLit q [125, 126, 127, 128, 129, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140]) + (countLit q [141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140]) (l₂ := [141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155])
  have hm := merge_right (literal (valuationOf q) (303)) (literal (valuationOf q) (305)) (countLit q [125, 126, 127, 128, 129, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140]) (countLit q [141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (count305 q) 1 (meaning303 q) (meaning305 q) hs
  change valuationOf q 303 = false ∨ valuationOf q 305 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause738 (q : Snake 81) (h : Conditions q) : valuation q 303 = false ∨ valuation q 305 = true := counterClause738 (baseVal q)

theorem counterClause739 (q : Nat → Bool) : valuationOf q 304 = false ∨ valuationOf q 306 = true := by
  have hs : count305 q = (countLit q [125, 126, 127, 128, 129, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140]) + (countLit q [141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140]) (l₂ := [141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155])
  have hm := merge_right (literal (valuationOf q) (304)) (literal (valuationOf q) (306)) (countLit q [125, 126, 127, 128, 129, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140]) (countLit q [141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (count305 q) 2 (meaning304 q) (meaning306 q) hs
  change valuationOf q 304 = false ∨ valuationOf q 306 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause739 (q : Snake 81) (h : Conditions q) : valuation q 304 = false ∨ valuation q 306 = true := counterClause739 (baseVal q)

theorem counterClause740 (q : Nat → Bool) : valuationOf q 275 = false ∨ valuationOf q 305 = true := by
  have hs : count305 q = (countLit q [125, 126, 127, 128, 129, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140]) + (countLit q [141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140]) (l₂ := [141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155])
  have hm := merge_left (literal (valuationOf q) (275)) (literal (valuationOf q) (305)) (countLit q [125, 126, 127, 128, 129, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140]) (countLit q [141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (count305 q) 1 (meaning275 q) (meaning305 q) hs
  change valuationOf q 275 = false ∨ valuationOf q 305 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause740 (q : Snake 81) (h : Conditions q) : valuation q 275 = false ∨ valuation q 305 = true := counterClause740 (baseVal q)

theorem counterClause741 (q : Nat → Bool) : valuationOf q 275 = false ∨ valuationOf q 303 = false ∨ valuationOf q 306 = true := by
  have hs : count305 q = (countLit q [125, 126, 127, 128, 129, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140]) + (countLit q [141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140]) (l₂ := [141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155])
  have hm := merge_two (literal (valuationOf q) (275)) (literal (valuationOf q) (303)) (literal (valuationOf q) (306)) (countLit q [125, 126, 127, 128, 129, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140]) (countLit q [141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (count305 q) 1 1 (meaning275 q) (meaning303 q) (meaning306 q) hs
  change valuationOf q 275 = false ∨ valuationOf q 303 = false ∨ valuationOf q 306 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause741 (q : Snake 81) (h : Conditions q) : valuation q 275 = false ∨ valuation q 303 = false ∨ valuation q 306 = true := counterClause741 (baseVal q)

theorem counterClause742 (q : Nat → Bool) : valuationOf q 162 = false ∨ valuationOf q 313 = true := by
  have hs : count313 q = (countLit q [161]) + (countLit q [162]) := List.countP_append (p := literal q) (l₁ := [161]) (l₂ := [162])
  have hm := merge_right (literal (valuationOf q) (162)) (literal (valuationOf q) (313)) (countLit q [161]) (countLit q [162]) (count313 q) 1 (meaning162 q) (meaning313 q) hs
  change valuationOf q 162 = false ∨ valuationOf q 313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause742 (q : Snake 81) (h : Conditions q) : valuation q 162 = false ∨ valuation q 313 = true := counterClause742 (baseVal q)

theorem counterClause743 (q : Nat → Bool) : valuationOf q 313 = false ∨ valuationOf q 315 = true := by
  have hs : count315 q = (countLit q [159, 160]) + (countLit q [161, 162]) := List.countP_append (p := literal q) (l₁ := [159, 160]) (l₂ := [161, 162])
  have hm := merge_right (literal (valuationOf q) (313)) (literal (valuationOf q) (315)) (countLit q [159, 160]) (countLit q [161, 162]) (count315 q) 1 (meaning313 q) (meaning315 q) hs
  change valuationOf q 313 = false ∨ valuationOf q 315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause743 (q : Snake 81) (h : Conditions q) : valuation q 313 = false ∨ valuation q 315 = true := counterClause743 (baseVal q)

theorem counterClause744 (q : Nat → Bool) : valuationOf q 315 = false ∨ valuationOf q 317 = true := by
  have hs : count317 q = (countLit q [156, 157, 158]) + (countLit q [159, 160, 161, 162]) := List.countP_append (p := literal q) (l₁ := [156, 157, 158]) (l₂ := [159, 160, 161, 162])
  have hm := merge_right (literal (valuationOf q) (315)) (literal (valuationOf q) (317)) (countLit q [156, 157, 158]) (countLit q [159, 160, 161, 162]) (count317 q) 1 (meaning315 q) (meaning317 q) hs
  change valuationOf q 315 = false ∨ valuationOf q 317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause744 (q : Snake 81) (h : Conditions q) : valuation q 315 = false ∨ valuation q 317 = true := counterClause744 (baseVal q)

theorem counterClause745 (q : Nat → Bool) : valuationOf q 164 = false ∨ valuationOf q 319 = true := by
  have hs : count319 q = (countLit q [163]) + (countLit q [164]) := List.countP_append (p := literal q) (l₁ := [163]) (l₂ := [164])
  have hm := merge_right (literal (valuationOf q) (164)) (literal (valuationOf q) (319)) (countLit q [163]) (countLit q [164]) (count319 q) 1 (meaning164 q) (meaning319 q) hs
  change valuationOf q 164 = false ∨ valuationOf q 319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause745 (q : Snake 81) (h : Conditions q) : valuation q 164 = false ∨ valuation q 319 = true := counterClause745 (baseVal q)

theorem counterClause746 (q : Nat → Bool) : valuationOf q 163 = false ∨ valuationOf q 319 = true := by
  have hs : count319 q = (countLit q [163]) + (countLit q [164]) := List.countP_append (p := literal q) (l₁ := [163]) (l₂ := [164])
  have hm := merge_left (literal (valuationOf q) (163)) (literal (valuationOf q) (319)) (countLit q [163]) (countLit q [164]) (count319 q) 1 (meaning163 q) (meaning319 q) hs
  change valuationOf q 163 = false ∨ valuationOf q 319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause746 (q : Snake 81) (h : Conditions q) : valuation q 163 = false ∨ valuation q 319 = true := counterClause746 (baseVal q)

theorem counterClause747 (q : Nat → Bool) : valuationOf q 319 = false ∨ valuationOf q 323 = true := by
  have hs : count323 q = (countLit q [163, 164]) + (countLit q [165, 166]) := List.countP_append (p := literal q) (l₁ := [163, 164]) (l₂ := [165, 166])
  have hm := merge_left (literal (valuationOf q) (319)) (literal (valuationOf q) (323)) (countLit q [163, 164]) (countLit q [165, 166]) (count323 q) 1 (meaning319 q) (meaning323 q) hs
  change valuationOf q 319 = false ∨ valuationOf q 323 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause747 (q : Snake 81) (h : Conditions q) : valuation q 319 = false ∨ valuation q 323 = true := counterClause747 (baseVal q)

theorem counterClause748 (q : Nat → Bool) : valuationOf q 170 = false ∨ valuationOf q 327 = true := by
  have hs : count327 q = (countLit q [169]) + (countLit q [170]) := List.countP_append (p := literal q) (l₁ := [169]) (l₂ := [170])
  have hm := merge_right (literal (valuationOf q) (170)) (literal (valuationOf q) (327)) (countLit q [169]) (countLit q [170]) (count327 q) 1 (meaning170 q) (meaning327 q) hs
  change valuationOf q 170 = false ∨ valuationOf q 327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause748 (q : Snake 81) (h : Conditions q) : valuation q 170 = false ∨ valuation q 327 = true := counterClause748 (baseVal q)

theorem counterClause749 (q : Nat → Bool) : valuationOf q 169 = false ∨ valuationOf q 327 = true := by
  have hs : count327 q = (countLit q [169]) + (countLit q [170]) := List.countP_append (p := literal q) (l₁ := [169]) (l₂ := [170])
  have hm := merge_left (literal (valuationOf q) (169)) (literal (valuationOf q) (327)) (countLit q [169]) (countLit q [170]) (count327 q) 1 (meaning169 q) (meaning327 q) hs
  change valuationOf q 169 = false ∨ valuationOf q 327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause749 (q : Snake 81) (h : Conditions q) : valuation q 169 = false ∨ valuation q 327 = true := counterClause749 (baseVal q)

theorem counterClause750 (q : Nat → Bool) : valuationOf q 327 = false ∨ valuationOf q 329 = true := by
  have hs : count329 q = (countLit q [167, 168]) + (countLit q [169, 170]) := List.countP_append (p := literal q) (l₁ := [167, 168]) (l₂ := [169, 170])
  have hm := merge_right (literal (valuationOf q) (327)) (literal (valuationOf q) (329)) (countLit q [167, 168]) (countLit q [169, 170]) (count329 q) 1 (meaning327 q) (meaning329 q) hs
  change valuationOf q 327 = false ∨ valuationOf q 329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause750 (q : Snake 81) (h : Conditions q) : valuation q 327 = false ∨ valuation q 329 = true := counterClause750 (baseVal q)

theorem counterClause751 (q : Nat → Bool) : valuationOf q 329 = false ∨ valuationOf q 331 = true := by
  have hs : count331 q = (countLit q [163, 164, 165, 166]) + (countLit q [167, 168, 169, 170]) := List.countP_append (p := literal q) (l₁ := [163, 164, 165, 166]) (l₂ := [167, 168, 169, 170])
  have hm := merge_right (literal (valuationOf q) (329)) (literal (valuationOf q) (331)) (countLit q [163, 164, 165, 166]) (countLit q [167, 168, 169, 170]) (count331 q) 1 (meaning329 q) (meaning331 q) hs
  change valuationOf q 329 = false ∨ valuationOf q 331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause751 (q : Snake 81) (h : Conditions q) : valuation q 329 = false ∨ valuation q 331 = true := counterClause751 (baseVal q)

theorem counterClause752 (q : Nat → Bool) : valuationOf q 323 = false ∨ valuationOf q 331 = true := by
  have hs : count331 q = (countLit q [163, 164, 165, 166]) + (countLit q [167, 168, 169, 170]) := List.countP_append (p := literal q) (l₁ := [163, 164, 165, 166]) (l₂ := [167, 168, 169, 170])
  have hm := merge_left (literal (valuationOf q) (323)) (literal (valuationOf q) (331)) (countLit q [163, 164, 165, 166]) (countLit q [167, 168, 169, 170]) (count331 q) 1 (meaning323 q) (meaning331 q) hs
  change valuationOf q 323 = false ∨ valuationOf q 331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause752 (q : Snake 81) (h : Conditions q) : valuation q 323 = false ∨ valuation q 331 = true := counterClause752 (baseVal q)

theorem counterClause753 (q : Nat → Bool) : valuationOf q 323 = false ∨ valuationOf q 329 = false ∨ valuationOf q 332 = true := by
  have hs : count331 q = (countLit q [163, 164, 165, 166]) + (countLit q [167, 168, 169, 170]) := List.countP_append (p := literal q) (l₁ := [163, 164, 165, 166]) (l₂ := [167, 168, 169, 170])
  have hm := merge_two (literal (valuationOf q) (323)) (literal (valuationOf q) (329)) (literal (valuationOf q) (332)) (countLit q [163, 164, 165, 166]) (countLit q [167, 168, 169, 170]) (count331 q) 1 1 (meaning323 q) (meaning329 q) (meaning332 q) hs
  change valuationOf q 323 = false ∨ valuationOf q 329 = false ∨ valuationOf q 332 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause753 (q : Snake 81) (h : Conditions q) : valuation q 323 = false ∨ valuation q 329 = false ∨ valuation q 332 = true := counterClause753 (baseVal q)

theorem counterClause754 (q : Nat → Bool) : valuationOf q 331 = false ∨ valuationOf q 333 = true := by
  have hs : count333 q = (countLit q [156, 157, 158, 159, 160, 161, 162]) + (countLit q [163, 164, 165, 166, 167, 168, 169, 170]) := List.countP_append (p := literal q) (l₁ := [156, 157, 158, 159, 160, 161, 162]) (l₂ := [163, 164, 165, 166, 167, 168, 169, 170])
  have hm := merge_right (literal (valuationOf q) (331)) (literal (valuationOf q) (333)) (countLit q [156, 157, 158, 159, 160, 161, 162]) (countLit q [163, 164, 165, 166, 167, 168, 169, 170]) (count333 q) 1 (meaning331 q) (meaning333 q) hs
  change valuationOf q 331 = false ∨ valuationOf q 333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause754 (q : Snake 81) (h : Conditions q) : valuation q 331 = false ∨ valuation q 333 = true := counterClause754 (baseVal q)

theorem counterClause755 (q : Nat → Bool) : valuationOf q 332 = false ∨ valuationOf q 334 = true := by
  have hs : count333 q = (countLit q [156, 157, 158, 159, 160, 161, 162]) + (countLit q [163, 164, 165, 166, 167, 168, 169, 170]) := List.countP_append (p := literal q) (l₁ := [156, 157, 158, 159, 160, 161, 162]) (l₂ := [163, 164, 165, 166, 167, 168, 169, 170])
  have hm := merge_right (literal (valuationOf q) (332)) (literal (valuationOf q) (334)) (countLit q [156, 157, 158, 159, 160, 161, 162]) (countLit q [163, 164, 165, 166, 167, 168, 169, 170]) (count333 q) 2 (meaning332 q) (meaning334 q) hs
  change valuationOf q 332 = false ∨ valuationOf q 334 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause755 (q : Snake 81) (h : Conditions q) : valuation q 332 = false ∨ valuation q 334 = true := counterClause755 (baseVal q)

theorem counterClause756 (q : Nat → Bool) : valuationOf q 317 = false ∨ valuationOf q 333 = true := by
  have hs : count333 q = (countLit q [156, 157, 158, 159, 160, 161, 162]) + (countLit q [163, 164, 165, 166, 167, 168, 169, 170]) := List.countP_append (p := literal q) (l₁ := [156, 157, 158, 159, 160, 161, 162]) (l₂ := [163, 164, 165, 166, 167, 168, 169, 170])
  have hm := merge_left (literal (valuationOf q) (317)) (literal (valuationOf q) (333)) (countLit q [156, 157, 158, 159, 160, 161, 162]) (countLit q [163, 164, 165, 166, 167, 168, 169, 170]) (count333 q) 1 (meaning317 q) (meaning333 q) hs
  change valuationOf q 317 = false ∨ valuationOf q 333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause756 (q : Snake 81) (h : Conditions q) : valuation q 317 = false ∨ valuation q 333 = true := counterClause756 (baseVal q)

theorem counterClause757 (q : Nat → Bool) : valuationOf q 317 = false ∨ valuationOf q 331 = false ∨ valuationOf q 334 = true := by
  have hs : count333 q = (countLit q [156, 157, 158, 159, 160, 161, 162]) + (countLit q [163, 164, 165, 166, 167, 168, 169, 170]) := List.countP_append (p := literal q) (l₁ := [156, 157, 158, 159, 160, 161, 162]) (l₂ := [163, 164, 165, 166, 167, 168, 169, 170])
  have hm := merge_two (literal (valuationOf q) (317)) (literal (valuationOf q) (331)) (literal (valuationOf q) (334)) (countLit q [156, 157, 158, 159, 160, 161, 162]) (countLit q [163, 164, 165, 166, 167, 168, 169, 170]) (count333 q) 1 1 (meaning317 q) (meaning331 q) (meaning334 q) hs
  change valuationOf q 317 = false ∨ valuationOf q 331 = false ∨ valuationOf q 334 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause757 (q : Snake 81) (h : Conditions q) : valuation q 317 = false ∨ valuation q 331 = false ∨ valuation q 334 = true := counterClause757 (baseVal q)

theorem counterClause758 (q : Nat → Bool) : valuationOf q 171 = false ∨ valuationOf q 335 = true := by
  have hs : count335 q = (countLit q [171]) + (countLit q [172]) := List.countP_append (p := literal q) (l₁ := [171]) (l₂ := [172])
  have hm := merge_left (literal (valuationOf q) (171)) (literal (valuationOf q) (335)) (countLit q [171]) (countLit q [172]) (count335 q) 1 (meaning171 q) (meaning335 q) hs
  change valuationOf q 171 = false ∨ valuationOf q 335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause758 (q : Snake 81) (h : Conditions q) : valuation q 171 = false ∨ valuation q 335 = true := counterClause758 (baseVal q)

theorem counterClause759 (q : Nat → Bool) : valuationOf q 335 = false ∨ valuationOf q 339 = true := by
  have hs : count339 q = (countLit q [171, 172]) + (countLit q [173, 174]) := List.countP_append (p := literal q) (l₁ := [171, 172]) (l₂ := [173, 174])
  have hm := merge_left (literal (valuationOf q) (335)) (literal (valuationOf q) (339)) (countLit q [171, 172]) (countLit q [173, 174]) (count339 q) 1 (meaning335 q) (meaning339 q) hs
  change valuationOf q 335 = false ∨ valuationOf q 339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause759 (q : Snake 81) (h : Conditions q) : valuation q 335 = false ∨ valuation q 339 = true := counterClause759 (baseVal q)

theorem counterClause760 (q : Nat → Bool) : valuationOf q 339 = false ∨ valuationOf q 347 = true := by
  have hs : count347 q = (countLit q [171, 172, 173, 174]) + (countLit q [175, 176, 177, 178]) := List.countP_append (p := literal q) (l₁ := [171, 172, 173, 174]) (l₂ := [175, 176, 177, 178])
  have hm := merge_left (literal (valuationOf q) (339)) (literal (valuationOf q) (347)) (countLit q [171, 172, 173, 174]) (countLit q [175, 176, 177, 178]) (count347 q) 1 (meaning339 q) (meaning347 q) hs
  change valuationOf q 339 = false ∨ valuationOf q 347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause760 (q : Snake 81) (h : Conditions q) : valuation q 339 = false ∨ valuation q 347 = true := counterClause760 (baseVal q)

theorem counterClause761 (q : Nat → Bool) : valuationOf q 347 = false ∨ valuationOf q 363 = true := by
  have hs : count363 q = (countLit q [171, 172, 173, 174, 175, 176, 177, 178]) + (countLit q [179, 180, 181, 182, 183, 184, 185, 186]) := List.countP_append (p := literal q) (l₁ := [171, 172, 173, 174, 175, 176, 177, 178]) (l₂ := [179, 180, 181, 182, 183, 184, 185, 186])
  have hm := merge_left (literal (valuationOf q) (347)) (literal (valuationOf q) (363)) (countLit q [171, 172, 173, 174, 175, 176, 177, 178]) (countLit q [179, 180, 181, 182, 183, 184, 185, 186]) (count363 q) 1 (meaning347 q) (meaning363 q) hs
  change valuationOf q 347 = false ∨ valuationOf q 363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause761 (q : Snake 81) (h : Conditions q) : valuation q 347 = false ∨ valuation q 363 = true := counterClause761 (baseVal q)

theorem counterClause762 (q : Nat → Bool) : valuationOf q 363 = false ∨ valuationOf q 365 = true := by
  have hs : count365 q = (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) + (countLit q [171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) := List.countP_append (p := literal q) (l₁ := [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) (l₂ := [171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186])
  have hm := merge_right (literal (valuationOf q) (363)) (literal (valuationOf q) (365)) (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) (countLit q [171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) (count365 q) 1 (meaning363 q) (meaning365 q) hs
  change valuationOf q 363 = false ∨ valuationOf q 365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause762 (q : Snake 81) (h : Conditions q) : valuation q 363 = false ∨ valuation q 365 = true := counterClause762 (baseVal q)

theorem counterClause763 (q : Nat → Bool) : valuationOf q 333 = false ∨ valuationOf q 365 = true := by
  have hs : count365 q = (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) + (countLit q [171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) := List.countP_append (p := literal q) (l₁ := [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) (l₂ := [171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186])
  have hm := merge_left (literal (valuationOf q) (333)) (literal (valuationOf q) (365)) (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) (countLit q [171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) (count365 q) 1 (meaning333 q) (meaning365 q) hs
  change valuationOf q 333 = false ∨ valuationOf q 365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause763 (q : Snake 81) (h : Conditions q) : valuation q 333 = false ∨ valuation q 365 = true := counterClause763 (baseVal q)

theorem counterClause764 (q : Nat → Bool) : valuationOf q 334 = false ∨ valuationOf q 366 = true := by
  have hs : count365 q = (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) + (countLit q [171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) := List.countP_append (p := literal q) (l₁ := [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) (l₂ := [171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186])
  have hm := merge_left (literal (valuationOf q) (334)) (literal (valuationOf q) (366)) (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) (countLit q [171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) (count365 q) 2 (meaning334 q) (meaning366 q) hs
  change valuationOf q 334 = false ∨ valuationOf q 366 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause764 (q : Snake 81) (h : Conditions q) : valuation q 334 = false ∨ valuation q 366 = true := counterClause764 (baseVal q)

theorem counterClause765 (q : Nat → Bool) : valuationOf q 365 = false ∨ valuationOf q 367 = true := by
  have hs : count367 q = (countLit q [125, 126, 127, 128, 129, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) + (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (l₂ := [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186])
  have hm := merge_right (literal (valuationOf q) (365)) (literal (valuationOf q) (367)) (countLit q [125, 126, 127, 128, 129, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) (count367 q) 1 (meaning365 q) (meaning367 q) hs
  change valuationOf q 365 = false ∨ valuationOf q 367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause765 (q : Snake 81) (h : Conditions q) : valuation q 365 = false ∨ valuation q 367 = true := counterClause765 (baseVal q)

theorem counterClause766 (q : Nat → Bool) : valuationOf q 366 = false ∨ valuationOf q 368 = true := by
  have hs : count367 q = (countLit q [125, 126, 127, 128, 129, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) + (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (l₂ := [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186])
  have hm := merge_right (literal (valuationOf q) (366)) (literal (valuationOf q) (368)) (countLit q [125, 126, 127, 128, 129, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) (count367 q) 2 (meaning366 q) (meaning368 q) hs
  change valuationOf q 366 = false ∨ valuationOf q 368 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause766 (q : Snake 81) (h : Conditions q) : valuation q 366 = false ∨ valuation q 368 = true := counterClause766 (baseVal q)

theorem counterClause767 (q : Nat → Bool) : valuationOf q 305 = false ∨ valuationOf q 367 = true := by
  have hs : count367 q = (countLit q [125, 126, 127, 128, 129, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) + (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (l₂ := [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186])
  have hm := merge_left (literal (valuationOf q) (305)) (literal (valuationOf q) (367)) (countLit q [125, 126, 127, 128, 129, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) (count367 q) 1 (meaning305 q) (meaning367 q) hs
  change valuationOf q 305 = false ∨ valuationOf q 367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause767 (q : Snake 81) (h : Conditions q) : valuation q 305 = false ∨ valuation q 367 = true := counterClause767 (baseVal q)

theorem counterClause768 (q : Nat → Bool) : valuationOf q 305 = false ∨ valuationOf q 365 = false ∨ valuationOf q 368 = true := by
  have hs : count367 q = (countLit q [125, 126, 127, 128, 129, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) + (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (l₂ := [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186])
  have hm := merge_two (literal (valuationOf q) (305)) (literal (valuationOf q) (365)) (literal (valuationOf q) (368)) (countLit q [125, 126, 127, 128, 129, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (countLit q [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) (count367 q) 1 1 (meaning305 q) (meaning365 q) (meaning368 q) hs
  change valuationOf q 305 = false ∨ valuationOf q 365 = false ∨ valuationOf q 368 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause768 (q : Snake 81) (h : Conditions q) : valuation q 305 = false ∨ valuation q 365 = false ∨ valuation q 368 = true := counterClause768 (baseVal q)

theorem block23 (q : Snake 81) (h : Conditions q) : B112E186.Block23 (valuation q) :=
  ⟨clause737 q h, clause738 q h, clause739 q h, clause740 q h, clause741 q h, clause742 q h, clause743 q h, clause744 q h, clause745 q h, clause746 q h, clause747 q h, clause748 q h, clause749 q h, clause750 q h, clause751 q h, clause752 q h, clause753 q h, clause754 q h, clause755 q h, clause756 q h, clause757 q h, clause758 q h, clause759 q h, clause760 q h, clause761 q h, clause762 q h, clause763 q h, clause764 q h, clause765 q h, clause766 q h, clause767 q h, clause768 q h⟩

end
end Snake9.Regrowth.E112186
