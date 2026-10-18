import E112020Semantics
import B112E020Inputs
namespace Snake9.Regrowth.E112020
noncomputable section
local instance blockDec27 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause865 (q : Nat → Bool) : valuationOf q 276 = false ∨ valuationOf q 306 = true := by
  have hs : count305 q = (countLit q [125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140]) + (countLit q [141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) := List.countP_append (p := literal q) (l₁ := [125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140]) (l₂ := [141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155])
  have hm := merge_left (literal (valuationOf q) (276)) (literal (valuationOf q) (306)) (countLit q [125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140]) (countLit q [141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (count305 q) 2 (meaning276 q) (meaning306 q) hs
  change valuationOf q 276 = false ∨ valuationOf q 306 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause865 (q : Snake 81) (h : Conditions q) : valuation q 276 = false ∨ valuation q 306 = true := counterClause865 (baseVal q)

theorem counterClause866 (q : Nat → Bool) : valuationOf q 157 = false ∨ valuationOf q 307 = true := by
  have hs : count307 q = (countLit q [157]) + (countLit q [158]) := List.countP_append (p := literal q) (l₁ := [157]) (l₂ := [158])
  have hm := merge_left (literal (valuationOf q) (157)) (literal (valuationOf q) (307)) (countLit q [157]) (countLit q [158]) (count307 q) 1 (meaning157 q) (meaning307 q) hs
  change valuationOf q 157 = false ∨ valuationOf q 307 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause866 (q : Snake 81) (h : Conditions q) : valuation q 157 = false ∨ valuation q 307 = true := counterClause866 (baseVal q)

theorem counterClause867 (q : Nat → Bool) : valuationOf q 307 = false ∨ valuationOf q 309 = true := by
  have hs : count309 q = (countLit q [156]) + (countLit q [157, 158]) := List.countP_append (p := literal q) (l₁ := [156]) (l₂ := [157, 158])
  have hm := merge_right (literal (valuationOf q) (307)) (literal (valuationOf q) (309)) (countLit q [156]) (countLit q [157, 158]) (count309 q) 1 (meaning307 q) (meaning309 q) hs
  change valuationOf q 307 = false ∨ valuationOf q 309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause867 (q : Snake 81) (h : Conditions q) : valuation q 307 = false ∨ valuation q 309 = true := counterClause867 (baseVal q)

theorem counterClause868 (q : Nat → Bool) : valuationOf q 156 = false ∨ valuationOf q 309 = true := by
  have hs : count309 q = (countLit q [156]) + (countLit q [157, 158]) := List.countP_append (p := literal q) (l₁ := [156]) (l₂ := [157, 158])
  have hm := merge_left (literal (valuationOf q) (156)) (literal (valuationOf q) (309)) (countLit q [156]) (countLit q [157, 158]) (count309 q) 1 (meaning156 q) (meaning309 q) hs
  change valuationOf q 156 = false ∨ valuationOf q 309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause868 (q : Snake 81) (h : Conditions q) : valuation q 156 = false ∨ valuation q 309 = true := counterClause868 (baseVal q)

theorem counterClause869 (q : Nat → Bool) : valuationOf q 156 = false ∨ valuationOf q 307 = false ∨ valuationOf q 310 = true := by
  have hs : count309 q = (countLit q [156]) + (countLit q [157, 158]) := List.countP_append (p := literal q) (l₁ := [156]) (l₂ := [157, 158])
  have hm := merge_two (literal (valuationOf q) (156)) (literal (valuationOf q) (307)) (literal (valuationOf q) (310)) (countLit q [156]) (countLit q [157, 158]) (count309 q) 1 1 (meaning156 q) (meaning307 q) (meaning310 q) hs
  change valuationOf q 156 = false ∨ valuationOf q 307 = false ∨ valuationOf q 310 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause869 (q : Snake 81) (h : Conditions q) : valuation q 156 = false ∨ valuation q 307 = false ∨ valuation q 310 = true := counterClause869 (baseVal q)

theorem counterClause870 (q : Nat → Bool) : valuationOf q 160 = false ∨ valuationOf q 311 = true := by
  have hs : count311 q = (countLit q [159]) + (countLit q [160]) := List.countP_append (p := literal q) (l₁ := [159]) (l₂ := [160])
  have hm := merge_right (literal (valuationOf q) (160)) (literal (valuationOf q) (311)) (countLit q [159]) (countLit q [160]) (count311 q) 1 (meaning160 q) (meaning311 q) hs
  change valuationOf q 160 = false ∨ valuationOf q 311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause870 (q : Snake 81) (h : Conditions q) : valuation q 160 = false ∨ valuation q 311 = true := counterClause870 (baseVal q)

theorem counterClause871 (q : Nat → Bool) : valuationOf q 311 = false ∨ valuationOf q 315 = true := by
  have hs : count315 q = (countLit q [159, 160]) + (countLit q [161, 162]) := List.countP_append (p := literal q) (l₁ := [159, 160]) (l₂ := [161, 162])
  have hm := merge_left (literal (valuationOf q) (311)) (literal (valuationOf q) (315)) (countLit q [159, 160]) (countLit q [161, 162]) (count315 q) 1 (meaning311 q) (meaning315 q) hs
  change valuationOf q 311 = false ∨ valuationOf q 315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause871 (q : Snake 81) (h : Conditions q) : valuation q 311 = false ∨ valuation q 315 = true := counterClause871 (baseVal q)

theorem counterClause872 (q : Nat → Bool) : valuationOf q 315 = false ∨ valuationOf q 317 = true := by
  have hs : count317 q = (countLit q [156, 157, 158]) + (countLit q [159, 160, 161, 162]) := List.countP_append (p := literal q) (l₁ := [156, 157, 158]) (l₂ := [159, 160, 161, 162])
  have hm := merge_right (literal (valuationOf q) (315)) (literal (valuationOf q) (317)) (countLit q [156, 157, 158]) (countLit q [159, 160, 161, 162]) (count317 q) 1 (meaning315 q) (meaning317 q) hs
  change valuationOf q 315 = false ∨ valuationOf q 317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause872 (q : Snake 81) (h : Conditions q) : valuation q 315 = false ∨ valuation q 317 = true := counterClause872 (baseVal q)

theorem counterClause873 (q : Nat → Bool) : valuationOf q 309 = false ∨ valuationOf q 317 = true := by
  have hs : count317 q = (countLit q [156, 157, 158]) + (countLit q [159, 160, 161, 162]) := List.countP_append (p := literal q) (l₁ := [156, 157, 158]) (l₂ := [159, 160, 161, 162])
  have hm := merge_left (literal (valuationOf q) (309)) (literal (valuationOf q) (317)) (countLit q [156, 157, 158]) (countLit q [159, 160, 161, 162]) (count317 q) 1 (meaning309 q) (meaning317 q) hs
  change valuationOf q 309 = false ∨ valuationOf q 317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause873 (q : Snake 81) (h : Conditions q) : valuation q 309 = false ∨ valuation q 317 = true := counterClause873 (baseVal q)

theorem counterClause874 (q : Nat → Bool) : valuationOf q 310 = false ∨ valuationOf q 318 = true := by
  have hs : count317 q = (countLit q [156, 157, 158]) + (countLit q [159, 160, 161, 162]) := List.countP_append (p := literal q) (l₁ := [156, 157, 158]) (l₂ := [159, 160, 161, 162])
  have hm := merge_left (literal (valuationOf q) (310)) (literal (valuationOf q) (318)) (countLit q [156, 157, 158]) (countLit q [159, 160, 161, 162]) (count317 q) 2 (meaning310 q) (meaning318 q) hs
  change valuationOf q 310 = false ∨ valuationOf q 318 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause874 (q : Snake 81) (h : Conditions q) : valuation q 310 = false ∨ valuation q 318 = true := counterClause874 (baseVal q)

theorem counterClause875 (q : Nat → Bool) : valuationOf q 163 = false ∨ valuationOf q 319 = true := by
  have hs : count319 q = (countLit q [163]) + (countLit q [164]) := List.countP_append (p := literal q) (l₁ := [163]) (l₂ := [164])
  have hm := merge_left (literal (valuationOf q) (163)) (literal (valuationOf q) (319)) (countLit q [163]) (countLit q [164]) (count319 q) 1 (meaning163 q) (meaning319 q) hs
  change valuationOf q 163 = false ∨ valuationOf q 319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause875 (q : Snake 81) (h : Conditions q) : valuation q 163 = false ∨ valuation q 319 = true := counterClause875 (baseVal q)

theorem counterClause876 (q : Nat → Bool) : valuationOf q 165 = false ∨ valuationOf q 321 = true := by
  have hs : count321 q = (countLit q [165]) + (countLit q [166]) := List.countP_append (p := literal q) (l₁ := [165]) (l₂ := [166])
  have hm := merge_left (literal (valuationOf q) (165)) (literal (valuationOf q) (321)) (countLit q [165]) (countLit q [166]) (count321 q) 1 (meaning165 q) (meaning321 q) hs
  change valuationOf q 165 = false ∨ valuationOf q 321 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause876 (q : Snake 81) (h : Conditions q) : valuation q 165 = false ∨ valuation q 321 = true := counterClause876 (baseVal q)

theorem counterClause877 (q : Nat → Bool) : valuationOf q 321 = false ∨ valuationOf q 323 = true := by
  have hs : count323 q = (countLit q [163, 164]) + (countLit q [165, 166]) := List.countP_append (p := literal q) (l₁ := [163, 164]) (l₂ := [165, 166])
  have hm := merge_right (literal (valuationOf q) (321)) (literal (valuationOf q) (323)) (countLit q [163, 164]) (countLit q [165, 166]) (count323 q) 1 (meaning321 q) (meaning323 q) hs
  change valuationOf q 321 = false ∨ valuationOf q 323 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause877 (q : Snake 81) (h : Conditions q) : valuation q 321 = false ∨ valuation q 323 = true := counterClause877 (baseVal q)

theorem counterClause878 (q : Nat → Bool) : valuationOf q 319 = false ∨ valuationOf q 323 = true := by
  have hs : count323 q = (countLit q [163, 164]) + (countLit q [165, 166]) := List.countP_append (p := literal q) (l₁ := [163, 164]) (l₂ := [165, 166])
  have hm := merge_left (literal (valuationOf q) (319)) (literal (valuationOf q) (323)) (countLit q [163, 164]) (countLit q [165, 166]) (count323 q) 1 (meaning319 q) (meaning323 q) hs
  change valuationOf q 319 = false ∨ valuationOf q 323 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause878 (q : Snake 81) (h : Conditions q) : valuation q 319 = false ∨ valuation q 323 = true := counterClause878 (baseVal q)

theorem counterClause879 (q : Nat → Bool) : valuationOf q 168 = false ∨ valuationOf q 325 = true := by
  have hs : count325 q = (countLit q [167]) + (countLit q [168]) := List.countP_append (p := literal q) (l₁ := [167]) (l₂ := [168])
  have hm := merge_right (literal (valuationOf q) (168)) (literal (valuationOf q) (325)) (countLit q [167]) (countLit q [168]) (count325 q) 1 (meaning168 q) (meaning325 q) hs
  change valuationOf q 168 = false ∨ valuationOf q 325 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause879 (q : Snake 81) (h : Conditions q) : valuation q 168 = false ∨ valuation q 325 = true := counterClause879 (baseVal q)

theorem counterClause880 (q : Nat → Bool) : valuationOf q 170 = false ∨ valuationOf q 327 = true := by
  have hs : count327 q = (countLit q [169]) + (countLit q [170]) := List.countP_append (p := literal q) (l₁ := [169]) (l₂ := [170])
  have hm := merge_right (literal (valuationOf q) (170)) (literal (valuationOf q) (327)) (countLit q [169]) (countLit q [170]) (count327 q) 1 (meaning170 q) (meaning327 q) hs
  change valuationOf q 170 = false ∨ valuationOf q 327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause880 (q : Snake 81) (h : Conditions q) : valuation q 170 = false ∨ valuation q 327 = true := counterClause880 (baseVal q)

theorem counterClause881 (q : Nat → Bool) : valuationOf q 327 = false ∨ valuationOf q 329 = true := by
  have hs : count329 q = (countLit q [167, 168]) + (countLit q [169, 170]) := List.countP_append (p := literal q) (l₁ := [167, 168]) (l₂ := [169, 170])
  have hm := merge_right (literal (valuationOf q) (327)) (literal (valuationOf q) (329)) (countLit q [167, 168]) (countLit q [169, 170]) (count329 q) 1 (meaning327 q) (meaning329 q) hs
  change valuationOf q 327 = false ∨ valuationOf q 329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause881 (q : Snake 81) (h : Conditions q) : valuation q 327 = false ∨ valuation q 329 = true := counterClause881 (baseVal q)

theorem counterClause882 (q : Nat → Bool) : valuationOf q 325 = false ∨ valuationOf q 329 = true := by
  have hs : count329 q = (countLit q [167, 168]) + (countLit q [169, 170]) := List.countP_append (p := literal q) (l₁ := [167, 168]) (l₂ := [169, 170])
  have hm := merge_left (literal (valuationOf q) (325)) (literal (valuationOf q) (329)) (countLit q [167, 168]) (countLit q [169, 170]) (count329 q) 1 (meaning325 q) (meaning329 q) hs
  change valuationOf q 325 = false ∨ valuationOf q 329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause882 (q : Snake 81) (h : Conditions q) : valuation q 325 = false ∨ valuation q 329 = true := counterClause882 (baseVal q)

theorem counterClause883 (q : Nat → Bool) : valuationOf q 329 = false ∨ valuationOf q 331 = true := by
  have hs : count331 q = (countLit q [163, 164, 165, 166]) + (countLit q [167, 168, 169, 170]) := List.countP_append (p := literal q) (l₁ := [163, 164, 165, 166]) (l₂ := [167, 168, 169, 170])
  have hm := merge_right (literal (valuationOf q) (329)) (literal (valuationOf q) (331)) (countLit q [163, 164, 165, 166]) (countLit q [167, 168, 169, 170]) (count331 q) 1 (meaning329 q) (meaning331 q) hs
  change valuationOf q 329 = false ∨ valuationOf q 331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause883 (q : Snake 81) (h : Conditions q) : valuation q 329 = false ∨ valuation q 331 = true := counterClause883 (baseVal q)

theorem counterClause884 (q : Nat → Bool) : valuationOf q 323 = false ∨ valuationOf q 331 = true := by
  have hs : count331 q = (countLit q [163, 164, 165, 166]) + (countLit q [167, 168, 169, 170]) := List.countP_append (p := literal q) (l₁ := [163, 164, 165, 166]) (l₂ := [167, 168, 169, 170])
  have hm := merge_left (literal (valuationOf q) (323)) (literal (valuationOf q) (331)) (countLit q [163, 164, 165, 166]) (countLit q [167, 168, 169, 170]) (count331 q) 1 (meaning323 q) (meaning331 q) hs
  change valuationOf q 323 = false ∨ valuationOf q 331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause884 (q : Snake 81) (h : Conditions q) : valuation q 323 = false ∨ valuation q 331 = true := counterClause884 (baseVal q)

theorem counterClause885 (q : Nat → Bool) : valuationOf q 331 = false ∨ valuationOf q 333 = true := by
  have hs : count333 q = (countLit q [156, 157, 158, 159, 160, 161, 162]) + (countLit q [163, 164, 165, 166, 167, 168, 169, 170]) := List.countP_append (p := literal q) (l₁ := [156, 157, 158, 159, 160, 161, 162]) (l₂ := [163, 164, 165, 166, 167, 168, 169, 170])
  have hm := merge_right (literal (valuationOf q) (331)) (literal (valuationOf q) (333)) (countLit q [156, 157, 158, 159, 160, 161, 162]) (countLit q [163, 164, 165, 166, 167, 168, 169, 170]) (count333 q) 1 (meaning331 q) (meaning333 q) hs
  change valuationOf q 331 = false ∨ valuationOf q 333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause885 (q : Snake 81) (h : Conditions q) : valuation q 331 = false ∨ valuation q 333 = true := counterClause885 (baseVal q)

theorem counterClause886 (q : Nat → Bool) : valuationOf q 317 = false ∨ valuationOf q 333 = true := by
  have hs : count333 q = (countLit q [156, 157, 158, 159, 160, 161, 162]) + (countLit q [163, 164, 165, 166, 167, 168, 169, 170]) := List.countP_append (p := literal q) (l₁ := [156, 157, 158, 159, 160, 161, 162]) (l₂ := [163, 164, 165, 166, 167, 168, 169, 170])
  have hm := merge_left (literal (valuationOf q) (317)) (literal (valuationOf q) (333)) (countLit q [156, 157, 158, 159, 160, 161, 162]) (countLit q [163, 164, 165, 166, 167, 168, 169, 170]) (count333 q) 1 (meaning317 q) (meaning333 q) hs
  change valuationOf q 317 = false ∨ valuationOf q 333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause886 (q : Snake 81) (h : Conditions q) : valuation q 317 = false ∨ valuation q 333 = true := counterClause886 (baseVal q)

theorem counterClause887 (q : Nat → Bool) : valuationOf q 317 = false ∨ valuationOf q 331 = false ∨ valuationOf q 334 = true := by
  have hs : count333 q = (countLit q [156, 157, 158, 159, 160, 161, 162]) + (countLit q [163, 164, 165, 166, 167, 168, 169, 170]) := List.countP_append (p := literal q) (l₁ := [156, 157, 158, 159, 160, 161, 162]) (l₂ := [163, 164, 165, 166, 167, 168, 169, 170])
  have hm := merge_two (literal (valuationOf q) (317)) (literal (valuationOf q) (331)) (literal (valuationOf q) (334)) (countLit q [156, 157, 158, 159, 160, 161, 162]) (countLit q [163, 164, 165, 166, 167, 168, 169, 170]) (count333 q) 1 1 (meaning317 q) (meaning331 q) (meaning334 q) hs
  change valuationOf q 317 = false ∨ valuationOf q 331 = false ∨ valuationOf q 334 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause887 (q : Snake 81) (h : Conditions q) : valuation q 317 = false ∨ valuation q 331 = false ∨ valuation q 334 = true := counterClause887 (baseVal q)

theorem counterClause888 (q : Nat → Bool) : valuationOf q 318 = false ∨ valuationOf q 334 = true := by
  have hs : count333 q = (countLit q [156, 157, 158, 159, 160, 161, 162]) + (countLit q [163, 164, 165, 166, 167, 168, 169, 170]) := List.countP_append (p := literal q) (l₁ := [156, 157, 158, 159, 160, 161, 162]) (l₂ := [163, 164, 165, 166, 167, 168, 169, 170])
  have hm := merge_left (literal (valuationOf q) (318)) (literal (valuationOf q) (334)) (countLit q [156, 157, 158, 159, 160, 161, 162]) (countLit q [163, 164, 165, 166, 167, 168, 169, 170]) (count333 q) 2 (meaning318 q) (meaning334 q) hs
  change valuationOf q 318 = false ∨ valuationOf q 334 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause888 (q : Snake 81) (h : Conditions q) : valuation q 318 = false ∨ valuation q 334 = true := counterClause888 (baseVal q)

theorem counterClause889 (q : Nat → Bool) : valuationOf q 174 = false ∨ valuationOf q 337 = true := by
  have hs : count337 q = (countLit q [173]) + (countLit q [174]) := List.countP_append (p := literal q) (l₁ := [173]) (l₂ := [174])
  have hm := merge_right (literal (valuationOf q) (174)) (literal (valuationOf q) (337)) (countLit q [173]) (countLit q [174]) (count337 q) 1 (meaning174 q) (meaning337 q) hs
  change valuationOf q 174 = false ∨ valuationOf q 337 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause889 (q : Snake 81) (h : Conditions q) : valuation q 174 = false ∨ valuation q 337 = true := counterClause889 (baseVal q)

theorem counterClause890 (q : Nat → Bool) : valuationOf q 337 = false ∨ valuationOf q 339 = true := by
  have hs : count339 q = (countLit q [171, 172]) + (countLit q [173, 174]) := List.countP_append (p := literal q) (l₁ := [171, 172]) (l₂ := [173, 174])
  have hm := merge_right (literal (valuationOf q) (337)) (literal (valuationOf q) (339)) (countLit q [171, 172]) (countLit q [173, 174]) (count339 q) 1 (meaning337 q) (meaning339 q) hs
  change valuationOf q 337 = false ∨ valuationOf q 339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause890 (q : Snake 81) (h : Conditions q) : valuation q 337 = false ∨ valuation q 339 = true := counterClause890 (baseVal q)

theorem counterClause891 (q : Nat → Bool) : valuationOf q 176 = false ∨ valuationOf q 341 = true := by
  have hs : count341 q = (countLit q [175]) + (countLit q [176]) := List.countP_append (p := literal q) (l₁ := [175]) (l₂ := [176])
  have hm := merge_right (literal (valuationOf q) (176)) (literal (valuationOf q) (341)) (countLit q [175]) (countLit q [176]) (count341 q) 1 (meaning176 q) (meaning341 q) hs
  change valuationOf q 176 = false ∨ valuationOf q 341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause891 (q : Snake 81) (h : Conditions q) : valuation q 176 = false ∨ valuation q 341 = true := counterClause891 (baseVal q)

theorem counterClause892 (q : Nat → Bool) : valuationOf q 341 = false ∨ valuationOf q 345 = true := by
  have hs : count345 q = (countLit q [175, 176]) + (countLit q [177, 178]) := List.countP_append (p := literal q) (l₁ := [175, 176]) (l₂ := [177, 178])
  have hm := merge_left (literal (valuationOf q) (341)) (literal (valuationOf q) (345)) (countLit q [175, 176]) (countLit q [177, 178]) (count345 q) 1 (meaning341 q) (meaning345 q) hs
  change valuationOf q 341 = false ∨ valuationOf q 345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause892 (q : Snake 81) (h : Conditions q) : valuation q 341 = false ∨ valuation q 345 = true := counterClause892 (baseVal q)

theorem counterClause893 (q : Nat → Bool) : valuationOf q 345 = false ∨ valuationOf q 347 = true := by
  have hs : count347 q = (countLit q [171, 172, 173, 174]) + (countLit q [175, 176, 177, 178]) := List.countP_append (p := literal q) (l₁ := [171, 172, 173, 174]) (l₂ := [175, 176, 177, 178])
  have hm := merge_right (literal (valuationOf q) (345)) (literal (valuationOf q) (347)) (countLit q [171, 172, 173, 174]) (countLit q [175, 176, 177, 178]) (count347 q) 1 (meaning345 q) (meaning347 q) hs
  change valuationOf q 345 = false ∨ valuationOf q 347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause893 (q : Snake 81) (h : Conditions q) : valuation q 345 = false ∨ valuation q 347 = true := counterClause893 (baseVal q)

theorem counterClause894 (q : Nat → Bool) : valuationOf q 339 = false ∨ valuationOf q 347 = true := by
  have hs : count347 q = (countLit q [171, 172, 173, 174]) + (countLit q [175, 176, 177, 178]) := List.countP_append (p := literal q) (l₁ := [171, 172, 173, 174]) (l₂ := [175, 176, 177, 178])
  have hm := merge_left (literal (valuationOf q) (339)) (literal (valuationOf q) (347)) (countLit q [171, 172, 173, 174]) (countLit q [175, 176, 177, 178]) (count347 q) 1 (meaning339 q) (meaning347 q) hs
  change valuationOf q 339 = false ∨ valuationOf q 347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause894 (q : Snake 81) (h : Conditions q) : valuation q 339 = false ∨ valuation q 347 = true := counterClause894 (baseVal q)

theorem counterClause895 (q : Nat → Bool) : valuationOf q 339 = false ∨ valuationOf q 345 = false ∨ valuationOf q 348 = true := by
  have hs : count347 q = (countLit q [171, 172, 173, 174]) + (countLit q [175, 176, 177, 178]) := List.countP_append (p := literal q) (l₁ := [171, 172, 173, 174]) (l₂ := [175, 176, 177, 178])
  have hm := merge_two (literal (valuationOf q) (339)) (literal (valuationOf q) (345)) (literal (valuationOf q) (348)) (countLit q [171, 172, 173, 174]) (countLit q [175, 176, 177, 178]) (count347 q) 1 1 (meaning339 q) (meaning345 q) (meaning348 q) hs
  change valuationOf q 339 = false ∨ valuationOf q 345 = false ∨ valuationOf q 348 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause895 (q : Snake 81) (h : Conditions q) : valuation q 339 = false ∨ valuation q 345 = false ∨ valuation q 348 = true := counterClause895 (baseVal q)

theorem counterClause896 (q : Nat → Bool) : valuationOf q 179 = false ∨ valuationOf q 349 = true := by
  have hs : count349 q = (countLit q [179]) + (countLit q [180]) := List.countP_append (p := literal q) (l₁ := [179]) (l₂ := [180])
  have hm := merge_left (literal (valuationOf q) (179)) (literal (valuationOf q) (349)) (countLit q [179]) (countLit q [180]) (count349 q) 1 (meaning179 q) (meaning349 q) hs
  change valuationOf q 179 = false ∨ valuationOf q 349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause896 (q : Snake 81) (h : Conditions q) : valuation q 179 = false ∨ valuation q 349 = true := counterClause896 (baseVal q)

theorem block27 (q : Snake 81) (h : Conditions q) : B112E020.Block27 (valuation q) :=
  ⟨clause865 q h, clause866 q h, clause867 q h, clause868 q h, clause869 q h, clause870 q h, clause871 q h, clause872 q h, clause873 q h, clause874 q h, clause875 q h, clause876 q h, clause877 q h, clause878 q h, clause879 q h, clause880 q h, clause881 q h, clause882 q h, clause883 q h, clause884 q h, clause885 q h, clause886 q h, clause887 q h, clause888 q h, clause889 q h, clause890 q h, clause891 q h, clause892 q h, clause893 q h, clause894 q h, clause895 q h, clause896 q h⟩

end
end Snake9.Regrowth.E112020
