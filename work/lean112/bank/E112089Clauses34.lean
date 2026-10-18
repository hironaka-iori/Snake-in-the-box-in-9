import E112089Semantics
import B112E089Inputs
namespace Snake9.Regrowth.E112089
noncomputable section
local instance blockDec34 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1089 (q : Nat → Bool) : valuationOf q 304 = false ∨ valuationOf q 306 = true := by
  have hs : count305 q = (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139]) + (countLit q [140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139]) (l₂ := [140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154])
  have hm := merge_right (literal (valuationOf q) (304)) (literal (valuationOf q) (306)) (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139]) (countLit q [140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154]) (count305 q) 2 (meaning304 q) (meaning306 q) hs
  change valuationOf q 304 = false ∨ valuationOf q 306 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1089 (q : Snake 81) (h : Conditions q) : valuation q 304 = false ∨ valuation q 306 = true := counterClause1089 (baseVal q)

theorem counterClause1090 (q : Nat → Bool) : valuationOf q 275 = false ∨ valuationOf q 305 = true := by
  have hs : count305 q = (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139]) + (countLit q [140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139]) (l₂ := [140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154])
  have hm := merge_left (literal (valuationOf q) (275)) (literal (valuationOf q) (305)) (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139]) (countLit q [140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154]) (count305 q) 1 (meaning275 q) (meaning305 q) hs
  change valuationOf q 275 = false ∨ valuationOf q 305 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1090 (q : Snake 81) (h : Conditions q) : valuation q 275 = false ∨ valuation q 305 = true := counterClause1090 (baseVal q)

theorem counterClause1091 (q : Nat → Bool) : valuationOf q 275 = false ∨ valuationOf q 303 = false ∨ valuationOf q 306 = true := by
  have hs : count305 q = (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139]) + (countLit q [140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139]) (l₂ := [140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154])
  have hm := merge_two (literal (valuationOf q) (275)) (literal (valuationOf q) (303)) (literal (valuationOf q) (306)) (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139]) (countLit q [140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154]) (count305 q) 1 1 (meaning275 q) (meaning303 q) (meaning306 q) hs
  change valuationOf q 275 = false ∨ valuationOf q 303 = false ∨ valuationOf q 306 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1091 (q : Snake 81) (h : Conditions q) : valuation q 275 = false ∨ valuation q 303 = false ∨ valuation q 306 = true := counterClause1091 (baseVal q)

theorem counterClause1092 (q : Nat → Bool) : valuationOf q 276 = false ∨ valuationOf q 306 = true := by
  have hs : count305 q = (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139]) + (countLit q [140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139]) (l₂ := [140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154])
  have hm := merge_left (literal (valuationOf q) (276)) (literal (valuationOf q) (306)) (countLit q [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139]) (countLit q [140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154]) (count305 q) 2 (meaning276 q) (meaning306 q) hs
  change valuationOf q 276 = false ∨ valuationOf q 306 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1092 (q : Snake 81) (h : Conditions q) : valuation q 276 = false ∨ valuation q 306 = true := counterClause1092 (baseVal q)

theorem counterClause1093 (q : Nat → Bool) : valuationOf q 156 = false ∨ valuationOf q 307 = true := by
  have hs : count307 q = (countLit q [156]) + (countLit q [157]) := List.countP_append (p := literal q) (l₁ := [156]) (l₂ := [157])
  have hm := merge_left (literal (valuationOf q) (156)) (literal (valuationOf q) (307)) (countLit q [156]) (countLit q [157]) (count307 q) 1 (meaning156 q) (meaning307 q) hs
  change valuationOf q 156 = false ∨ valuationOf q 307 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1093 (q : Snake 81) (h : Conditions q) : valuation q 156 = false ∨ valuation q 307 = true := counterClause1093 (baseVal q)

theorem counterClause1094 (q : Nat → Bool) : valuationOf q 307 = false ∨ valuationOf q 309 = true := by
  have hs : count309 q = (countLit q [155]) + (countLit q [156, 157]) := List.countP_append (p := literal q) (l₁ := [155]) (l₂ := [156, 157])
  have hm := merge_right (literal (valuationOf q) (307)) (literal (valuationOf q) (309)) (countLit q [155]) (countLit q [156, 157]) (count309 q) 1 (meaning307 q) (meaning309 q) hs
  change valuationOf q 307 = false ∨ valuationOf q 309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1094 (q : Snake 81) (h : Conditions q) : valuation q 307 = false ∨ valuation q 309 = true := counterClause1094 (baseVal q)

theorem counterClause1095 (q : Nat → Bool) : valuationOf q 155 = false ∨ valuationOf q 309 = true := by
  have hs : count309 q = (countLit q [155]) + (countLit q [156, 157]) := List.countP_append (p := literal q) (l₁ := [155]) (l₂ := [156, 157])
  have hm := merge_left (literal (valuationOf q) (155)) (literal (valuationOf q) (309)) (countLit q [155]) (countLit q [156, 157]) (count309 q) 1 (meaning155 q) (meaning309 q) hs
  change valuationOf q 155 = false ∨ valuationOf q 309 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1095 (q : Snake 81) (h : Conditions q) : valuation q 155 = false ∨ valuation q 309 = true := counterClause1095 (baseVal q)

theorem counterClause1096 (q : Nat → Bool) : valuationOf q 155 = false ∨ valuationOf q 307 = false ∨ valuationOf q 310 = true := by
  have hs : count309 q = (countLit q [155]) + (countLit q [156, 157]) := List.countP_append (p := literal q) (l₁ := [155]) (l₂ := [156, 157])
  have hm := merge_two (literal (valuationOf q) (155)) (literal (valuationOf q) (307)) (literal (valuationOf q) (310)) (countLit q [155]) (countLit q [156, 157]) (count309 q) 1 1 (meaning155 q) (meaning307 q) (meaning310 q) hs
  change valuationOf q 155 = false ∨ valuationOf q 307 = false ∨ valuationOf q 310 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1096 (q : Snake 81) (h : Conditions q) : valuation q 155 = false ∨ valuation q 307 = false ∨ valuation q 310 = true := counterClause1096 (baseVal q)

theorem counterClause1097 (q : Nat → Bool) : valuationOf q 158 = false ∨ valuationOf q 311 = true := by
  have hs : count311 q = (countLit q [158]) + (countLit q [159]) := List.countP_append (p := literal q) (l₁ := [158]) (l₂ := [159])
  have hm := merge_left (literal (valuationOf q) (158)) (literal (valuationOf q) (311)) (countLit q [158]) (countLit q [159]) (count311 q) 1 (meaning158 q) (meaning311 q) hs
  change valuationOf q 158 = false ∨ valuationOf q 311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1097 (q : Snake 81) (h : Conditions q) : valuation q 158 = false ∨ valuation q 311 = true := counterClause1097 (baseVal q)

theorem counterClause1098 (q : Nat → Bool) : valuationOf q 311 = false ∨ valuationOf q 315 = true := by
  have hs : count315 q = (countLit q [158, 159]) + (countLit q [160, 161]) := List.countP_append (p := literal q) (l₁ := [158, 159]) (l₂ := [160, 161])
  have hm := merge_left (literal (valuationOf q) (311)) (literal (valuationOf q) (315)) (countLit q [158, 159]) (countLit q [160, 161]) (count315 q) 1 (meaning311 q) (meaning315 q) hs
  change valuationOf q 311 = false ∨ valuationOf q 315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1098 (q : Snake 81) (h : Conditions q) : valuation q 311 = false ∨ valuation q 315 = true := counterClause1098 (baseVal q)

theorem counterClause1099 (q : Nat → Bool) : valuationOf q 315 = false ∨ valuationOf q 317 = true := by
  have hs : count317 q = (countLit q [155, 156, 157]) + (countLit q [158, 159, 160, 161]) := List.countP_append (p := literal q) (l₁ := [155, 156, 157]) (l₂ := [158, 159, 160, 161])
  have hm := merge_right (literal (valuationOf q) (315)) (literal (valuationOf q) (317)) (countLit q [155, 156, 157]) (countLit q [158, 159, 160, 161]) (count317 q) 1 (meaning315 q) (meaning317 q) hs
  change valuationOf q 315 = false ∨ valuationOf q 317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1099 (q : Snake 81) (h : Conditions q) : valuation q 315 = false ∨ valuation q 317 = true := counterClause1099 (baseVal q)

theorem counterClause1100 (q : Nat → Bool) : valuationOf q 309 = false ∨ valuationOf q 317 = true := by
  have hs : count317 q = (countLit q [155, 156, 157]) + (countLit q [158, 159, 160, 161]) := List.countP_append (p := literal q) (l₁ := [155, 156, 157]) (l₂ := [158, 159, 160, 161])
  have hm := merge_left (literal (valuationOf q) (309)) (literal (valuationOf q) (317)) (countLit q [155, 156, 157]) (countLit q [158, 159, 160, 161]) (count317 q) 1 (meaning309 q) (meaning317 q) hs
  change valuationOf q 309 = false ∨ valuationOf q 317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1100 (q : Snake 81) (h : Conditions q) : valuation q 309 = false ∨ valuation q 317 = true := counterClause1100 (baseVal q)

theorem counterClause1101 (q : Nat → Bool) : valuationOf q 309 = false ∨ valuationOf q 315 = false ∨ valuationOf q 318 = true := by
  have hs : count317 q = (countLit q [155, 156, 157]) + (countLit q [158, 159, 160, 161]) := List.countP_append (p := literal q) (l₁ := [155, 156, 157]) (l₂ := [158, 159, 160, 161])
  have hm := merge_two (literal (valuationOf q) (309)) (literal (valuationOf q) (315)) (literal (valuationOf q) (318)) (countLit q [155, 156, 157]) (countLit q [158, 159, 160, 161]) (count317 q) 1 1 (meaning309 q) (meaning315 q) (meaning318 q) hs
  change valuationOf q 309 = false ∨ valuationOf q 315 = false ∨ valuationOf q 318 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1101 (q : Snake 81) (h : Conditions q) : valuation q 309 = false ∨ valuation q 315 = false ∨ valuation q 318 = true := counterClause1101 (baseVal q)

theorem counterClause1102 (q : Nat → Bool) : valuationOf q 310 = false ∨ valuationOf q 318 = true := by
  have hs : count317 q = (countLit q [155, 156, 157]) + (countLit q [158, 159, 160, 161]) := List.countP_append (p := literal q) (l₁ := [155, 156, 157]) (l₂ := [158, 159, 160, 161])
  have hm := merge_left (literal (valuationOf q) (310)) (literal (valuationOf q) (318)) (countLit q [155, 156, 157]) (countLit q [158, 159, 160, 161]) (count317 q) 2 (meaning310 q) (meaning318 q) hs
  change valuationOf q 310 = false ∨ valuationOf q 318 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1102 (q : Snake 81) (h : Conditions q) : valuation q 310 = false ∨ valuation q 318 = true := counterClause1102 (baseVal q)

theorem counterClause1103 (q : Nat → Bool) : valuationOf q 163 = false ∨ valuationOf q 319 = true := by
  have hs : count319 q = (countLit q [162]) + (countLit q [163]) := List.countP_append (p := literal q) (l₁ := [162]) (l₂ := [163])
  have hm := merge_right (literal (valuationOf q) (163)) (literal (valuationOf q) (319)) (countLit q [162]) (countLit q [163]) (count319 q) 1 (meaning163 q) (meaning319 q) hs
  change valuationOf q 163 = false ∨ valuationOf q 319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1103 (q : Snake 81) (h : Conditions q) : valuation q 163 = false ∨ valuation q 319 = true := counterClause1103 (baseVal q)

theorem counterClause1104 (q : Nat → Bool) : valuationOf q 165 = false ∨ valuationOf q 321 = true := by
  have hs : count321 q = (countLit q [164]) + (countLit q [165]) := List.countP_append (p := literal q) (l₁ := [164]) (l₂ := [165])
  have hm := merge_right (literal (valuationOf q) (165)) (literal (valuationOf q) (321)) (countLit q [164]) (countLit q [165]) (count321 q) 1 (meaning165 q) (meaning321 q) hs
  change valuationOf q 165 = false ∨ valuationOf q 321 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1104 (q : Snake 81) (h : Conditions q) : valuation q 165 = false ∨ valuation q 321 = true := counterClause1104 (baseVal q)

theorem counterClause1105 (q : Nat → Bool) : valuationOf q 321 = false ∨ valuationOf q 323 = true := by
  have hs : count323 q = (countLit q [162, 163]) + (countLit q [164, 165]) := List.countP_append (p := literal q) (l₁ := [162, 163]) (l₂ := [164, 165])
  have hm := merge_right (literal (valuationOf q) (321)) (literal (valuationOf q) (323)) (countLit q [162, 163]) (countLit q [164, 165]) (count323 q) 1 (meaning321 q) (meaning323 q) hs
  change valuationOf q 321 = false ∨ valuationOf q 323 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1105 (q : Snake 81) (h : Conditions q) : valuation q 321 = false ∨ valuation q 323 = true := counterClause1105 (baseVal q)

theorem counterClause1106 (q : Nat → Bool) : valuationOf q 319 = false ∨ valuationOf q 323 = true := by
  have hs : count323 q = (countLit q [162, 163]) + (countLit q [164, 165]) := List.countP_append (p := literal q) (l₁ := [162, 163]) (l₂ := [164, 165])
  have hm := merge_left (literal (valuationOf q) (319)) (literal (valuationOf q) (323)) (countLit q [162, 163]) (countLit q [164, 165]) (count323 q) 1 (meaning319 q) (meaning323 q) hs
  change valuationOf q 319 = false ∨ valuationOf q 323 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1106 (q : Snake 81) (h : Conditions q) : valuation q 319 = false ∨ valuation q 323 = true := counterClause1106 (baseVal q)

theorem counterClause1107 (q : Nat → Bool) : valuationOf q 319 = false ∨ valuationOf q 321 = false ∨ valuationOf q 324 = true := by
  have hs : count323 q = (countLit q [162, 163]) + (countLit q [164, 165]) := List.countP_append (p := literal q) (l₁ := [162, 163]) (l₂ := [164, 165])
  have hm := merge_two (literal (valuationOf q) (319)) (literal (valuationOf q) (321)) (literal (valuationOf q) (324)) (countLit q [162, 163]) (countLit q [164, 165]) (count323 q) 1 1 (meaning319 q) (meaning321 q) (meaning324 q) hs
  change valuationOf q 319 = false ∨ valuationOf q 321 = false ∨ valuationOf q 324 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1107 (q : Snake 81) (h : Conditions q) : valuation q 319 = false ∨ valuation q 321 = false ∨ valuation q 324 = true := counterClause1107 (baseVal q)

theorem counterClause1108 (q : Nat → Bool) : valuationOf q 166 = false ∨ valuationOf q 325 = true := by
  have hs : count325 q = (countLit q [166]) + (countLit q [167]) := List.countP_append (p := literal q) (l₁ := [166]) (l₂ := [167])
  have hm := merge_left (literal (valuationOf q) (166)) (literal (valuationOf q) (325)) (countLit q [166]) (countLit q [167]) (count325 q) 1 (meaning166 q) (meaning325 q) hs
  change valuationOf q 166 = false ∨ valuationOf q 325 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1108 (q : Snake 81) (h : Conditions q) : valuation q 166 = false ∨ valuation q 325 = true := counterClause1108 (baseVal q)

theorem counterClause1109 (q : Nat → Bool) : valuationOf q 169 = false ∨ valuationOf q 327 = true := by
  have hs : count327 q = (countLit q [168]) + (countLit q [169]) := List.countP_append (p := literal q) (l₁ := [168]) (l₂ := [169])
  have hm := merge_right (literal (valuationOf q) (169)) (literal (valuationOf q) (327)) (countLit q [168]) (countLit q [169]) (count327 q) 1 (meaning169 q) (meaning327 q) hs
  change valuationOf q 169 = false ∨ valuationOf q 327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1109 (q : Snake 81) (h : Conditions q) : valuation q 169 = false ∨ valuation q 327 = true := counterClause1109 (baseVal q)

theorem counterClause1110 (q : Nat → Bool) : valuationOf q 168 = false ∨ valuationOf q 327 = true := by
  have hs : count327 q = (countLit q [168]) + (countLit q [169]) := List.countP_append (p := literal q) (l₁ := [168]) (l₂ := [169])
  have hm := merge_left (literal (valuationOf q) (168)) (literal (valuationOf q) (327)) (countLit q [168]) (countLit q [169]) (count327 q) 1 (meaning168 q) (meaning327 q) hs
  change valuationOf q 168 = false ∨ valuationOf q 327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1110 (q : Snake 81) (h : Conditions q) : valuation q 168 = false ∨ valuation q 327 = true := counterClause1110 (baseVal q)

theorem counterClause1111 (q : Nat → Bool) : valuationOf q 168 = false ∨ valuationOf q 169 = false ∨ valuationOf q 328 = true := by
  have hs : count327 q = (countLit q [168]) + (countLit q [169]) := List.countP_append (p := literal q) (l₁ := [168]) (l₂ := [169])
  have hm := merge_two (literal (valuationOf q) (168)) (literal (valuationOf q) (169)) (literal (valuationOf q) (328)) (countLit q [168]) (countLit q [169]) (count327 q) 1 1 (meaning168 q) (meaning169 q) (meaning328 q) hs
  change valuationOf q 168 = false ∨ valuationOf q 169 = false ∨ valuationOf q 328 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1111 (q : Snake 81) (h : Conditions q) : valuation q 168 = false ∨ valuation q 169 = false ∨ valuation q 328 = true := counterClause1111 (baseVal q)

theorem counterClause1112 (q : Nat → Bool) : valuationOf q 327 = false ∨ valuationOf q 329 = true := by
  have hs : count329 q = (countLit q [166, 167]) + (countLit q [168, 169]) := List.countP_append (p := literal q) (l₁ := [166, 167]) (l₂ := [168, 169])
  have hm := merge_right (literal (valuationOf q) (327)) (literal (valuationOf q) (329)) (countLit q [166, 167]) (countLit q [168, 169]) (count329 q) 1 (meaning327 q) (meaning329 q) hs
  change valuationOf q 327 = false ∨ valuationOf q 329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1112 (q : Snake 81) (h : Conditions q) : valuation q 327 = false ∨ valuation q 329 = true := counterClause1112 (baseVal q)

theorem counterClause1113 (q : Nat → Bool) : valuationOf q 328 = false ∨ valuationOf q 330 = true := by
  have hs : count329 q = (countLit q [166, 167]) + (countLit q [168, 169]) := List.countP_append (p := literal q) (l₁ := [166, 167]) (l₂ := [168, 169])
  have hm := merge_right (literal (valuationOf q) (328)) (literal (valuationOf q) (330)) (countLit q [166, 167]) (countLit q [168, 169]) (count329 q) 2 (meaning328 q) (meaning330 q) hs
  change valuationOf q 328 = false ∨ valuationOf q 330 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1113 (q : Snake 81) (h : Conditions q) : valuation q 328 = false ∨ valuation q 330 = true := counterClause1113 (baseVal q)

theorem counterClause1114 (q : Nat → Bool) : valuationOf q 325 = false ∨ valuationOf q 329 = true := by
  have hs : count329 q = (countLit q [166, 167]) + (countLit q [168, 169]) := List.countP_append (p := literal q) (l₁ := [166, 167]) (l₂ := [168, 169])
  have hm := merge_left (literal (valuationOf q) (325)) (literal (valuationOf q) (329)) (countLit q [166, 167]) (countLit q [168, 169]) (count329 q) 1 (meaning325 q) (meaning329 q) hs
  change valuationOf q 325 = false ∨ valuationOf q 329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1114 (q : Snake 81) (h : Conditions q) : valuation q 325 = false ∨ valuation q 329 = true := counterClause1114 (baseVal q)

theorem counterClause1115 (q : Nat → Bool) : valuationOf q 325 = false ∨ valuationOf q 327 = false ∨ valuationOf q 330 = true := by
  have hs : count329 q = (countLit q [166, 167]) + (countLit q [168, 169]) := List.countP_append (p := literal q) (l₁ := [166, 167]) (l₂ := [168, 169])
  have hm := merge_two (literal (valuationOf q) (325)) (literal (valuationOf q) (327)) (literal (valuationOf q) (330)) (countLit q [166, 167]) (countLit q [168, 169]) (count329 q) 1 1 (meaning325 q) (meaning327 q) (meaning330 q) hs
  change valuationOf q 325 = false ∨ valuationOf q 327 = false ∨ valuationOf q 330 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1115 (q : Snake 81) (h : Conditions q) : valuation q 325 = false ∨ valuation q 327 = false ∨ valuation q 330 = true := counterClause1115 (baseVal q)

theorem counterClause1116 (q : Nat → Bool) : valuationOf q 329 = false ∨ valuationOf q 331 = true := by
  have hs : count331 q = (countLit q [162, 163, 164, 165]) + (countLit q [166, 167, 168, 169]) := List.countP_append (p := literal q) (l₁ := [162, 163, 164, 165]) (l₂ := [166, 167, 168, 169])
  have hm := merge_right (literal (valuationOf q) (329)) (literal (valuationOf q) (331)) (countLit q [162, 163, 164, 165]) (countLit q [166, 167, 168, 169]) (count331 q) 1 (meaning329 q) (meaning331 q) hs
  change valuationOf q 329 = false ∨ valuationOf q 331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1116 (q : Snake 81) (h : Conditions q) : valuation q 329 = false ∨ valuation q 331 = true := counterClause1116 (baseVal q)

theorem counterClause1117 (q : Nat → Bool) : valuationOf q 330 = false ∨ valuationOf q 332 = true := by
  have hs : count331 q = (countLit q [162, 163, 164, 165]) + (countLit q [166, 167, 168, 169]) := List.countP_append (p := literal q) (l₁ := [162, 163, 164, 165]) (l₂ := [166, 167, 168, 169])
  have hm := merge_right (literal (valuationOf q) (330)) (literal (valuationOf q) (332)) (countLit q [162, 163, 164, 165]) (countLit q [166, 167, 168, 169]) (count331 q) 2 (meaning330 q) (meaning332 q) hs
  change valuationOf q 330 = false ∨ valuationOf q 332 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1117 (q : Snake 81) (h : Conditions q) : valuation q 330 = false ∨ valuation q 332 = true := counterClause1117 (baseVal q)

theorem counterClause1118 (q : Nat → Bool) : valuationOf q 323 = false ∨ valuationOf q 331 = true := by
  have hs : count331 q = (countLit q [162, 163, 164, 165]) + (countLit q [166, 167, 168, 169]) := List.countP_append (p := literal q) (l₁ := [162, 163, 164, 165]) (l₂ := [166, 167, 168, 169])
  have hm := merge_left (literal (valuationOf q) (323)) (literal (valuationOf q) (331)) (countLit q [162, 163, 164, 165]) (countLit q [166, 167, 168, 169]) (count331 q) 1 (meaning323 q) (meaning331 q) hs
  change valuationOf q 323 = false ∨ valuationOf q 331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1118 (q : Snake 81) (h : Conditions q) : valuation q 323 = false ∨ valuation q 331 = true := counterClause1118 (baseVal q)

theorem counterClause1119 (q : Nat → Bool) : valuationOf q 323 = false ∨ valuationOf q 329 = false ∨ valuationOf q 332 = true := by
  have hs : count331 q = (countLit q [162, 163, 164, 165]) + (countLit q [166, 167, 168, 169]) := List.countP_append (p := literal q) (l₁ := [162, 163, 164, 165]) (l₂ := [166, 167, 168, 169])
  have hm := merge_two (literal (valuationOf q) (323)) (literal (valuationOf q) (329)) (literal (valuationOf q) (332)) (countLit q [162, 163, 164, 165]) (countLit q [166, 167, 168, 169]) (count331 q) 1 1 (meaning323 q) (meaning329 q) (meaning332 q) hs
  change valuationOf q 323 = false ∨ valuationOf q 329 = false ∨ valuationOf q 332 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1119 (q : Snake 81) (h : Conditions q) : valuation q 323 = false ∨ valuation q 329 = false ∨ valuation q 332 = true := counterClause1119 (baseVal q)

theorem counterClause1120 (q : Nat → Bool) : valuationOf q 324 = false ∨ valuationOf q 332 = true := by
  have hs : count331 q = (countLit q [162, 163, 164, 165]) + (countLit q [166, 167, 168, 169]) := List.countP_append (p := literal q) (l₁ := [162, 163, 164, 165]) (l₂ := [166, 167, 168, 169])
  have hm := merge_left (literal (valuationOf q) (324)) (literal (valuationOf q) (332)) (countLit q [162, 163, 164, 165]) (countLit q [166, 167, 168, 169]) (count331 q) 2 (meaning324 q) (meaning332 q) hs
  change valuationOf q 324 = false ∨ valuationOf q 332 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1120 (q : Snake 81) (h : Conditions q) : valuation q 324 = false ∨ valuation q 332 = true := counterClause1120 (baseVal q)

theorem block34 (q : Snake 81) (h : Conditions q) : B112E089.Block34 (valuation q) :=
  ⟨clause1089 q h, clause1090 q h, clause1091 q h, clause1092 q h, clause1093 q h, clause1094 q h, clause1095 q h, clause1096 q h, clause1097 q h, clause1098 q h, clause1099 q h, clause1100 q h, clause1101 q h, clause1102 q h, clause1103 q h, clause1104 q h, clause1105 q h, clause1106 q h, clause1107 q h, clause1108 q h, clause1109 q h, clause1110 q h, clause1111 q h, clause1112 q h, clause1113 q h, clause1114 q h, clause1115 q h, clause1116 q h, clause1117 q h, clause1118 q h, clause1119 q h, clause1120 q h⟩

end
end Snake9.Regrowth.E112089
