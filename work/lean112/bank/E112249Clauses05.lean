import E112249Semantics
import B112E249Inputs
namespace Snake9.Regrowth.E112249
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause161 (q : Nat → Bool) : valuationOf q 310 = false ∨ valuationOf q 312 = true := by
  have hs : count311 q = (countLit q [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]) + (countLit q [146, 147, 148, 149, 150, 152, 153, 154, 155, 156, 157, 158, 159]) := List.countP_append (p := literal q) (l₁ := [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]) (l₂ := [146, 147, 148, 149, 150, 152, 153, 154, 155, 156, 157, 158, 159])
  have hm := merge_right (literal (valuationOf q) (310)) (literal (valuationOf q) (312)) (countLit q [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]) (countLit q [146, 147, 148, 149, 150, 152, 153, 154, 155, 156, 157, 158, 159]) (count311 q) 2 (meaning310 q) (meaning312 q) hs
  change valuationOf q 310 = false ∨ valuationOf q 312 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 310 = false ∨ valuation q 312 = true := counterClause161 (baseVal q)

theorem counterClause162 (q : Nat → Bool) : valuationOf q 285 = false ∨ valuationOf q 311 = true := by
  have hs : count311 q = (countLit q [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]) + (countLit q [146, 147, 148, 149, 150, 152, 153, 154, 155, 156, 157, 158, 159]) := List.countP_append (p := literal q) (l₁ := [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]) (l₂ := [146, 147, 148, 149, 150, 152, 153, 154, 155, 156, 157, 158, 159])
  have hm := merge_left (literal (valuationOf q) (285)) (literal (valuationOf q) (311)) (countLit q [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]) (countLit q [146, 147, 148, 149, 150, 152, 153, 154, 155, 156, 157, 158, 159]) (count311 q) 1 (meaning285 q) (meaning311 q) hs
  change valuationOf q 285 = false ∨ valuationOf q 311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 285 = false ∨ valuation q 311 = true := counterClause162 (baseVal q)

theorem counterClause163 (q : Nat → Bool) : valuationOf q 285 = false ∨ valuationOf q 309 = false ∨ valuationOf q 312 = true := by
  have hs : count311 q = (countLit q [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]) + (countLit q [146, 147, 148, 149, 150, 152, 153, 154, 155, 156, 157, 158, 159]) := List.countP_append (p := literal q) (l₁ := [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]) (l₂ := [146, 147, 148, 149, 150, 152, 153, 154, 155, 156, 157, 158, 159])
  have hm := merge_two (literal (valuationOf q) (285)) (literal (valuationOf q) (309)) (literal (valuationOf q) (312)) (countLit q [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]) (countLit q [146, 147, 148, 149, 150, 152, 153, 154, 155, 156, 157, 158, 159]) (count311 q) 1 1 (meaning285 q) (meaning309 q) (meaning312 q) hs
  change valuationOf q 285 = false ∨ valuationOf q 309 = false ∨ valuationOf q 312 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 285 = false ∨ valuation q 309 = false ∨ valuation q 312 = true := counterClause163 (baseVal q)

theorem counterClause164 (q : Nat → Bool) : valuationOf q 286 = false ∨ valuationOf q 312 = true := by
  have hs : count311 q = (countLit q [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]) + (countLit q [146, 147, 148, 149, 150, 152, 153, 154, 155, 156, 157, 158, 159]) := List.countP_append (p := literal q) (l₁ := [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]) (l₂ := [146, 147, 148, 149, 150, 152, 153, 154, 155, 156, 157, 158, 159])
  have hm := merge_left (literal (valuationOf q) (286)) (literal (valuationOf q) (312)) (countLit q [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]) (countLit q [146, 147, 148, 149, 150, 152, 153, 154, 155, 156, 157, 158, 159]) (count311 q) 2 (meaning286 q) (meaning312 q) hs
  change valuationOf q 286 = false ∨ valuationOf q 312 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 286 = false ∨ valuation q 312 = true := counterClause164 (baseVal q)

theorem counterClause165 (q : Nat → Bool) : valuationOf q 311 = false ∨ valuationOf q 313 = true := by
  have hs : count313 q = (countLit q [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) + (countLit q [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 152, 153, 154, 155, 156, 157, 158, 159]) := List.countP_append (p := literal q) (l₁ := [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) (l₂ := [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 152, 153, 154, 155, 156, 157, 158, 159])
  have hm := merge_right (literal (valuationOf q) (311)) (literal (valuationOf q) (313)) (countLit q [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) (countLit q [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 152, 153, 154, 155, 156, 157, 158, 159]) (count313 q) 1 (meaning311 q) (meaning313 q) hs
  change valuationOf q 311 = false ∨ valuationOf q 313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 311 = false ∨ valuation q 313 = true := counterClause165 (baseVal q)

theorem counterClause166 (q : Nat → Bool) : valuationOf q 312 = false ∨ valuationOf q 314 = true := by
  have hs : count313 q = (countLit q [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) + (countLit q [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 152, 153, 154, 155, 156, 157, 158, 159]) := List.countP_append (p := literal q) (l₁ := [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) (l₂ := [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 152, 153, 154, 155, 156, 157, 158, 159])
  have hm := merge_right (literal (valuationOf q) (312)) (literal (valuationOf q) (314)) (countLit q [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) (countLit q [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 152, 153, 154, 155, 156, 157, 158, 159]) (count313 q) 2 (meaning312 q) (meaning314 q) hs
  change valuationOf q 312 = false ∨ valuationOf q 314 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 312 = false ∨ valuation q 314 = true := counterClause166 (baseVal q)

theorem counterClause167 (q : Nat → Bool) : valuationOf q 261 = false ∨ valuationOf q 313 = true := by
  have hs : count313 q = (countLit q [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) + (countLit q [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 152, 153, 154, 155, 156, 157, 158, 159]) := List.countP_append (p := literal q) (l₁ := [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) (l₂ := [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 152, 153, 154, 155, 156, 157, 158, 159])
  have hm := merge_left (literal (valuationOf q) (261)) (literal (valuationOf q) (313)) (countLit q [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) (countLit q [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 152, 153, 154, 155, 156, 157, 158, 159]) (count313 q) 1 (meaning261 q) (meaning313 q) hs
  change valuationOf q 261 = false ∨ valuationOf q 313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 261 = false ∨ valuation q 313 = true := counterClause167 (baseVal q)

theorem counterClause168 (q : Nat → Bool) : valuationOf q 261 = false ∨ valuationOf q 311 = false ∨ valuationOf q 314 = true := by
  have hs : count313 q = (countLit q [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) + (countLit q [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 152, 153, 154, 155, 156, 157, 158, 159]) := List.countP_append (p := literal q) (l₁ := [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) (l₂ := [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 152, 153, 154, 155, 156, 157, 158, 159])
  have hm := merge_two (literal (valuationOf q) (261)) (literal (valuationOf q) (311)) (literal (valuationOf q) (314)) (countLit q [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) (countLit q [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 152, 153, 154, 155, 156, 157, 158, 159]) (count313 q) 1 1 (meaning261 q) (meaning311 q) (meaning314 q) hs
  change valuationOf q 261 = false ∨ valuationOf q 311 = false ∨ valuationOf q 314 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 261 = false ∨ valuation q 311 = false ∨ valuation q 314 = true := counterClause168 (baseVal q)

theorem counterClause169 (q : Nat → Bool) : valuationOf q 262 = false ∨ valuationOf q 314 = true := by
  have hs : count313 q = (countLit q [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) + (countLit q [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 152, 153, 154, 155, 156, 157, 158, 159]) := List.countP_append (p := literal q) (l₁ := [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) (l₂ := [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 152, 153, 154, 155, 156, 157, 158, 159])
  have hm := merge_left (literal (valuationOf q) (262)) (literal (valuationOf q) (314)) (countLit q [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]) (countLit q [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 152, 153, 154, 155, 156, 157, 158, 159]) (count313 q) 2 (meaning262 q) (meaning314 q) hs
  change valuationOf q 262 = false ∨ valuationOf q 314 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 262 = false ∨ valuation q 314 = true := counterClause169 (baseVal q)

theorem counterClause170 (q : Nat → Bool) : valuationOf q 162 = false ∨ valuationOf q 315 = true := by
  have hs : count315 q = (countLit q [161]) + (countLit q [162]) := List.countP_append (p := literal q) (l₁ := [161]) (l₂ := [162])
  have hm := merge_right (literal (valuationOf q) (162)) (literal (valuationOf q) (315)) (countLit q [161]) (countLit q [162]) (count315 q) 1 (meaning162 q) (meaning315 q) hs
  change valuationOf q 162 = false ∨ valuationOf q 315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 162 = false ∨ valuation q 315 = true := counterClause170 (baseVal q)

theorem counterClause171 (q : Nat → Bool) : valuationOf q 315 = false ∨ valuationOf q 317 = true := by
  have hs : count317 q = (countLit q [160]) + (countLit q [161, 162]) := List.countP_append (p := literal q) (l₁ := [160]) (l₂ := [161, 162])
  have hm := merge_right (literal (valuationOf q) (315)) (literal (valuationOf q) (317)) (countLit q [160]) (countLit q [161, 162]) (count317 q) 1 (meaning315 q) (meaning317 q) hs
  change valuationOf q 315 = false ∨ valuationOf q 317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 315 = false ∨ valuation q 317 = true := counterClause171 (baseVal q)

theorem counterClause172 (q : Nat → Bool) : valuationOf q 160 = false ∨ valuationOf q 317 = true := by
  have hs : count317 q = (countLit q [160]) + (countLit q [161, 162]) := List.countP_append (p := literal q) (l₁ := [160]) (l₂ := [161, 162])
  have hm := merge_left (literal (valuationOf q) (160)) (literal (valuationOf q) (317)) (countLit q [160]) (countLit q [161, 162]) (count317 q) 1 (meaning160 q) (meaning317 q) hs
  change valuationOf q 160 = false ∨ valuationOf q 317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 160 = false ∨ valuation q 317 = true := counterClause172 (baseVal q)

theorem counterClause173 (q : Nat → Bool) : valuationOf q 317 = false ∨ valuationOf q 323 = true := by
  have hs : count323 q = (countLit q [160, 161, 162]) + (countLit q [163, 164, 165]) := List.countP_append (p := literal q) (l₁ := [160, 161, 162]) (l₂ := [163, 164, 165])
  have hm := merge_left (literal (valuationOf q) (317)) (literal (valuationOf q) (323)) (countLit q [160, 161, 162]) (countLit q [163, 164, 165]) (count323 q) 1 (meaning317 q) (meaning323 q) hs
  change valuationOf q 317 = false ∨ valuationOf q 323 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 317 = false ∨ valuation q 323 = true := counterClause173 (baseVal q)

theorem counterClause174 (q : Nat → Bool) : valuationOf q 168 = false ∨ valuationOf q 325 = true := by
  have hs : count325 q = (countLit q [167]) + (countLit q [168]) := List.countP_append (p := literal q) (l₁ := [167]) (l₂ := [168])
  have hm := merge_right (literal (valuationOf q) (168)) (literal (valuationOf q) (325)) (countLit q [167]) (countLit q [168]) (count325 q) 1 (meaning168 q) (meaning325 q) hs
  change valuationOf q 168 = false ∨ valuationOf q 325 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 168 = false ∨ valuation q 325 = true := counterClause174 (baseVal q)

theorem counterClause175 (q : Nat → Bool) : valuationOf q 325 = false ∨ valuationOf q 327 = true := by
  have hs : count327 q = (countLit q [166]) + (countLit q [167, 168]) := List.countP_append (p := literal q) (l₁ := [166]) (l₂ := [167, 168])
  have hm := merge_right (literal (valuationOf q) (325)) (literal (valuationOf q) (327)) (countLit q [166]) (countLit q [167, 168]) (count327 q) 1 (meaning325 q) (meaning327 q) hs
  change valuationOf q 325 = false ∨ valuationOf q 327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 325 = false ∨ valuation q 327 = true := counterClause175 (baseVal q)

theorem counterClause176 (q : Nat → Bool) : valuationOf q 172 = false ∨ valuationOf q 331 = true := by
  have hs : count331 q = (countLit q [171]) + (countLit q [172]) := List.countP_append (p := literal q) (l₁ := [171]) (l₂ := [172])
  have hm := merge_right (literal (valuationOf q) (172)) (literal (valuationOf q) (331)) (countLit q [171]) (countLit q [172]) (count331 q) 1 (meaning172 q) (meaning331 q) hs
  change valuationOf q 172 = false ∨ valuationOf q 331 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 172 = false ∨ valuation q 331 = true := counterClause176 (baseVal q)

theorem counterClause177 (q : Nat → Bool) : valuationOf q 331 = false ∨ valuationOf q 333 = true := by
  have hs : count333 q = (countLit q [169, 170]) + (countLit q [171, 172]) := List.countP_append (p := literal q) (l₁ := [169, 170]) (l₂ := [171, 172])
  have hm := merge_right (literal (valuationOf q) (331)) (literal (valuationOf q) (333)) (countLit q [169, 170]) (countLit q [171, 172]) (count333 q) 1 (meaning331 q) (meaning333 q) hs
  change valuationOf q 331 = false ∨ valuationOf q 333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 331 = false ∨ valuation q 333 = true := counterClause177 (baseVal q)

theorem counterClause178 (q : Nat → Bool) : valuationOf q 333 = false ∨ valuationOf q 335 = true := by
  have hs : count335 q = (countLit q [166, 167, 168]) + (countLit q [169, 170, 171, 172]) := List.countP_append (p := literal q) (l₁ := [166, 167, 168]) (l₂ := [169, 170, 171, 172])
  have hm := merge_right (literal (valuationOf q) (333)) (literal (valuationOf q) (335)) (countLit q [166, 167, 168]) (countLit q [169, 170, 171, 172]) (count335 q) 1 (meaning333 q) (meaning335 q) hs
  change valuationOf q 333 = false ∨ valuationOf q 335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 333 = false ∨ valuation q 335 = true := counterClause178 (baseVal q)

theorem counterClause179 (q : Nat → Bool) : valuationOf q 327 = false ∨ valuationOf q 335 = true := by
  have hs : count335 q = (countLit q [166, 167, 168]) + (countLit q [169, 170, 171, 172]) := List.countP_append (p := literal q) (l₁ := [166, 167, 168]) (l₂ := [169, 170, 171, 172])
  have hm := merge_left (literal (valuationOf q) (327)) (literal (valuationOf q) (335)) (countLit q [166, 167, 168]) (countLit q [169, 170, 171, 172]) (count335 q) 1 (meaning327 q) (meaning335 q) hs
  change valuationOf q 327 = false ∨ valuationOf q 335 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 327 = false ∨ valuation q 335 = true := counterClause179 (baseVal q)

theorem counterClause180 (q : Nat → Bool) : valuationOf q 327 = false ∨ valuationOf q 333 = false ∨ valuationOf q 336 = true := by
  have hs : count335 q = (countLit q [166, 167, 168]) + (countLit q [169, 170, 171, 172]) := List.countP_append (p := literal q) (l₁ := [166, 167, 168]) (l₂ := [169, 170, 171, 172])
  have hm := merge_two (literal (valuationOf q) (327)) (literal (valuationOf q) (333)) (literal (valuationOf q) (336)) (countLit q [166, 167, 168]) (countLit q [169, 170, 171, 172]) (count335 q) 1 1 (meaning327 q) (meaning333 q) (meaning336 q) hs
  change valuationOf q 327 = false ∨ valuationOf q 333 = false ∨ valuationOf q 336 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 327 = false ∨ valuation q 333 = false ∨ valuation q 336 = true := counterClause180 (baseVal q)

theorem counterClause181 (q : Nat → Bool) : valuationOf q 335 = false ∨ valuationOf q 337 = true := by
  have hs : count337 q = (countLit q [160, 161, 162, 163, 164, 165]) + (countLit q [166, 167, 168, 169, 170, 171, 172]) := List.countP_append (p := literal q) (l₁ := [160, 161, 162, 163, 164, 165]) (l₂ := [166, 167, 168, 169, 170, 171, 172])
  have hm := merge_right (literal (valuationOf q) (335)) (literal (valuationOf q) (337)) (countLit q [160, 161, 162, 163, 164, 165]) (countLit q [166, 167, 168, 169, 170, 171, 172]) (count337 q) 1 (meaning335 q) (meaning337 q) hs
  change valuationOf q 335 = false ∨ valuationOf q 337 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 335 = false ∨ valuation q 337 = true := counterClause181 (baseVal q)

theorem counterClause182 (q : Nat → Bool) : valuationOf q 336 = false ∨ valuationOf q 338 = true := by
  have hs : count337 q = (countLit q [160, 161, 162, 163, 164, 165]) + (countLit q [166, 167, 168, 169, 170, 171, 172]) := List.countP_append (p := literal q) (l₁ := [160, 161, 162, 163, 164, 165]) (l₂ := [166, 167, 168, 169, 170, 171, 172])
  have hm := merge_right (literal (valuationOf q) (336)) (literal (valuationOf q) (338)) (countLit q [160, 161, 162, 163, 164, 165]) (countLit q [166, 167, 168, 169, 170, 171, 172]) (count337 q) 2 (meaning336 q) (meaning338 q) hs
  change valuationOf q 336 = false ∨ valuationOf q 338 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 336 = false ∨ valuation q 338 = true := counterClause182 (baseVal q)

theorem counterClause183 (q : Nat → Bool) : valuationOf q 323 = false ∨ valuationOf q 337 = true := by
  have hs : count337 q = (countLit q [160, 161, 162, 163, 164, 165]) + (countLit q [166, 167, 168, 169, 170, 171, 172]) := List.countP_append (p := literal q) (l₁ := [160, 161, 162, 163, 164, 165]) (l₂ := [166, 167, 168, 169, 170, 171, 172])
  have hm := merge_left (literal (valuationOf q) (323)) (literal (valuationOf q) (337)) (countLit q [160, 161, 162, 163, 164, 165]) (countLit q [166, 167, 168, 169, 170, 171, 172]) (count337 q) 1 (meaning323 q) (meaning337 q) hs
  change valuationOf q 323 = false ∨ valuationOf q 337 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 323 = false ∨ valuation q 337 = true := counterClause183 (baseVal q)

theorem counterClause184 (q : Nat → Bool) : valuationOf q 174 = false ∨ valuationOf q 339 = true := by
  have hs : count339 q = (countLit q [174]) + (countLit q [175]) := List.countP_append (p := literal q) (l₁ := [174]) (l₂ := [175])
  have hm := merge_left (literal (valuationOf q) (174)) (literal (valuationOf q) (339)) (countLit q [174]) (countLit q [175]) (count339 q) 1 (meaning174 q) (meaning339 q) hs
  change valuationOf q 174 = false ∨ valuationOf q 339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 174 = false ∨ valuation q 339 = true := counterClause184 (baseVal q)

theorem counterClause185 (q : Nat → Bool) : valuationOf q 173 = false ∨ valuationOf q 341 = true := by
  have hs : count341 q = (countLit q [173]) + (countLit q [174, 175]) := List.countP_append (p := literal q) (l₁ := [173]) (l₂ := [174, 175])
  have hm := merge_left (literal (valuationOf q) (173)) (literal (valuationOf q) (341)) (countLit q [173]) (countLit q [174, 175]) (count341 q) 1 (meaning173 q) (meaning341 q) hs
  change valuationOf q 173 = false ∨ valuationOf q 341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 173 = false ∨ valuation q 341 = true := counterClause185 (baseVal q)

theorem counterClause186 (q : Nat → Bool) : valuationOf q 173 = false ∨ valuationOf q 339 = false ∨ valuationOf q 342 = true := by
  have hs : count341 q = (countLit q [173]) + (countLit q [174, 175]) := List.countP_append (p := literal q) (l₁ := [173]) (l₂ := [174, 175])
  have hm := merge_two (literal (valuationOf q) (173)) (literal (valuationOf q) (339)) (literal (valuationOf q) (342)) (countLit q [173]) (countLit q [174, 175]) (count341 q) 1 1 (meaning173 q) (meaning339 q) (meaning342 q) hs
  change valuationOf q 173 = false ∨ valuationOf q 339 = false ∨ valuationOf q 342 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 173 = false ∨ valuation q 339 = false ∨ valuation q 342 = true := counterClause186 (baseVal q)

theorem counterClause187 (q : Nat → Bool) : valuationOf q 341 = false ∨ valuationOf q 347 = true := by
  have hs : count347 q = (countLit q [173, 174, 175]) + (countLit q [176, 177, 178]) := List.countP_append (p := literal q) (l₁ := [173, 174, 175]) (l₂ := [176, 177, 178])
  have hm := merge_left (literal (valuationOf q) (341)) (literal (valuationOf q) (347)) (countLit q [173, 174, 175]) (countLit q [176, 177, 178]) (count347 q) 1 (meaning341 q) (meaning347 q) hs
  change valuationOf q 341 = false ∨ valuationOf q 347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 341 = false ∨ valuation q 347 = true := counterClause187 (baseVal q)

theorem counterClause188 (q : Nat → Bool) : valuationOf q 342 = false ∨ valuationOf q 348 = true := by
  have hs : count347 q = (countLit q [173, 174, 175]) + (countLit q [176, 177, 178]) := List.countP_append (p := literal q) (l₁ := [173, 174, 175]) (l₂ := [176, 177, 178])
  have hm := merge_left (literal (valuationOf q) (342)) (literal (valuationOf q) (348)) (countLit q [173, 174, 175]) (countLit q [176, 177, 178]) (count347 q) 2 (meaning342 q) (meaning348 q) hs
  change valuationOf q 342 = false ∨ valuationOf q 348 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 342 = false ∨ valuation q 348 = true := counterClause188 (baseVal q)

theorem counterClause189 (q : Nat → Bool) : valuationOf q 180 = false ∨ valuationOf q 349 = true := by
  have hs : count349 q = (countLit q [180]) + (countLit q [181]) := List.countP_append (p := literal q) (l₁ := [180]) (l₂ := [181])
  have hm := merge_left (literal (valuationOf q) (180)) (literal (valuationOf q) (349)) (countLit q [180]) (countLit q [181]) (count349 q) 1 (meaning180 q) (meaning349 q) hs
  change valuationOf q 180 = false ∨ valuationOf q 349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 180 = false ∨ valuation q 349 = true := counterClause189 (baseVal q)

theorem counterClause190 (q : Nat → Bool) : valuationOf q 349 = false ∨ valuationOf q 351 = true := by
  have hs : count351 q = (countLit q [179]) + (countLit q [180, 181]) := List.countP_append (p := literal q) (l₁ := [179]) (l₂ := [180, 181])
  have hm := merge_right (literal (valuationOf q) (349)) (literal (valuationOf q) (351)) (countLit q [179]) (countLit q [180, 181]) (count351 q) 1 (meaning349 q) (meaning351 q) hs
  change valuationOf q 349 = false ∨ valuationOf q 351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 349 = false ∨ valuation q 351 = true := counterClause190 (baseVal q)

theorem counterClause191 (q : Nat → Bool) : valuationOf q 351 = false ∨ valuationOf q 359 = true := by
  have hs : count359 q = (countLit q [179, 180, 181]) + (countLit q [182, 183, 184, 185]) := List.countP_append (p := literal q) (l₁ := [179, 180, 181]) (l₂ := [182, 183, 184, 185])
  have hm := merge_left (literal (valuationOf q) (351)) (literal (valuationOf q) (359)) (countLit q [179, 180, 181]) (countLit q [182, 183, 184, 185]) (count359 q) 1 (meaning351 q) (meaning359 q) hs
  change valuationOf q 351 = false ∨ valuationOf q 359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 351 = false ∨ valuation q 359 = true := counterClause191 (baseVal q)

theorem counterClause192 (q : Nat → Bool) : valuationOf q 359 = false ∨ valuationOf q 361 = true := by
  have hs : count361 q = (countLit q [173, 174, 175, 176, 177, 178]) + (countLit q [179, 180, 181, 182, 183, 184, 185]) := List.countP_append (p := literal q) (l₁ := [173, 174, 175, 176, 177, 178]) (l₂ := [179, 180, 181, 182, 183, 184, 185])
  have hm := merge_right (literal (valuationOf q) (359)) (literal (valuationOf q) (361)) (countLit q [173, 174, 175, 176, 177, 178]) (countLit q [179, 180, 181, 182, 183, 184, 185]) (count361 q) 1 (meaning359 q) (meaning361 q) hs
  change valuationOf q 359 = false ∨ valuationOf q 361 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 359 = false ∨ valuation q 361 = true := counterClause192 (baseVal q)

theorem block5 (q : Snake 81) (h : Conditions q) : B112E249.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112249
