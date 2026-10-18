import E112190Semantics
import B112E190Inputs
namespace Snake9.Regrowth.E112190
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause161 (q : Nat → Bool) : valuationOf q 307 = false ∨ valuationOf q 311 = true := by
  have hs : count311 q = (countLit q [159, 160]) + (countLit q [161, 162]) := List.countP_append (p := literal q) (l₁ := [159, 160]) (l₂ := [161, 162])
  have hm := merge_left (literal (valuationOf q) (307)) (literal (valuationOf q) (311)) (countLit q [159, 160]) (countLit q [161, 162]) (count311 q) 1 (meaning307 q) (meaning311 q) hs
  change valuationOf q 307 = false ∨ valuationOf q 311 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 307 = false ∨ valuation q 311 = true := counterClause161 (baseVal q)

theorem counterClause162 (q : Nat → Bool) : valuationOf q 311 = false ∨ valuationOf q 313 = true := by
  have hs : count313 q = (countLit q [156, 157, 158]) + (countLit q [159, 160, 161, 162]) := List.countP_append (p := literal q) (l₁ := [156, 157, 158]) (l₂ := [159, 160, 161, 162])
  have hm := merge_right (literal (valuationOf q) (311)) (literal (valuationOf q) (313)) (countLit q [156, 157, 158]) (countLit q [159, 160, 161, 162]) (count313 q) 1 (meaning311 q) (meaning313 q) hs
  change valuationOf q 311 = false ∨ valuationOf q 313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 311 = false ∨ valuation q 313 = true := counterClause162 (baseVal q)

theorem counterClause163 (q : Nat → Bool) : valuationOf q 305 = false ∨ valuationOf q 313 = true := by
  have hs : count313 q = (countLit q [156, 157, 158]) + (countLit q [159, 160, 161, 162]) := List.countP_append (p := literal q) (l₁ := [156, 157, 158]) (l₂ := [159, 160, 161, 162])
  have hm := merge_left (literal (valuationOf q) (305)) (literal (valuationOf q) (313)) (countLit q [156, 157, 158]) (countLit q [159, 160, 161, 162]) (count313 q) 1 (meaning305 q) (meaning313 q) hs
  change valuationOf q 305 = false ∨ valuationOf q 313 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 305 = false ∨ valuation q 313 = true := counterClause163 (baseVal q)

theorem counterClause164 (q : Nat → Bool) : valuationOf q 313 = false ∨ valuationOf q 315 = true := by
  have hs : count315 q = (countLit q [149, 150, 151, 152, 153, 154, 155]) + (countLit q [156, 157, 158, 159, 160, 161, 162]) := List.countP_append (p := literal q) (l₁ := [149, 150, 151, 152, 153, 154, 155]) (l₂ := [156, 157, 158, 159, 160, 161, 162])
  have hm := merge_right (literal (valuationOf q) (313)) (literal (valuationOf q) (315)) (countLit q [149, 150, 151, 152, 153, 154, 155]) (countLit q [156, 157, 158, 159, 160, 161, 162]) (count315 q) 1 (meaning313 q) (meaning315 q) hs
  change valuationOf q 313 = false ∨ valuationOf q 315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 313 = false ∨ valuation q 315 = true := counterClause164 (baseVal q)

theorem counterClause165 (q : Nat → Bool) : valuationOf q 301 = false ∨ valuationOf q 315 = true := by
  have hs : count315 q = (countLit q [149, 150, 151, 152, 153, 154, 155]) + (countLit q [156, 157, 158, 159, 160, 161, 162]) := List.countP_append (p := literal q) (l₁ := [149, 150, 151, 152, 153, 154, 155]) (l₂ := [156, 157, 158, 159, 160, 161, 162])
  have hm := merge_left (literal (valuationOf q) (301)) (literal (valuationOf q) (315)) (countLit q [149, 150, 151, 152, 153, 154, 155]) (countLit q [156, 157, 158, 159, 160, 161, 162]) (count315 q) 1 (meaning301 q) (meaning315 q) hs
  change valuationOf q 301 = false ∨ valuationOf q 315 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 301 = false ∨ valuation q 315 = true := counterClause165 (baseVal q)

theorem counterClause166 (q : Nat → Bool) : valuationOf q 315 = false ∨ valuationOf q 317 = true := by
  have hs : count317 q = (countLit q [136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) + (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162]) := List.countP_append (p := literal q) (l₁ := [136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (l₂ := [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162])
  have hm := merge_right (literal (valuationOf q) (315)) (literal (valuationOf q) (317)) (countLit q [136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162]) (count317 q) 1 (meaning315 q) (meaning317 q) hs
  change valuationOf q 315 = false ∨ valuationOf q 317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 315 = false ∨ valuation q 317 = true := counterClause166 (baseVal q)

theorem counterClause167 (q : Nat → Bool) : valuationOf q 289 = false ∨ valuationOf q 317 = true := by
  have hs : count317 q = (countLit q [136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) + (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162]) := List.countP_append (p := literal q) (l₁ := [136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (l₂ := [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162])
  have hm := merge_left (literal (valuationOf q) (289)) (literal (valuationOf q) (317)) (countLit q [136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162]) (count317 q) 1 (meaning289 q) (meaning317 q) hs
  change valuationOf q 289 = false ∨ valuationOf q 317 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 289 = false ∨ valuation q 317 = true := counterClause167 (baseVal q)

theorem counterClause168 (q : Nat → Bool) : valuationOf q 289 = false ∨ valuationOf q 315 = false ∨ valuationOf q 318 = true := by
  have hs : count317 q = (countLit q [136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) + (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162]) := List.countP_append (p := literal q) (l₁ := [136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (l₂ := [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162])
  have hm := merge_two (literal (valuationOf q) (289)) (literal (valuationOf q) (315)) (literal (valuationOf q) (318)) (countLit q [136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162]) (count317 q) 1 1 (meaning289 q) (meaning315 q) (meaning318 q) hs
  change valuationOf q 289 = false ∨ valuationOf q 315 = false ∨ valuationOf q 318 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 289 = false ∨ valuation q 315 = false ∨ valuation q 318 = true := counterClause168 (baseVal q)

theorem counterClause169 (q : Nat → Bool) : valuationOf q 317 = false ∨ valuationOf q 319 = true := by
  have hs : count319 q = (countLit q [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]) + (countLit q [136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162]) := List.countP_append (p := literal q) (l₁ := [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]) (l₂ := [136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162])
  have hm := merge_right (literal (valuationOf q) (317)) (literal (valuationOf q) (319)) (countLit q [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]) (countLit q [136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162]) (count319 q) 1 (meaning317 q) (meaning319 q) hs
  change valuationOf q 317 = false ∨ valuationOf q 319 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 317 = false ∨ valuation q 319 = true := counterClause169 (baseVal q)

theorem counterClause170 (q : Nat → Bool) : valuationOf q 318 = false ∨ valuationOf q 320 = true := by
  have hs : count319 q = (countLit q [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]) + (countLit q [136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162]) := List.countP_append (p := literal q) (l₁ := [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]) (l₂ := [136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162])
  have hm := merge_right (literal (valuationOf q) (318)) (literal (valuationOf q) (320)) (countLit q [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]) (countLit q [136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162]) (count319 q) 2 (meaning318 q) (meaning320 q) hs
  change valuationOf q 318 = false ∨ valuationOf q 320 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 318 = false ∨ valuation q 320 = true := counterClause170 (baseVal q)

theorem counterClause171 (q : Nat → Bool) : valuationOf q 163 = false ∨ valuationOf q 323 = true := by
  have hs : count323 q = (countLit q [163]) + (countLit q [164, 165]) := List.countP_append (p := literal q) (l₁ := [163]) (l₂ := [164, 165])
  have hm := merge_left (literal (valuationOf q) (163)) (literal (valuationOf q) (323)) (countLit q [163]) (countLit q [164, 165]) (count323 q) 1 (meaning163 q) (meaning323 q) hs
  change valuationOf q 163 = false ∨ valuationOf q 323 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 163 = false ∨ valuation q 323 = true := counterClause171 (baseVal q)

theorem counterClause172 (q : Nat → Bool) : valuationOf q 168 = false ∨ valuationOf q 325 = true := by
  have hs : count325 q = (countLit q [167]) + (countLit q [168]) := List.countP_append (p := literal q) (l₁ := [167]) (l₂ := [168])
  have hm := merge_right (literal (valuationOf q) (168)) (literal (valuationOf q) (325)) (countLit q [167]) (countLit q [168]) (count325 q) 1 (meaning168 q) (meaning325 q) hs
  change valuationOf q 168 = false ∨ valuationOf q 325 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 168 = false ∨ valuation q 325 = true := counterClause172 (baseVal q)

theorem counterClause173 (q : Nat → Bool) : valuationOf q 325 = false ∨ valuationOf q 327 = true := by
  have hs : count327 q = (countLit q [166]) + (countLit q [167, 168]) := List.countP_append (p := literal q) (l₁ := [166]) (l₂ := [167, 168])
  have hm := merge_right (literal (valuationOf q) (325)) (literal (valuationOf q) (327)) (countLit q [166]) (countLit q [167, 168]) (count327 q) 1 (meaning325 q) (meaning327 q) hs
  change valuationOf q 325 = false ∨ valuationOf q 327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 325 = false ∨ valuation q 327 = true := counterClause173 (baseVal q)

theorem counterClause174 (q : Nat → Bool) : valuationOf q 166 = false ∨ valuationOf q 327 = true := by
  have hs : count327 q = (countLit q [166]) + (countLit q [167, 168]) := List.countP_append (p := literal q) (l₁ := [166]) (l₂ := [167, 168])
  have hm := merge_left (literal (valuationOf q) (166)) (literal (valuationOf q) (327)) (countLit q [166]) (countLit q [167, 168]) (count327 q) 1 (meaning166 q) (meaning327 q) hs
  change valuationOf q 166 = false ∨ valuationOf q 327 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 166 = false ∨ valuation q 327 = true := counterClause174 (baseVal q)

theorem counterClause175 (q : Nat → Bool) : valuationOf q 327 = false ∨ valuationOf q 329 = true := by
  have hs : count329 q = (countLit q [163, 164, 165]) + (countLit q [166, 167, 168]) := List.countP_append (p := literal q) (l₁ := [163, 164, 165]) (l₂ := [166, 167, 168])
  have hm := merge_right (literal (valuationOf q) (327)) (literal (valuationOf q) (329)) (countLit q [163, 164, 165]) (countLit q [166, 167, 168]) (count329 q) 1 (meaning327 q) (meaning329 q) hs
  change valuationOf q 327 = false ∨ valuationOf q 329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 327 = false ∨ valuation q 329 = true := counterClause175 (baseVal q)

theorem counterClause176 (q : Nat → Bool) : valuationOf q 323 = false ∨ valuationOf q 329 = true := by
  have hs : count329 q = (countLit q [163, 164, 165]) + (countLit q [166, 167, 168]) := List.countP_append (p := literal q) (l₁ := [163, 164, 165]) (l₂ := [166, 167, 168])
  have hm := merge_left (literal (valuationOf q) (323)) (literal (valuationOf q) (329)) (countLit q [163, 164, 165]) (countLit q [166, 167, 168]) (count329 q) 1 (meaning323 q) (meaning329 q) hs
  change valuationOf q 323 = false ∨ valuationOf q 329 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 323 = false ∨ valuation q 329 = true := counterClause176 (baseVal q)

theorem counterClause177 (q : Nat → Bool) : valuationOf q 169 = false ∨ valuationOf q 333 = true := by
  have hs : count333 q = (countLit q [169]) + (countLit q [170, 171]) := List.countP_append (p := literal q) (l₁ := [169]) (l₂ := [170, 171])
  have hm := merge_left (literal (valuationOf q) (169)) (literal (valuationOf q) (333)) (countLit q [169]) (countLit q [170, 171]) (count333 q) 1 (meaning169 q) (meaning333 q) hs
  change valuationOf q 169 = false ∨ valuationOf q 333 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 169 = false ∨ valuation q 333 = true := counterClause177 (baseVal q)

theorem counterClause178 (q : Nat → Bool) : valuationOf q 175 = false ∨ valuationOf q 337 = true := by
  have hs : count337 q = (countLit q [174]) + (countLit q [175]) := List.countP_append (p := literal q) (l₁ := [174]) (l₂ := [175])
  have hm := merge_right (literal (valuationOf q) (175)) (literal (valuationOf q) (337)) (countLit q [174]) (countLit q [175]) (count337 q) 1 (meaning175 q) (meaning337 q) hs
  change valuationOf q 175 = false ∨ valuationOf q 337 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 175 = false ∨ valuation q 337 = true := counterClause178 (baseVal q)

theorem counterClause179 (q : Nat → Bool) : valuationOf q 337 = false ∨ valuationOf q 339 = true := by
  have hs : count339 q = (countLit q [172, 173]) + (countLit q [174, 175]) := List.countP_append (p := literal q) (l₁ := [172, 173]) (l₂ := [174, 175])
  have hm := merge_right (literal (valuationOf q) (337)) (literal (valuationOf q) (339)) (countLit q [172, 173]) (countLit q [174, 175]) (count339 q) 1 (meaning337 q) (meaning339 q) hs
  change valuationOf q 337 = false ∨ valuationOf q 339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 337 = false ∨ valuation q 339 = true := counterClause179 (baseVal q)

theorem counterClause180 (q : Nat → Bool) : valuationOf q 339 = false ∨ valuationOf q 341 = true := by
  have hs : count341 q = (countLit q [169, 170, 171]) + (countLit q [172, 173, 174, 175]) := List.countP_append (p := literal q) (l₁ := [169, 170, 171]) (l₂ := [172, 173, 174, 175])
  have hm := merge_right (literal (valuationOf q) (339)) (literal (valuationOf q) (341)) (countLit q [169, 170, 171]) (countLit q [172, 173, 174, 175]) (count341 q) 1 (meaning339 q) (meaning341 q) hs
  change valuationOf q 339 = false ∨ valuationOf q 341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 339 = false ∨ valuation q 341 = true := counterClause180 (baseVal q)

theorem counterClause181 (q : Nat → Bool) : valuationOf q 333 = false ∨ valuationOf q 341 = true := by
  have hs : count341 q = (countLit q [169, 170, 171]) + (countLit q [172, 173, 174, 175]) := List.countP_append (p := literal q) (l₁ := [169, 170, 171]) (l₂ := [172, 173, 174, 175])
  have hm := merge_left (literal (valuationOf q) (333)) (literal (valuationOf q) (341)) (countLit q [169, 170, 171]) (countLit q [172, 173, 174, 175]) (count341 q) 1 (meaning333 q) (meaning341 q) hs
  change valuationOf q 333 = false ∨ valuationOf q 341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 333 = false ∨ valuation q 341 = true := counterClause181 (baseVal q)

theorem counterClause182 (q : Nat → Bool) : valuationOf q 341 = false ∨ valuationOf q 343 = true := by
  have hs : count343 q = (countLit q [163, 164, 165, 166, 167, 168]) + (countLit q [169, 170, 171, 172, 173, 174, 175]) := List.countP_append (p := literal q) (l₁ := [163, 164, 165, 166, 167, 168]) (l₂ := [169, 170, 171, 172, 173, 174, 175])
  have hm := merge_right (literal (valuationOf q) (341)) (literal (valuationOf q) (343)) (countLit q [163, 164, 165, 166, 167, 168]) (countLit q [169, 170, 171, 172, 173, 174, 175]) (count343 q) 1 (meaning341 q) (meaning343 q) hs
  change valuationOf q 341 = false ∨ valuationOf q 343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 341 = false ∨ valuation q 343 = true := counterClause182 (baseVal q)

theorem counterClause183 (q : Nat → Bool) : valuationOf q 329 = false ∨ valuationOf q 343 = true := by
  have hs : count343 q = (countLit q [163, 164, 165, 166, 167, 168]) + (countLit q [169, 170, 171, 172, 173, 174, 175]) := List.countP_append (p := literal q) (l₁ := [163, 164, 165, 166, 167, 168]) (l₂ := [169, 170, 171, 172, 173, 174, 175])
  have hm := merge_left (literal (valuationOf q) (329)) (literal (valuationOf q) (343)) (countLit q [163, 164, 165, 166, 167, 168]) (countLit q [169, 170, 171, 172, 173, 174, 175]) (count343 q) 1 (meaning329 q) (meaning343 q) hs
  change valuationOf q 329 = false ∨ valuationOf q 343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 329 = false ∨ valuation q 343 = true := counterClause183 (baseVal q)

theorem counterClause184 (q : Nat → Bool) : valuationOf q 181 = false ∨ valuationOf q 351 = true := by
  have hs : count351 q = (countLit q [181]) + (countLit q [182]) := List.countP_append (p := literal q) (l₁ := [181]) (l₂ := [182])
  have hm := merge_left (literal (valuationOf q) (181)) (literal (valuationOf q) (351)) (countLit q [181]) (countLit q [182]) (count351 q) 1 (meaning181 q) (meaning351 q) hs
  change valuationOf q 181 = false ∨ valuationOf q 351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 181 = false ∨ valuation q 351 = true := counterClause184 (baseVal q)

theorem counterClause185 (q : Nat → Bool) : valuationOf q 351 = false ∨ valuationOf q 353 = true := by
  have hs : count353 q = (countLit q [179, 180]) + (countLit q [181, 182]) := List.countP_append (p := literal q) (l₁ := [179, 180]) (l₂ := [181, 182])
  have hm := merge_right (literal (valuationOf q) (351)) (literal (valuationOf q) (353)) (countLit q [179, 180]) (countLit q [181, 182]) (count353 q) 1 (meaning351 q) (meaning353 q) hs
  change valuationOf q 351 = false ∨ valuationOf q 353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 351 = false ∨ valuation q 353 = true := counterClause185 (baseVal q)

theorem counterClause186 (q : Nat → Bool) : valuationOf q 353 = false ∨ valuationOf q 355 = true := by
  have hs : count355 q = (countLit q [176, 177, 178]) + (countLit q [179, 180, 181, 182]) := List.countP_append (p := literal q) (l₁ := [176, 177, 178]) (l₂ := [179, 180, 181, 182])
  have hm := merge_right (literal (valuationOf q) (353)) (literal (valuationOf q) (355)) (countLit q [176, 177, 178]) (countLit q [179, 180, 181, 182]) (count355 q) 1 (meaning353 q) (meaning355 q) hs
  change valuationOf q 353 = false ∨ valuationOf q 355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 353 = false ∨ valuation q 355 = true := counterClause186 (baseVal q)

theorem counterClause187 (q : Nat → Bool) : valuationOf q 355 = false ∨ valuationOf q 369 = true := by
  have hs : count369 q = (countLit q [176, 177, 178, 179, 180, 181, 182]) + (countLit q [183, 184, 185, 186, 187, 188, 189]) := List.countP_append (p := literal q) (l₁ := [176, 177, 178, 179, 180, 181, 182]) (l₂ := [183, 184, 185, 186, 187, 188, 189])
  have hm := merge_left (literal (valuationOf q) (355)) (literal (valuationOf q) (369)) (countLit q [176, 177, 178, 179, 180, 181, 182]) (countLit q [183, 184, 185, 186, 187, 188, 189]) (count369 q) 1 (meaning355 q) (meaning369 q) hs
  change valuationOf q 355 = false ∨ valuationOf q 369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 355 = false ∨ valuation q 369 = true := counterClause187 (baseVal q)

theorem counterClause188 (q : Nat → Bool) : valuationOf q 343 = false ∨ valuationOf q 371 = true := by
  have hs : count371 q = (countLit q [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) + (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) := List.countP_append (p := literal q) (l₁ := [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) (l₂ := [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189])
  have hm := merge_left (literal (valuationOf q) (343)) (literal (valuationOf q) (371)) (countLit q [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) (count371 q) 1 (meaning343 q) (meaning371 q) hs
  change valuationOf q 343 = false ∨ valuationOf q 371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 343 = false ∨ valuation q 371 = true := counterClause188 (baseVal q)

theorem counterClause189 (q : Nat → Bool) : valuationOf q 343 = false ∨ valuationOf q 369 = false ∨ valuationOf q 372 = true := by
  have hs : count371 q = (countLit q [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) + (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) := List.countP_append (p := literal q) (l₁ := [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) (l₂ := [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189])
  have hm := merge_two (literal (valuationOf q) (343)) (literal (valuationOf q) (369)) (literal (valuationOf q) (372)) (countLit q [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]) (countLit q [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]) (count371 q) 1 1 (meaning343 q) (meaning369 q) (meaning372 q) hs
  change valuationOf q 343 = false ∨ valuationOf q 369 = false ∨ valuationOf q 372 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 343 = false ∨ valuation q 369 = false ∨ valuation q 372 = true := counterClause189 (baseVal q)

theorem counterClause190 (q : Nat → Bool) : valuationOf q 191 = false ∨ valuationOf q 373 = true := by
  have hs : count373 q = (countLit q [191]) + (countLit q [192]) := List.countP_append (p := literal q) (l₁ := [191]) (l₂ := [192])
  have hm := merge_left (literal (valuationOf q) (191)) (literal (valuationOf q) (373)) (countLit q [191]) (countLit q [192]) (count373 q) 1 (meaning191 q) (meaning373 q) hs
  change valuationOf q 191 = false ∨ valuationOf q 373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 191 = false ∨ valuation q 373 = true := counterClause190 (baseVal q)

theorem counterClause191 (q : Nat → Bool) : valuationOf q 373 = false ∨ valuationOf q 375 = true := by
  have hs : count375 q = (countLit q [190]) + (countLit q [191, 192]) := List.countP_append (p := literal q) (l₁ := [190]) (l₂ := [191, 192])
  have hm := merge_right (literal (valuationOf q) (373)) (literal (valuationOf q) (375)) (countLit q [190]) (countLit q [191, 192]) (count375 q) 1 (meaning373 q) (meaning375 q) hs
  change valuationOf q 373 = false ∨ valuationOf q 375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 373 = false ∨ valuation q 375 = true := counterClause191 (baseVal q)

theorem counterClause192 (q : Nat → Bool) : valuationOf q 375 = false ∨ valuationOf q 381 = true := by
  have hs : count381 q = (countLit q [190, 191, 192]) + (countLit q [193, 194, 195]) := List.countP_append (p := literal q) (l₁ := [190, 191, 192]) (l₂ := [193, 194, 195])
  have hm := merge_left (literal (valuationOf q) (375)) (literal (valuationOf q) (381)) (countLit q [190, 191, 192]) (countLit q [193, 194, 195]) (count381 q) 1 (meaning375 q) (meaning381 q) hs
  change valuationOf q 375 = false ∨ valuationOf q 381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 375 = false ∨ valuation q 381 = true := counterClause192 (baseVal q)

theorem block5 (q : Snake 81) (h : Conditions q) : B112E190.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112190
