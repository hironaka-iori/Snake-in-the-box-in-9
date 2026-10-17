import E112057Semantics
import B112E057Inputs
namespace Snake9.Regrowth.E112057
noncomputable section
local instance blockDec37 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1185 (q : Nat → Bool) : valuationOf q 420 = false ∨ valuationOf q 436 = true := by
  have hs : count435 q = (countLit q [206, 207, 208, 209, 210, 211, 212, 213]) + (countLit q [214, 215, 216, 217, 218, 219, 220, 221]) := List.countP_append (p := literal q) (l₁ := [206, 207, 208, 209, 210, 211, 212, 213]) (l₂ := [214, 215, 216, 217, 218, 219, 220, 221])
  have hm := merge_left (literal (valuationOf q) (420)) (literal (valuationOf q) (436)) (countLit q [206, 207, 208, 209, 210, 211, 212, 213]) (countLit q [214, 215, 216, 217, 218, 219, 220, 221]) (count435 q) 2 (meaning420 q) (meaning436 q) hs
  change valuationOf q 420 = false ∨ valuationOf q 436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1185 (q : Snake 81) (h : Conditions q) : valuation q 420 = false ∨ valuation q 436 = true := counterClause1185 (baseVal q)

theorem counterClause1186 (q : Nat → Bool) : valuationOf q 435 = false ∨ valuationOf q 437 = true := by
  have hs : count437 q = (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205]) + (countLit q [206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205]) (l₂ := [206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221])
  have hm := merge_right (literal (valuationOf q) (435)) (literal (valuationOf q) (437)) (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205]) (countLit q [206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) (count437 q) 1 (meaning435 q) (meaning437 q) hs
  change valuationOf q 435 = false ∨ valuationOf q 437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1186 (q : Snake 81) (h : Conditions q) : valuation q 435 = false ∨ valuation q 437 = true := counterClause1186 (baseVal q)

theorem counterClause1187 (q : Nat → Bool) : valuationOf q 436 = false ∨ valuationOf q 438 = true := by
  have hs : count437 q = (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205]) + (countLit q [206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205]) (l₂ := [206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221])
  have hm := merge_right (literal (valuationOf q) (436)) (literal (valuationOf q) (438)) (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205]) (countLit q [206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) (count437 q) 2 (meaning436 q) (meaning438 q) hs
  change valuationOf q 436 = false ∨ valuationOf q 438 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1187 (q : Snake 81) (h : Conditions q) : valuation q 436 = false ∨ valuation q 438 = true := counterClause1187 (baseVal q)

theorem counterClause1188 (q : Nat → Bool) : valuationOf q 405 = false ∨ valuationOf q 437 = true := by
  have hs : count437 q = (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205]) + (countLit q [206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205]) (l₂ := [206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221])
  have hm := merge_left (literal (valuationOf q) (405)) (literal (valuationOf q) (437)) (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205]) (countLit q [206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) (count437 q) 1 (meaning405 q) (meaning437 q) hs
  change valuationOf q 405 = false ∨ valuationOf q 437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1188 (q : Snake 81) (h : Conditions q) : valuation q 405 = false ∨ valuation q 437 = true := counterClause1188 (baseVal q)

theorem counterClause1189 (q : Nat → Bool) : valuationOf q 405 = false ∨ valuationOf q 435 = false ∨ valuationOf q 438 = true := by
  have hs : count437 q = (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205]) + (countLit q [206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205]) (l₂ := [206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221])
  have hm := merge_two (literal (valuationOf q) (405)) (literal (valuationOf q) (435)) (literal (valuationOf q) (438)) (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205]) (countLit q [206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) (count437 q) 1 1 (meaning405 q) (meaning435 q) (meaning438 q) hs
  change valuationOf q 405 = false ∨ valuationOf q 435 = false ∨ valuationOf q 438 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1189 (q : Snake 81) (h : Conditions q) : valuation q 405 = false ∨ valuation q 435 = false ∨ valuation q 438 = true := counterClause1189 (baseVal q)

theorem counterClause1190 (q : Nat → Bool) : valuationOf q 406 = false ∨ valuationOf q 438 = true := by
  have hs : count437 q = (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205]) + (countLit q [206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205]) (l₂ := [206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221])
  have hm := merge_left (literal (valuationOf q) (406)) (literal (valuationOf q) (438)) (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205]) (countLit q [206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) (count437 q) 2 (meaning406 q) (meaning438 q) hs
  change valuationOf q 406 = false ∨ valuationOf q 438 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1190 (q : Snake 81) (h : Conditions q) : valuation q 406 = false ∨ valuation q 438 = true := counterClause1190 (baseVal q)

theorem counterClause1191 (q : Nat → Bool) : valuationOf q 225 = false ∨ valuationOf q 441 = true := by
  have hs : count441 q = (countLit q [224]) + (countLit q [225]) := List.countP_append (p := literal q) (l₁ := [224]) (l₂ := [225])
  have hm := merge_right (literal (valuationOf q) (225)) (literal (valuationOf q) (441)) (countLit q [224]) (countLit q [225]) (count441 q) 1 (meaning225 q) (meaning441 q) hs
  change valuationOf q 225 = false ∨ valuationOf q 441 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1191 (q : Snake 81) (h : Conditions q) : valuation q 225 = false ∨ valuation q 441 = true := counterClause1191 (baseVal q)

theorem counterClause1192 (q : Nat → Bool) : valuationOf q 441 = false ∨ valuationOf q 443 = true := by
  have hs : count443 q = (countLit q [222, 223]) + (countLit q [224, 225]) := List.countP_append (p := literal q) (l₁ := [222, 223]) (l₂ := [224, 225])
  have hm := merge_right (literal (valuationOf q) (441)) (literal (valuationOf q) (443)) (countLit q [222, 223]) (countLit q [224, 225]) (count443 q) 1 (meaning441 q) (meaning443 q) hs
  change valuationOf q 441 = false ∨ valuationOf q 443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1192 (q : Snake 81) (h : Conditions q) : valuation q 441 = false ∨ valuation q 443 = true := counterClause1192 (baseVal q)

theorem counterClause1193 (q : Nat → Bool) : valuationOf q 227 = false ∨ valuationOf q 445 = true := by
  have hs : count445 q = (countLit q [226]) + (countLit q [227]) := List.countP_append (p := literal q) (l₁ := [226]) (l₂ := [227])
  have hm := merge_right (literal (valuationOf q) (227)) (literal (valuationOf q) (445)) (countLit q [226]) (countLit q [227]) (count445 q) 1 (meaning227 q) (meaning445 q) hs
  change valuationOf q 227 = false ∨ valuationOf q 445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1193 (q : Snake 81) (h : Conditions q) : valuation q 227 = false ∨ valuation q 445 = true := counterClause1193 (baseVal q)

theorem counterClause1194 (q : Nat → Bool) : valuationOf q 226 = false ∨ valuationOf q 445 = true := by
  have hs : count445 q = (countLit q [226]) + (countLit q [227]) := List.countP_append (p := literal q) (l₁ := [226]) (l₂ := [227])
  have hm := merge_left (literal (valuationOf q) (226)) (literal (valuationOf q) (445)) (countLit q [226]) (countLit q [227]) (count445 q) 1 (meaning226 q) (meaning445 q) hs
  change valuationOf q 226 = false ∨ valuationOf q 445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1194 (q : Snake 81) (h : Conditions q) : valuation q 226 = false ∨ valuation q 445 = true := counterClause1194 (baseVal q)

theorem counterClause1195 (q : Nat → Bool) : valuationOf q 229 = false ∨ valuationOf q 447 = true := by
  have hs : count447 q = (countLit q [228]) + (countLit q [229]) := List.countP_append (p := literal q) (l₁ := [228]) (l₂ := [229])
  have hm := merge_right (literal (valuationOf q) (229)) (literal (valuationOf q) (447)) (countLit q [228]) (countLit q [229]) (count447 q) 1 (meaning229 q) (meaning447 q) hs
  change valuationOf q 229 = false ∨ valuationOf q 447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1195 (q : Snake 81) (h : Conditions q) : valuation q 229 = false ∨ valuation q 447 = true := counterClause1195 (baseVal q)

theorem counterClause1196 (q : Nat → Bool) : valuationOf q 447 = false ∨ valuationOf q 449 = true := by
  have hs : count449 q = (countLit q [226, 227]) + (countLit q [228, 229]) := List.countP_append (p := literal q) (l₁ := [226, 227]) (l₂ := [228, 229])
  have hm := merge_right (literal (valuationOf q) (447)) (literal (valuationOf q) (449)) (countLit q [226, 227]) (countLit q [228, 229]) (count449 q) 1 (meaning447 q) (meaning449 q) hs
  change valuationOf q 447 = false ∨ valuationOf q 449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1196 (q : Snake 81) (h : Conditions q) : valuation q 447 = false ∨ valuation q 449 = true := counterClause1196 (baseVal q)

theorem counterClause1197 (q : Nat → Bool) : valuationOf q 445 = false ∨ valuationOf q 449 = true := by
  have hs : count449 q = (countLit q [226, 227]) + (countLit q [228, 229]) := List.countP_append (p := literal q) (l₁ := [226, 227]) (l₂ := [228, 229])
  have hm := merge_left (literal (valuationOf q) (445)) (literal (valuationOf q) (449)) (countLit q [226, 227]) (countLit q [228, 229]) (count449 q) 1 (meaning445 q) (meaning449 q) hs
  change valuationOf q 445 = false ∨ valuationOf q 449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1197 (q : Snake 81) (h : Conditions q) : valuation q 445 = false ∨ valuation q 449 = true := counterClause1197 (baseVal q)

theorem counterClause1198 (q : Nat → Bool) : valuationOf q 445 = false ∨ valuationOf q 447 = false ∨ valuationOf q 450 = true := by
  have hs : count449 q = (countLit q [226, 227]) + (countLit q [228, 229]) := List.countP_append (p := literal q) (l₁ := [226, 227]) (l₂ := [228, 229])
  have hm := merge_two (literal (valuationOf q) (445)) (literal (valuationOf q) (447)) (literal (valuationOf q) (450)) (countLit q [226, 227]) (countLit q [228, 229]) (count449 q) 1 1 (meaning445 q) (meaning447 q) (meaning450 q) hs
  change valuationOf q 445 = false ∨ valuationOf q 447 = false ∨ valuationOf q 450 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1198 (q : Snake 81) (h : Conditions q) : valuation q 445 = false ∨ valuation q 447 = false ∨ valuation q 450 = true := counterClause1198 (baseVal q)

theorem counterClause1199 (q : Nat → Bool) : valuationOf q 449 = false ∨ valuationOf q 451 = true := by
  have hs : count451 q = (countLit q [222, 223, 224, 225]) + (countLit q [226, 227, 228, 229]) := List.countP_append (p := literal q) (l₁ := [222, 223, 224, 225]) (l₂ := [226, 227, 228, 229])
  have hm := merge_right (literal (valuationOf q) (449)) (literal (valuationOf q) (451)) (countLit q [222, 223, 224, 225]) (countLit q [226, 227, 228, 229]) (count451 q) 1 (meaning449 q) (meaning451 q) hs
  change valuationOf q 449 = false ∨ valuationOf q 451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1199 (q : Snake 81) (h : Conditions q) : valuation q 449 = false ∨ valuation q 451 = true := counterClause1199 (baseVal q)

theorem counterClause1200 (q : Nat → Bool) : valuationOf q 450 = false ∨ valuationOf q 452 = true := by
  have hs : count451 q = (countLit q [222, 223, 224, 225]) + (countLit q [226, 227, 228, 229]) := List.countP_append (p := literal q) (l₁ := [222, 223, 224, 225]) (l₂ := [226, 227, 228, 229])
  have hm := merge_right (literal (valuationOf q) (450)) (literal (valuationOf q) (452)) (countLit q [222, 223, 224, 225]) (countLit q [226, 227, 228, 229]) (count451 q) 2 (meaning450 q) (meaning452 q) hs
  change valuationOf q 450 = false ∨ valuationOf q 452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1200 (q : Snake 81) (h : Conditions q) : valuation q 450 = false ∨ valuation q 452 = true := counterClause1200 (baseVal q)

theorem counterClause1201 (q : Nat → Bool) : valuationOf q 443 = false ∨ valuationOf q 451 = true := by
  have hs : count451 q = (countLit q [222, 223, 224, 225]) + (countLit q [226, 227, 228, 229]) := List.countP_append (p := literal q) (l₁ := [222, 223, 224, 225]) (l₂ := [226, 227, 228, 229])
  have hm := merge_left (literal (valuationOf q) (443)) (literal (valuationOf q) (451)) (countLit q [222, 223, 224, 225]) (countLit q [226, 227, 228, 229]) (count451 q) 1 (meaning443 q) (meaning451 q) hs
  change valuationOf q 443 = false ∨ valuationOf q 451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1201 (q : Snake 81) (h : Conditions q) : valuation q 443 = false ∨ valuation q 451 = true := counterClause1201 (baseVal q)

theorem counterClause1202 (q : Nat → Bool) : valuationOf q 443 = false ∨ valuationOf q 449 = false ∨ valuationOf q 452 = true := by
  have hs : count451 q = (countLit q [222, 223, 224, 225]) + (countLit q [226, 227, 228, 229]) := List.countP_append (p := literal q) (l₁ := [222, 223, 224, 225]) (l₂ := [226, 227, 228, 229])
  have hm := merge_two (literal (valuationOf q) (443)) (literal (valuationOf q) (449)) (literal (valuationOf q) (452)) (countLit q [222, 223, 224, 225]) (countLit q [226, 227, 228, 229]) (count451 q) 1 1 (meaning443 q) (meaning449 q) (meaning452 q) hs
  change valuationOf q 443 = false ∨ valuationOf q 449 = false ∨ valuationOf q 452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1202 (q : Snake 81) (h : Conditions q) : valuation q 443 = false ∨ valuation q 449 = false ∨ valuation q 452 = true := counterClause1202 (baseVal q)

theorem counterClause1203 (q : Nat → Bool) : valuationOf q 231 = false ∨ valuationOf q 453 = true := by
  have hs : count453 q = (countLit q [230]) + (countLit q [231]) := List.countP_append (p := literal q) (l₁ := [230]) (l₂ := [231])
  have hm := merge_right (literal (valuationOf q) (231)) (literal (valuationOf q) (453)) (countLit q [230]) (countLit q [231]) (count453 q) 1 (meaning231 q) (meaning453 q) hs
  change valuationOf q 231 = false ∨ valuationOf q 453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1203 (q : Snake 81) (h : Conditions q) : valuation q 231 = false ∨ valuation q 453 = true := counterClause1203 (baseVal q)

theorem counterClause1204 (q : Nat → Bool) : valuationOf q 233 = false ∨ valuationOf q 455 = true := by
  have hs : count455 q = (countLit q [232]) + (countLit q [233]) := List.countP_append (p := literal q) (l₁ := [232]) (l₂ := [233])
  have hm := merge_right (literal (valuationOf q) (233)) (literal (valuationOf q) (455)) (countLit q [232]) (countLit q [233]) (count455 q) 1 (meaning233 q) (meaning455 q) hs
  change valuationOf q 233 = false ∨ valuationOf q 455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1204 (q : Snake 81) (h : Conditions q) : valuation q 233 = false ∨ valuation q 455 = true := counterClause1204 (baseVal q)

theorem counterClause1205 (q : Nat → Bool) : valuationOf q 455 = false ∨ valuationOf q 457 = true := by
  have hs : count457 q = (countLit q [230, 231]) + (countLit q [232, 233]) := List.countP_append (p := literal q) (l₁ := [230, 231]) (l₂ := [232, 233])
  have hm := merge_right (literal (valuationOf q) (455)) (literal (valuationOf q) (457)) (countLit q [230, 231]) (countLit q [232, 233]) (count457 q) 1 (meaning455 q) (meaning457 q) hs
  change valuationOf q 455 = false ∨ valuationOf q 457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1205 (q : Snake 81) (h : Conditions q) : valuation q 455 = false ∨ valuation q 457 = true := counterClause1205 (baseVal q)

theorem counterClause1206 (q : Nat → Bool) : valuationOf q 453 = false ∨ valuationOf q 457 = true := by
  have hs : count457 q = (countLit q [230, 231]) + (countLit q [232, 233]) := List.countP_append (p := literal q) (l₁ := [230, 231]) (l₂ := [232, 233])
  have hm := merge_left (literal (valuationOf q) (453)) (literal (valuationOf q) (457)) (countLit q [230, 231]) (countLit q [232, 233]) (count457 q) 1 (meaning453 q) (meaning457 q) hs
  change valuationOf q 453 = false ∨ valuationOf q 457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1206 (q : Snake 81) (h : Conditions q) : valuation q 453 = false ∨ valuation q 457 = true := counterClause1206 (baseVal q)

theorem counterClause1207 (q : Nat → Bool) : valuationOf q 235 = false ∨ valuationOf q 459 = true := by
  have hs : count459 q = (countLit q [234]) + (countLit q [235]) := List.countP_append (p := literal q) (l₁ := [234]) (l₂ := [235])
  have hm := merge_right (literal (valuationOf q) (235)) (literal (valuationOf q) (459)) (countLit q [234]) (countLit q [235]) (count459 q) 1 (meaning235 q) (meaning459 q) hs
  change valuationOf q 235 = false ∨ valuationOf q 459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1207 (q : Snake 81) (h : Conditions q) : valuation q 235 = false ∨ valuation q 459 = true := counterClause1207 (baseVal q)

theorem counterClause1208 (q : Nat → Bool) : valuationOf q 237 = false ∨ valuationOf q 461 = true := by
  have hs : count461 q = (countLit q [236]) + (countLit q [237]) := List.countP_append (p := literal q) (l₁ := [236]) (l₂ := [237])
  have hm := merge_right (literal (valuationOf q) (237)) (literal (valuationOf q) (461)) (countLit q [236]) (countLit q [237]) (count461 q) 1 (meaning237 q) (meaning461 q) hs
  change valuationOf q 237 = false ∨ valuationOf q 461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1208 (q : Snake 81) (h : Conditions q) : valuation q 237 = false ∨ valuation q 461 = true := counterClause1208 (baseVal q)

theorem counterClause1209 (q : Nat → Bool) : valuationOf q 461 = false ∨ valuationOf q 463 = true := by
  have hs : count463 q = (countLit q [234, 235]) + (countLit q [236, 237]) := List.countP_append (p := literal q) (l₁ := [234, 235]) (l₂ := [236, 237])
  have hm := merge_right (literal (valuationOf q) (461)) (literal (valuationOf q) (463)) (countLit q [234, 235]) (countLit q [236, 237]) (count463 q) 1 (meaning461 q) (meaning463 q) hs
  change valuationOf q 461 = false ∨ valuationOf q 463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1209 (q : Snake 81) (h : Conditions q) : valuation q 461 = false ∨ valuation q 463 = true := counterClause1209 (baseVal q)

theorem counterClause1210 (q : Nat → Bool) : valuationOf q 459 = false ∨ valuationOf q 463 = true := by
  have hs : count463 q = (countLit q [234, 235]) + (countLit q [236, 237]) := List.countP_append (p := literal q) (l₁ := [234, 235]) (l₂ := [236, 237])
  have hm := merge_left (literal (valuationOf q) (459)) (literal (valuationOf q) (463)) (countLit q [234, 235]) (countLit q [236, 237]) (count463 q) 1 (meaning459 q) (meaning463 q) hs
  change valuationOf q 459 = false ∨ valuationOf q 463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1210 (q : Snake 81) (h : Conditions q) : valuation q 459 = false ∨ valuation q 463 = true := counterClause1210 (baseVal q)

theorem counterClause1211 (q : Nat → Bool) : valuationOf q 463 = false ∨ valuationOf q 465 = true := by
  have hs : count465 q = (countLit q [230, 231, 232, 233]) + (countLit q [234, 235, 236, 237]) := List.countP_append (p := literal q) (l₁ := [230, 231, 232, 233]) (l₂ := [234, 235, 236, 237])
  have hm := merge_right (literal (valuationOf q) (463)) (literal (valuationOf q) (465)) (countLit q [230, 231, 232, 233]) (countLit q [234, 235, 236, 237]) (count465 q) 1 (meaning463 q) (meaning465 q) hs
  change valuationOf q 463 = false ∨ valuationOf q 465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1211 (q : Snake 81) (h : Conditions q) : valuation q 463 = false ∨ valuation q 465 = true := counterClause1211 (baseVal q)

theorem counterClause1212 (q : Nat → Bool) : valuationOf q 457 = false ∨ valuationOf q 465 = true := by
  have hs : count465 q = (countLit q [230, 231, 232, 233]) + (countLit q [234, 235, 236, 237]) := List.countP_append (p := literal q) (l₁ := [230, 231, 232, 233]) (l₂ := [234, 235, 236, 237])
  have hm := merge_left (literal (valuationOf q) (457)) (literal (valuationOf q) (465)) (countLit q [230, 231, 232, 233]) (countLit q [234, 235, 236, 237]) (count465 q) 1 (meaning457 q) (meaning465 q) hs
  change valuationOf q 457 = false ∨ valuationOf q 465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1212 (q : Snake 81) (h : Conditions q) : valuation q 457 = false ∨ valuation q 465 = true := counterClause1212 (baseVal q)

theorem counterClause1213 (q : Nat → Bool) : valuationOf q 457 = false ∨ valuationOf q 463 = false ∨ valuationOf q 466 = true := by
  have hs : count465 q = (countLit q [230, 231, 232, 233]) + (countLit q [234, 235, 236, 237]) := List.countP_append (p := literal q) (l₁ := [230, 231, 232, 233]) (l₂ := [234, 235, 236, 237])
  have hm := merge_two (literal (valuationOf q) (457)) (literal (valuationOf q) (463)) (literal (valuationOf q) (466)) (countLit q [230, 231, 232, 233]) (countLit q [234, 235, 236, 237]) (count465 q) 1 1 (meaning457 q) (meaning463 q) (meaning466 q) hs
  change valuationOf q 457 = false ∨ valuationOf q 463 = false ∨ valuationOf q 466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1213 (q : Snake 81) (h : Conditions q) : valuation q 457 = false ∨ valuation q 463 = false ∨ valuation q 466 = true := counterClause1213 (baseVal q)

theorem counterClause1214 (q : Nat → Bool) : valuationOf q 465 = false ∨ valuationOf q 467 = true := by
  have hs : count467 q = (countLit q [222, 223, 224, 225, 226, 227, 228, 229]) + (countLit q [230, 231, 232, 233, 234, 235, 236, 237]) := List.countP_append (p := literal q) (l₁ := [222, 223, 224, 225, 226, 227, 228, 229]) (l₂ := [230, 231, 232, 233, 234, 235, 236, 237])
  have hm := merge_right (literal (valuationOf q) (465)) (literal (valuationOf q) (467)) (countLit q [222, 223, 224, 225, 226, 227, 228, 229]) (countLit q [230, 231, 232, 233, 234, 235, 236, 237]) (count467 q) 1 (meaning465 q) (meaning467 q) hs
  change valuationOf q 465 = false ∨ valuationOf q 467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1214 (q : Snake 81) (h : Conditions q) : valuation q 465 = false ∨ valuation q 467 = true := counterClause1214 (baseVal q)

theorem counterClause1215 (q : Nat → Bool) : valuationOf q 466 = false ∨ valuationOf q 468 = true := by
  have hs : count467 q = (countLit q [222, 223, 224, 225, 226, 227, 228, 229]) + (countLit q [230, 231, 232, 233, 234, 235, 236, 237]) := List.countP_append (p := literal q) (l₁ := [222, 223, 224, 225, 226, 227, 228, 229]) (l₂ := [230, 231, 232, 233, 234, 235, 236, 237])
  have hm := merge_right (literal (valuationOf q) (466)) (literal (valuationOf q) (468)) (countLit q [222, 223, 224, 225, 226, 227, 228, 229]) (countLit q [230, 231, 232, 233, 234, 235, 236, 237]) (count467 q) 2 (meaning466 q) (meaning468 q) hs
  change valuationOf q 466 = false ∨ valuationOf q 468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1215 (q : Snake 81) (h : Conditions q) : valuation q 466 = false ∨ valuation q 468 = true := counterClause1215 (baseVal q)

theorem counterClause1216 (q : Nat → Bool) : valuationOf q 451 = false ∨ valuationOf q 467 = true := by
  have hs : count467 q = (countLit q [222, 223, 224, 225, 226, 227, 228, 229]) + (countLit q [230, 231, 232, 233, 234, 235, 236, 237]) := List.countP_append (p := literal q) (l₁ := [222, 223, 224, 225, 226, 227, 228, 229]) (l₂ := [230, 231, 232, 233, 234, 235, 236, 237])
  have hm := merge_left (literal (valuationOf q) (451)) (literal (valuationOf q) (467)) (countLit q [222, 223, 224, 225, 226, 227, 228, 229]) (countLit q [230, 231, 232, 233, 234, 235, 236, 237]) (count467 q) 1 (meaning451 q) (meaning467 q) hs
  change valuationOf q 451 = false ∨ valuationOf q 467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1216 (q : Snake 81) (h : Conditions q) : valuation q 451 = false ∨ valuation q 467 = true := counterClause1216 (baseVal q)

theorem block37 (q : Snake 81) (h : Conditions q) : B112E057.Block37 (valuation q) :=
  ⟨clause1185 q h, clause1186 q h, clause1187 q h, clause1188 q h, clause1189 q h, clause1190 q h, clause1191 q h, clause1192 q h, clause1193 q h, clause1194 q h, clause1195 q h, clause1196 q h, clause1197 q h, clause1198 q h, clause1199 q h, clause1200 q h, clause1201 q h, clause1202 q h, clause1203 q h, clause1204 q h, clause1205 q h, clause1206 q h, clause1207 q h, clause1208 q h, clause1209 q h, clause1210 q h, clause1211 q h, clause1212 q h, clause1213 q h, clause1214 q h, clause1215 q h, clause1216 q h⟩

end
end Snake9.Regrowth.E112057
