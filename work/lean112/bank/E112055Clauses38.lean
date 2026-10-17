import E112055Semantics
import B112E055Inputs
namespace Snake9.Regrowth.E112055
noncomputable section
local instance blockDec38 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1217 (q : Nat → Bool) : valuationOf q 228 = false ∨ valuationOf q 449 = true := by
  have hs : count449 q = (countLit q [228]) + (countLit q [229]) := List.countP_append (p := literal q) (l₁ := [228]) (l₂ := [229])
  have hm := merge_left (literal (valuationOf q) (228)) (literal (valuationOf q) (449)) (countLit q [228]) (countLit q [229]) (count449 q) 1 (meaning228 q) (meaning449 q) hs
  change valuationOf q 228 = false ∨ valuationOf q 449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1217 (q : Snake 81) (h : Conditions q) : valuation q 228 = false ∨ valuation q 449 = true := counterClause1217 (baseVal q)

theorem counterClause1218 (q : Nat → Bool) : valuationOf q 230 = false ∨ valuationOf q 451 = true := by
  have hs : count451 q = (countLit q [230]) + (countLit q [231]) := List.countP_append (p := literal q) (l₁ := [230]) (l₂ := [231])
  have hm := merge_left (literal (valuationOf q) (230)) (literal (valuationOf q) (451)) (countLit q [230]) (countLit q [231]) (count451 q) 1 (meaning230 q) (meaning451 q) hs
  change valuationOf q 230 = false ∨ valuationOf q 451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1218 (q : Snake 81) (h : Conditions q) : valuation q 230 = false ∨ valuation q 451 = true := counterClause1218 (baseVal q)

theorem counterClause1219 (q : Nat → Bool) : valuationOf q 451 = false ∨ valuationOf q 453 = true := by
  have hs : count453 q = (countLit q [228, 229]) + (countLit q [230, 231]) := List.countP_append (p := literal q) (l₁ := [228, 229]) (l₂ := [230, 231])
  have hm := merge_right (literal (valuationOf q) (451)) (literal (valuationOf q) (453)) (countLit q [228, 229]) (countLit q [230, 231]) (count453 q) 1 (meaning451 q) (meaning453 q) hs
  change valuationOf q 451 = false ∨ valuationOf q 453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1219 (q : Snake 81) (h : Conditions q) : valuation q 451 = false ∨ valuation q 453 = true := counterClause1219 (baseVal q)

theorem counterClause1220 (q : Nat → Bool) : valuationOf q 449 = false ∨ valuationOf q 453 = true := by
  have hs : count453 q = (countLit q [228, 229]) + (countLit q [230, 231]) := List.countP_append (p := literal q) (l₁ := [228, 229]) (l₂ := [230, 231])
  have hm := merge_left (literal (valuationOf q) (449)) (literal (valuationOf q) (453)) (countLit q [228, 229]) (countLit q [230, 231]) (count453 q) 1 (meaning449 q) (meaning453 q) hs
  change valuationOf q 449 = false ∨ valuationOf q 453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1220 (q : Snake 81) (h : Conditions q) : valuation q 449 = false ∨ valuation q 453 = true := counterClause1220 (baseVal q)

theorem counterClause1221 (q : Nat → Bool) : valuationOf q 449 = false ∨ valuationOf q 451 = false ∨ valuationOf q 454 = true := by
  have hs : count453 q = (countLit q [228, 229]) + (countLit q [230, 231]) := List.countP_append (p := literal q) (l₁ := [228, 229]) (l₂ := [230, 231])
  have hm := merge_two (literal (valuationOf q) (449)) (literal (valuationOf q) (451)) (literal (valuationOf q) (454)) (countLit q [228, 229]) (countLit q [230, 231]) (count453 q) 1 1 (meaning449 q) (meaning451 q) (meaning454 q) hs
  change valuationOf q 449 = false ∨ valuationOf q 451 = false ∨ valuationOf q 454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1221 (q : Snake 81) (h : Conditions q) : valuation q 449 = false ∨ valuation q 451 = false ∨ valuation q 454 = true := counterClause1221 (baseVal q)

theorem counterClause1222 (q : Nat → Bool) : valuationOf q 453 = false ∨ valuationOf q 455 = true := by
  have hs : count455 q = (countLit q [224, 225, 226, 227]) + (countLit q [228, 229, 230, 231]) := List.countP_append (p := literal q) (l₁ := [224, 225, 226, 227]) (l₂ := [228, 229, 230, 231])
  have hm := merge_right (literal (valuationOf q) (453)) (literal (valuationOf q) (455)) (countLit q [224, 225, 226, 227]) (countLit q [228, 229, 230, 231]) (count455 q) 1 (meaning453 q) (meaning455 q) hs
  change valuationOf q 453 = false ∨ valuationOf q 455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1222 (q : Snake 81) (h : Conditions q) : valuation q 453 = false ∨ valuation q 455 = true := counterClause1222 (baseVal q)

theorem counterClause1223 (q : Nat → Bool) : valuationOf q 454 = false ∨ valuationOf q 456 = true := by
  have hs : count455 q = (countLit q [224, 225, 226, 227]) + (countLit q [228, 229, 230, 231]) := List.countP_append (p := literal q) (l₁ := [224, 225, 226, 227]) (l₂ := [228, 229, 230, 231])
  have hm := merge_right (literal (valuationOf q) (454)) (literal (valuationOf q) (456)) (countLit q [224, 225, 226, 227]) (countLit q [228, 229, 230, 231]) (count455 q) 2 (meaning454 q) (meaning456 q) hs
  change valuationOf q 454 = false ∨ valuationOf q 456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1223 (q : Snake 81) (h : Conditions q) : valuation q 454 = false ∨ valuation q 456 = true := counterClause1223 (baseVal q)

theorem counterClause1224 (q : Nat → Bool) : valuationOf q 447 = false ∨ valuationOf q 455 = true := by
  have hs : count455 q = (countLit q [224, 225, 226, 227]) + (countLit q [228, 229, 230, 231]) := List.countP_append (p := literal q) (l₁ := [224, 225, 226, 227]) (l₂ := [228, 229, 230, 231])
  have hm := merge_left (literal (valuationOf q) (447)) (literal (valuationOf q) (455)) (countLit q [224, 225, 226, 227]) (countLit q [228, 229, 230, 231]) (count455 q) 1 (meaning447 q) (meaning455 q) hs
  change valuationOf q 447 = false ∨ valuationOf q 455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1224 (q : Snake 81) (h : Conditions q) : valuation q 447 = false ∨ valuation q 455 = true := counterClause1224 (baseVal q)

theorem counterClause1225 (q : Nat → Bool) : valuationOf q 447 = false ∨ valuationOf q 453 = false ∨ valuationOf q 456 = true := by
  have hs : count455 q = (countLit q [224, 225, 226, 227]) + (countLit q [228, 229, 230, 231]) := List.countP_append (p := literal q) (l₁ := [224, 225, 226, 227]) (l₂ := [228, 229, 230, 231])
  have hm := merge_two (literal (valuationOf q) (447)) (literal (valuationOf q) (453)) (literal (valuationOf q) (456)) (countLit q [224, 225, 226, 227]) (countLit q [228, 229, 230, 231]) (count455 q) 1 1 (meaning447 q) (meaning453 q) (meaning456 q) hs
  change valuationOf q 447 = false ∨ valuationOf q 453 = false ∨ valuationOf q 456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1225 (q : Snake 81) (h : Conditions q) : valuation q 447 = false ∨ valuation q 453 = false ∨ valuation q 456 = true := counterClause1225 (baseVal q)

theorem counterClause1226 (q : Nat → Bool) : valuationOf q 448 = false ∨ valuationOf q 456 = true := by
  have hs : count455 q = (countLit q [224, 225, 226, 227]) + (countLit q [228, 229, 230, 231]) := List.countP_append (p := literal q) (l₁ := [224, 225, 226, 227]) (l₂ := [228, 229, 230, 231])
  have hm := merge_left (literal (valuationOf q) (448)) (literal (valuationOf q) (456)) (countLit q [224, 225, 226, 227]) (countLit q [228, 229, 230, 231]) (count455 q) 2 (meaning448 q) (meaning456 q) hs
  change valuationOf q 448 = false ∨ valuationOf q 456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1226 (q : Snake 81) (h : Conditions q) : valuation q 448 = false ∨ valuation q 456 = true := counterClause1226 (baseVal q)

theorem counterClause1227 (q : Nat → Bool) : valuationOf q 232 = false ∨ valuationOf q 457 = true := by
  have hs : count457 q = (countLit q [232]) + (countLit q [233]) := List.countP_append (p := literal q) (l₁ := [232]) (l₂ := [233])
  have hm := merge_left (literal (valuationOf q) (232)) (literal (valuationOf q) (457)) (countLit q [232]) (countLit q [233]) (count457 q) 1 (meaning232 q) (meaning457 q) hs
  change valuationOf q 232 = false ∨ valuationOf q 457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1227 (q : Snake 81) (h : Conditions q) : valuation q 232 = false ∨ valuation q 457 = true := counterClause1227 (baseVal q)

theorem counterClause1228 (q : Nat → Bool) : valuationOf q 234 = false ∨ valuationOf q 459 = true := by
  have hs : count459 q = (countLit q [234]) + (countLit q [235]) := List.countP_append (p := literal q) (l₁ := [234]) (l₂ := [235])
  have hm := merge_left (literal (valuationOf q) (234)) (literal (valuationOf q) (459)) (countLit q [234]) (countLit q [235]) (count459 q) 1 (meaning234 q) (meaning459 q) hs
  change valuationOf q 234 = false ∨ valuationOf q 459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1228 (q : Snake 81) (h : Conditions q) : valuation q 234 = false ∨ valuation q 459 = true := counterClause1228 (baseVal q)

theorem counterClause1229 (q : Nat → Bool) : valuationOf q 459 = false ∨ valuationOf q 461 = true := by
  have hs : count461 q = (countLit q [232, 233]) + (countLit q [234, 235]) := List.countP_append (p := literal q) (l₁ := [232, 233]) (l₂ := [234, 235])
  have hm := merge_right (literal (valuationOf q) (459)) (literal (valuationOf q) (461)) (countLit q [232, 233]) (countLit q [234, 235]) (count461 q) 1 (meaning459 q) (meaning461 q) hs
  change valuationOf q 459 = false ∨ valuationOf q 461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1229 (q : Snake 81) (h : Conditions q) : valuation q 459 = false ∨ valuation q 461 = true := counterClause1229 (baseVal q)

theorem counterClause1230 (q : Nat → Bool) : valuationOf q 457 = false ∨ valuationOf q 461 = true := by
  have hs : count461 q = (countLit q [232, 233]) + (countLit q [234, 235]) := List.countP_append (p := literal q) (l₁ := [232, 233]) (l₂ := [234, 235])
  have hm := merge_left (literal (valuationOf q) (457)) (literal (valuationOf q) (461)) (countLit q [232, 233]) (countLit q [234, 235]) (count461 q) 1 (meaning457 q) (meaning461 q) hs
  change valuationOf q 457 = false ∨ valuationOf q 461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1230 (q : Snake 81) (h : Conditions q) : valuation q 457 = false ∨ valuation q 461 = true := counterClause1230 (baseVal q)

theorem counterClause1231 (q : Nat → Bool) : valuationOf q 457 = false ∨ valuationOf q 459 = false ∨ valuationOf q 462 = true := by
  have hs : count461 q = (countLit q [232, 233]) + (countLit q [234, 235]) := List.countP_append (p := literal q) (l₁ := [232, 233]) (l₂ := [234, 235])
  have hm := merge_two (literal (valuationOf q) (457)) (literal (valuationOf q) (459)) (literal (valuationOf q) (462)) (countLit q [232, 233]) (countLit q [234, 235]) (count461 q) 1 1 (meaning457 q) (meaning459 q) (meaning462 q) hs
  change valuationOf q 457 = false ∨ valuationOf q 459 = false ∨ valuationOf q 462 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1231 (q : Snake 81) (h : Conditions q) : valuation q 457 = false ∨ valuation q 459 = false ∨ valuation q 462 = true := counterClause1231 (baseVal q)

theorem counterClause1232 (q : Nat → Bool) : valuationOf q 236 = false ∨ valuationOf q 463 = true := by
  have hs : count463 q = (countLit q [236]) + (countLit q [237]) := List.countP_append (p := literal q) (l₁ := [236]) (l₂ := [237])
  have hm := merge_left (literal (valuationOf q) (236)) (literal (valuationOf q) (463)) (countLit q [236]) (countLit q [237]) (count463 q) 1 (meaning236 q) (meaning463 q) hs
  change valuationOf q 236 = false ∨ valuationOf q 463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1232 (q : Snake 81) (h : Conditions q) : valuation q 236 = false ∨ valuation q 463 = true := counterClause1232 (baseVal q)

theorem counterClause1233 (q : Nat → Bool) : valuationOf q 239 = false ∨ valuationOf q 465 = true := by
  have hs : count465 q = (countLit q [238]) + (countLit q [239]) := List.countP_append (p := literal q) (l₁ := [238]) (l₂ := [239])
  have hm := merge_right (literal (valuationOf q) (239)) (literal (valuationOf q) (465)) (countLit q [238]) (countLit q [239]) (count465 q) 1 (meaning239 q) (meaning465 q) hs
  change valuationOf q 239 = false ∨ valuationOf q 465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1233 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 465 = true := counterClause1233 (baseVal q)

theorem counterClause1234 (q : Nat → Bool) : valuationOf q 238 = false ∨ valuationOf q 465 = true := by
  have hs : count465 q = (countLit q [238]) + (countLit q [239]) := List.countP_append (p := literal q) (l₁ := [238]) (l₂ := [239])
  have hm := merge_left (literal (valuationOf q) (238)) (literal (valuationOf q) (465)) (countLit q [238]) (countLit q [239]) (count465 q) 1 (meaning238 q) (meaning465 q) hs
  change valuationOf q 238 = false ∨ valuationOf q 465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1234 (q : Snake 81) (h : Conditions q) : valuation q 238 = false ∨ valuation q 465 = true := counterClause1234 (baseVal q)

theorem counterClause1235 (q : Nat → Bool) : valuationOf q 238 = false ∨ valuationOf q 239 = false ∨ valuationOf q 466 = true := by
  have hs : count465 q = (countLit q [238]) + (countLit q [239]) := List.countP_append (p := literal q) (l₁ := [238]) (l₂ := [239])
  have hm := merge_two (literal (valuationOf q) (238)) (literal (valuationOf q) (239)) (literal (valuationOf q) (466)) (countLit q [238]) (countLit q [239]) (count465 q) 1 1 (meaning238 q) (meaning239 q) (meaning466 q) hs
  change valuationOf q 238 = false ∨ valuationOf q 239 = false ∨ valuationOf q 466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1235 (q : Snake 81) (h : Conditions q) : valuation q 238 = false ∨ valuation q 239 = false ∨ valuation q 466 = true := counterClause1235 (baseVal q)

theorem counterClause1236 (q : Nat → Bool) : valuationOf q 465 = false ∨ valuationOf q 467 = true := by
  have hs : count467 q = (countLit q [236, 237]) + (countLit q [238, 239]) := List.countP_append (p := literal q) (l₁ := [236, 237]) (l₂ := [238, 239])
  have hm := merge_right (literal (valuationOf q) (465)) (literal (valuationOf q) (467)) (countLit q [236, 237]) (countLit q [238, 239]) (count467 q) 1 (meaning465 q) (meaning467 q) hs
  change valuationOf q 465 = false ∨ valuationOf q 467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1236 (q : Snake 81) (h : Conditions q) : valuation q 465 = false ∨ valuation q 467 = true := counterClause1236 (baseVal q)

theorem counterClause1237 (q : Nat → Bool) : valuationOf q 466 = false ∨ valuationOf q 468 = true := by
  have hs : count467 q = (countLit q [236, 237]) + (countLit q [238, 239]) := List.countP_append (p := literal q) (l₁ := [236, 237]) (l₂ := [238, 239])
  have hm := merge_right (literal (valuationOf q) (466)) (literal (valuationOf q) (468)) (countLit q [236, 237]) (countLit q [238, 239]) (count467 q) 2 (meaning466 q) (meaning468 q) hs
  change valuationOf q 466 = false ∨ valuationOf q 468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1237 (q : Snake 81) (h : Conditions q) : valuation q 466 = false ∨ valuation q 468 = true := counterClause1237 (baseVal q)

theorem counterClause1238 (q : Nat → Bool) : valuationOf q 463 = false ∨ valuationOf q 467 = true := by
  have hs : count467 q = (countLit q [236, 237]) + (countLit q [238, 239]) := List.countP_append (p := literal q) (l₁ := [236, 237]) (l₂ := [238, 239])
  have hm := merge_left (literal (valuationOf q) (463)) (literal (valuationOf q) (467)) (countLit q [236, 237]) (countLit q [238, 239]) (count467 q) 1 (meaning463 q) (meaning467 q) hs
  change valuationOf q 463 = false ∨ valuationOf q 467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1238 (q : Snake 81) (h : Conditions q) : valuation q 463 = false ∨ valuation q 467 = true := counterClause1238 (baseVal q)

theorem counterClause1239 (q : Nat → Bool) : valuationOf q 463 = false ∨ valuationOf q 465 = false ∨ valuationOf q 468 = true := by
  have hs : count467 q = (countLit q [236, 237]) + (countLit q [238, 239]) := List.countP_append (p := literal q) (l₁ := [236, 237]) (l₂ := [238, 239])
  have hm := merge_two (literal (valuationOf q) (463)) (literal (valuationOf q) (465)) (literal (valuationOf q) (468)) (countLit q [236, 237]) (countLit q [238, 239]) (count467 q) 1 1 (meaning463 q) (meaning465 q) (meaning468 q) hs
  change valuationOf q 463 = false ∨ valuationOf q 465 = false ∨ valuationOf q 468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1239 (q : Snake 81) (h : Conditions q) : valuation q 463 = false ∨ valuation q 465 = false ∨ valuation q 468 = true := counterClause1239 (baseVal q)

theorem counterClause1240 (q : Nat → Bool) : valuationOf q 467 = false ∨ valuationOf q 469 = true := by
  have hs : count469 q = (countLit q [232, 233, 234, 235]) + (countLit q [236, 237, 238, 239]) := List.countP_append (p := literal q) (l₁ := [232, 233, 234, 235]) (l₂ := [236, 237, 238, 239])
  have hm := merge_right (literal (valuationOf q) (467)) (literal (valuationOf q) (469)) (countLit q [232, 233, 234, 235]) (countLit q [236, 237, 238, 239]) (count469 q) 1 (meaning467 q) (meaning469 q) hs
  change valuationOf q 467 = false ∨ valuationOf q 469 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1240 (q : Snake 81) (h : Conditions q) : valuation q 467 = false ∨ valuation q 469 = true := counterClause1240 (baseVal q)

theorem counterClause1241 (q : Nat → Bool) : valuationOf q 468 = false ∨ valuationOf q 470 = true := by
  have hs : count469 q = (countLit q [232, 233, 234, 235]) + (countLit q [236, 237, 238, 239]) := List.countP_append (p := literal q) (l₁ := [232, 233, 234, 235]) (l₂ := [236, 237, 238, 239])
  have hm := merge_right (literal (valuationOf q) (468)) (literal (valuationOf q) (470)) (countLit q [232, 233, 234, 235]) (countLit q [236, 237, 238, 239]) (count469 q) 2 (meaning468 q) (meaning470 q) hs
  change valuationOf q 468 = false ∨ valuationOf q 470 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1241 (q : Snake 81) (h : Conditions q) : valuation q 468 = false ∨ valuation q 470 = true := counterClause1241 (baseVal q)

theorem counterClause1242 (q : Nat → Bool) : valuationOf q 461 = false ∨ valuationOf q 469 = true := by
  have hs : count469 q = (countLit q [232, 233, 234, 235]) + (countLit q [236, 237, 238, 239]) := List.countP_append (p := literal q) (l₁ := [232, 233, 234, 235]) (l₂ := [236, 237, 238, 239])
  have hm := merge_left (literal (valuationOf q) (461)) (literal (valuationOf q) (469)) (countLit q [232, 233, 234, 235]) (countLit q [236, 237, 238, 239]) (count469 q) 1 (meaning461 q) (meaning469 q) hs
  change valuationOf q 461 = false ∨ valuationOf q 469 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1242 (q : Snake 81) (h : Conditions q) : valuation q 461 = false ∨ valuation q 469 = true := counterClause1242 (baseVal q)

theorem counterClause1243 (q : Nat → Bool) : valuationOf q 461 = false ∨ valuationOf q 467 = false ∨ valuationOf q 470 = true := by
  have hs : count469 q = (countLit q [232, 233, 234, 235]) + (countLit q [236, 237, 238, 239]) := List.countP_append (p := literal q) (l₁ := [232, 233, 234, 235]) (l₂ := [236, 237, 238, 239])
  have hm := merge_two (literal (valuationOf q) (461)) (literal (valuationOf q) (467)) (literal (valuationOf q) (470)) (countLit q [232, 233, 234, 235]) (countLit q [236, 237, 238, 239]) (count469 q) 1 1 (meaning461 q) (meaning467 q) (meaning470 q) hs
  change valuationOf q 461 = false ∨ valuationOf q 467 = false ∨ valuationOf q 470 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1243 (q : Snake 81) (h : Conditions q) : valuation q 461 = false ∨ valuation q 467 = false ∨ valuation q 470 = true := counterClause1243 (baseVal q)

theorem counterClause1244 (q : Nat → Bool) : valuationOf q 462 = false ∨ valuationOf q 470 = true := by
  have hs : count469 q = (countLit q [232, 233, 234, 235]) + (countLit q [236, 237, 238, 239]) := List.countP_append (p := literal q) (l₁ := [232, 233, 234, 235]) (l₂ := [236, 237, 238, 239])
  have hm := merge_left (literal (valuationOf q) (462)) (literal (valuationOf q) (470)) (countLit q [232, 233, 234, 235]) (countLit q [236, 237, 238, 239]) (count469 q) 2 (meaning462 q) (meaning470 q) hs
  change valuationOf q 462 = false ∨ valuationOf q 470 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1244 (q : Snake 81) (h : Conditions q) : valuation q 462 = false ∨ valuation q 470 = true := counterClause1244 (baseVal q)

theorem counterClause1245 (q : Nat → Bool) : valuationOf q 469 = false ∨ valuationOf q 471 = true := by
  have hs : count471 q = (countLit q [224, 225, 226, 227, 228, 229, 230, 231]) + (countLit q [232, 233, 234, 235, 236, 237, 238, 239]) := List.countP_append (p := literal q) (l₁ := [224, 225, 226, 227, 228, 229, 230, 231]) (l₂ := [232, 233, 234, 235, 236, 237, 238, 239])
  have hm := merge_right (literal (valuationOf q) (469)) (literal (valuationOf q) (471)) (countLit q [224, 225, 226, 227, 228, 229, 230, 231]) (countLit q [232, 233, 234, 235, 236, 237, 238, 239]) (count471 q) 1 (meaning469 q) (meaning471 q) hs
  change valuationOf q 469 = false ∨ valuationOf q 471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1245 (q : Snake 81) (h : Conditions q) : valuation q 469 = false ∨ valuation q 471 = true := counterClause1245 (baseVal q)

theorem counterClause1246 (q : Nat → Bool) : valuationOf q 470 = false ∨ valuationOf q 472 = true := by
  have hs : count471 q = (countLit q [224, 225, 226, 227, 228, 229, 230, 231]) + (countLit q [232, 233, 234, 235, 236, 237, 238, 239]) := List.countP_append (p := literal q) (l₁ := [224, 225, 226, 227, 228, 229, 230, 231]) (l₂ := [232, 233, 234, 235, 236, 237, 238, 239])
  have hm := merge_right (literal (valuationOf q) (470)) (literal (valuationOf q) (472)) (countLit q [224, 225, 226, 227, 228, 229, 230, 231]) (countLit q [232, 233, 234, 235, 236, 237, 238, 239]) (count471 q) 2 (meaning470 q) (meaning472 q) hs
  change valuationOf q 470 = false ∨ valuationOf q 472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1246 (q : Snake 81) (h : Conditions q) : valuation q 470 = false ∨ valuation q 472 = true := counterClause1246 (baseVal q)

theorem counterClause1247 (q : Nat → Bool) : valuationOf q 455 = false ∨ valuationOf q 471 = true := by
  have hs : count471 q = (countLit q [224, 225, 226, 227, 228, 229, 230, 231]) + (countLit q [232, 233, 234, 235, 236, 237, 238, 239]) := List.countP_append (p := literal q) (l₁ := [224, 225, 226, 227, 228, 229, 230, 231]) (l₂ := [232, 233, 234, 235, 236, 237, 238, 239])
  have hm := merge_left (literal (valuationOf q) (455)) (literal (valuationOf q) (471)) (countLit q [224, 225, 226, 227, 228, 229, 230, 231]) (countLit q [232, 233, 234, 235, 236, 237, 238, 239]) (count471 q) 1 (meaning455 q) (meaning471 q) hs
  change valuationOf q 455 = false ∨ valuationOf q 471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1247 (q : Snake 81) (h : Conditions q) : valuation q 455 = false ∨ valuation q 471 = true := counterClause1247 (baseVal q)

theorem counterClause1248 (q : Nat → Bool) : valuationOf q 455 = false ∨ valuationOf q 469 = false ∨ valuationOf q 472 = true := by
  have hs : count471 q = (countLit q [224, 225, 226, 227, 228, 229, 230, 231]) + (countLit q [232, 233, 234, 235, 236, 237, 238, 239]) := List.countP_append (p := literal q) (l₁ := [224, 225, 226, 227, 228, 229, 230, 231]) (l₂ := [232, 233, 234, 235, 236, 237, 238, 239])
  have hm := merge_two (literal (valuationOf q) (455)) (literal (valuationOf q) (469)) (literal (valuationOf q) (472)) (countLit q [224, 225, 226, 227, 228, 229, 230, 231]) (countLit q [232, 233, 234, 235, 236, 237, 238, 239]) (count471 q) 1 1 (meaning455 q) (meaning469 q) (meaning472 q) hs
  change valuationOf q 455 = false ∨ valuationOf q 469 = false ∨ valuationOf q 472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1248 (q : Snake 81) (h : Conditions q) : valuation q 455 = false ∨ valuation q 469 = false ∨ valuation q 472 = true := counterClause1248 (baseVal q)

theorem block38 (q : Snake 81) (h : Conditions q) : B112E055.Block38 (valuation q) :=
  ⟨clause1217 q h, clause1218 q h, clause1219 q h, clause1220 q h, clause1221 q h, clause1222 q h, clause1223 q h, clause1224 q h, clause1225 q h, clause1226 q h, clause1227 q h, clause1228 q h, clause1229 q h, clause1230 q h, clause1231 q h, clause1232 q h, clause1233 q h, clause1234 q h, clause1235 q h, clause1236 q h, clause1237 q h, clause1238 q h, clause1239 q h, clause1240 q h, clause1241 q h, clause1242 q h, clause1243 q h, clause1244 q h, clause1245 q h, clause1246 q h, clause1247 q h, clause1248 q h⟩

end
end Snake9.Regrowth.E112055
