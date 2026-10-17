import E112052Semantics
import B112E052Inputs
namespace Snake9.Regrowth.E112052
noncomputable section
local instance blockDec38 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1217 (q : Nat → Bool) : valuationOf q 475 = false ∨ valuationOf q 479 = true := by
  have hs : count479 q = (countLit q [243, 244]) + (countLit q [245, 246]) := List.countP_append (p := literal q) (l₁ := [243, 244]) (l₂ := [245, 246])
  have hm := merge_left (literal (valuationOf q) (475)) (literal (valuationOf q) (479)) (countLit q [243, 244]) (countLit q [245, 246]) (count479 q) 1 (meaning475 q) (meaning479 q) hs
  change valuationOf q 475 = false ∨ valuationOf q 479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1217 (q : Snake 81) (h : Conditions q) : valuation q 475 = false ∨ valuation q 479 = true := counterClause1217 (baseVal q)

theorem counterClause1218 (q : Nat → Bool) : valuationOf q 479 = false ∨ valuationOf q 481 = true := by
  have hs : count481 q = (countLit q [239, 240, 241, 242]) + (countLit q [243, 244, 245, 246]) := List.countP_append (p := literal q) (l₁ := [239, 240, 241, 242]) (l₂ := [243, 244, 245, 246])
  have hm := merge_right (literal (valuationOf q) (479)) (literal (valuationOf q) (481)) (countLit q [239, 240, 241, 242]) (countLit q [243, 244, 245, 246]) (count481 q) 1 (meaning479 q) (meaning481 q) hs
  change valuationOf q 479 = false ∨ valuationOf q 481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1218 (q : Snake 81) (h : Conditions q) : valuation q 479 = false ∨ valuation q 481 = true := counterClause1218 (baseVal q)

theorem counterClause1219 (q : Nat → Bool) : valuationOf q 473 = false ∨ valuationOf q 481 = true := by
  have hs : count481 q = (countLit q [239, 240, 241, 242]) + (countLit q [243, 244, 245, 246]) := List.countP_append (p := literal q) (l₁ := [239, 240, 241, 242]) (l₂ := [243, 244, 245, 246])
  have hm := merge_left (literal (valuationOf q) (473)) (literal (valuationOf q) (481)) (countLit q [239, 240, 241, 242]) (countLit q [243, 244, 245, 246]) (count481 q) 1 (meaning473 q) (meaning481 q) hs
  change valuationOf q 473 = false ∨ valuationOf q 481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1219 (q : Snake 81) (h : Conditions q) : valuation q 473 = false ∨ valuation q 481 = true := counterClause1219 (baseVal q)

theorem counterClause1220 (q : Nat → Bool) : valuationOf q 473 = false ∨ valuationOf q 479 = false ∨ valuationOf q 482 = true := by
  have hs : count481 q = (countLit q [239, 240, 241, 242]) + (countLit q [243, 244, 245, 246]) := List.countP_append (p := literal q) (l₁ := [239, 240, 241, 242]) (l₂ := [243, 244, 245, 246])
  have hm := merge_two (literal (valuationOf q) (473)) (literal (valuationOf q) (479)) (literal (valuationOf q) (482)) (countLit q [239, 240, 241, 242]) (countLit q [243, 244, 245, 246]) (count481 q) 1 1 (meaning473 q) (meaning479 q) (meaning482 q) hs
  change valuationOf q 473 = false ∨ valuationOf q 479 = false ∨ valuationOf q 482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1220 (q : Snake 81) (h : Conditions q) : valuation q 473 = false ∨ valuation q 479 = false ∨ valuation q 482 = true := counterClause1220 (baseVal q)

theorem counterClause1221 (q : Nat → Bool) : valuationOf q 248 = false ∨ valuationOf q 483 = true := by
  have hs : count483 q = (countLit q [247]) + (countLit q [248]) := List.countP_append (p := literal q) (l₁ := [247]) (l₂ := [248])
  have hm := merge_right (literal (valuationOf q) (248)) (literal (valuationOf q) (483)) (countLit q [247]) (countLit q [248]) (count483 q) 1 (meaning248 q) (meaning483 q) hs
  change valuationOf q 248 = false ∨ valuationOf q 483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1221 (q : Snake 81) (h : Conditions q) : valuation q 248 = false ∨ valuation q 483 = true := counterClause1221 (baseVal q)

theorem counterClause1222 (q : Nat → Bool) : valuationOf q 483 = false ∨ valuationOf q 487 = true := by
  have hs : count487 q = (countLit q [247, 248]) + (countLit q [249, 250]) := List.countP_append (p := literal q) (l₁ := [247, 248]) (l₂ := [249, 250])
  have hm := merge_left (literal (valuationOf q) (483)) (literal (valuationOf q) (487)) (countLit q [247, 248]) (countLit q [249, 250]) (count487 q) 1 (meaning483 q) (meaning487 q) hs
  change valuationOf q 483 = false ∨ valuationOf q 487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1222 (q : Snake 81) (h : Conditions q) : valuation q 483 = false ∨ valuation q 487 = true := counterClause1222 (baseVal q)

theorem counterClause1223 (q : Nat → Bool) : valuationOf q 252 = false ∨ valuationOf q 489 = true := by
  have hs : count489 q = (countLit q [251]) + (countLit q [252]) := List.countP_append (p := literal q) (l₁ := [251]) (l₂ := [252])
  have hm := merge_right (literal (valuationOf q) (252)) (literal (valuationOf q) (489)) (countLit q [251]) (countLit q [252]) (count489 q) 1 (meaning252 q) (meaning489 q) hs
  change valuationOf q 252 = false ∨ valuationOf q 489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1223 (q : Snake 81) (h : Conditions q) : valuation q 252 = false ∨ valuation q 489 = true := counterClause1223 (baseVal q)

theorem counterClause1224 (q : Nat → Bool) : valuationOf q 489 = false ∨ valuationOf q 493 = true := by
  have hs : count493 q = (countLit q [251, 252]) + (countLit q [253, 254]) := List.countP_append (p := literal q) (l₁ := [251, 252]) (l₂ := [253, 254])
  have hm := merge_left (literal (valuationOf q) (489)) (literal (valuationOf q) (493)) (countLit q [251, 252]) (countLit q [253, 254]) (count493 q) 1 (meaning489 q) (meaning493 q) hs
  change valuationOf q 489 = false ∨ valuationOf q 493 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1224 (q : Snake 81) (h : Conditions q) : valuation q 489 = false ∨ valuation q 493 = true := counterClause1224 (baseVal q)

theorem counterClause1225 (q : Nat → Bool) : valuationOf q 493 = false ∨ valuationOf q 495 = true := by
  have hs : count495 q = (countLit q [247, 248, 249, 250]) + (countLit q [251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [247, 248, 249, 250]) (l₂ := [251, 252, 253, 254])
  have hm := merge_right (literal (valuationOf q) (493)) (literal (valuationOf q) (495)) (countLit q [247, 248, 249, 250]) (countLit q [251, 252, 253, 254]) (count495 q) 1 (meaning493 q) (meaning495 q) hs
  change valuationOf q 493 = false ∨ valuationOf q 495 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1225 (q : Snake 81) (h : Conditions q) : valuation q 493 = false ∨ valuation q 495 = true := counterClause1225 (baseVal q)

theorem counterClause1226 (q : Nat → Bool) : valuationOf q 487 = false ∨ valuationOf q 495 = true := by
  have hs : count495 q = (countLit q [247, 248, 249, 250]) + (countLit q [251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [247, 248, 249, 250]) (l₂ := [251, 252, 253, 254])
  have hm := merge_left (literal (valuationOf q) (487)) (literal (valuationOf q) (495)) (countLit q [247, 248, 249, 250]) (countLit q [251, 252, 253, 254]) (count495 q) 1 (meaning487 q) (meaning495 q) hs
  change valuationOf q 487 = false ∨ valuationOf q 495 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1226 (q : Snake 81) (h : Conditions q) : valuation q 487 = false ∨ valuation q 495 = true := counterClause1226 (baseVal q)

theorem counterClause1227 (q : Nat → Bool) : valuationOf q 487 = false ∨ valuationOf q 493 = false ∨ valuationOf q 496 = true := by
  have hs : count495 q = (countLit q [247, 248, 249, 250]) + (countLit q [251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [247, 248, 249, 250]) (l₂ := [251, 252, 253, 254])
  have hm := merge_two (literal (valuationOf q) (487)) (literal (valuationOf q) (493)) (literal (valuationOf q) (496)) (countLit q [247, 248, 249, 250]) (countLit q [251, 252, 253, 254]) (count495 q) 1 1 (meaning487 q) (meaning493 q) (meaning496 q) hs
  change valuationOf q 487 = false ∨ valuationOf q 493 = false ∨ valuationOf q 496 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1227 (q : Snake 81) (h : Conditions q) : valuation q 487 = false ∨ valuation q 493 = false ∨ valuation q 496 = true := counterClause1227 (baseVal q)

theorem counterClause1228 (q : Nat → Bool) : valuationOf q 495 = false ∨ valuationOf q 497 = true := by
  have hs : count497 q = (countLit q [239, 240, 241, 242, 243, 244, 245, 246]) + (countLit q [247, 248, 249, 250, 251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [239, 240, 241, 242, 243, 244, 245, 246]) (l₂ := [247, 248, 249, 250, 251, 252, 253, 254])
  have hm := merge_right (literal (valuationOf q) (495)) (literal (valuationOf q) (497)) (countLit q [239, 240, 241, 242, 243, 244, 245, 246]) (countLit q [247, 248, 249, 250, 251, 252, 253, 254]) (count497 q) 1 (meaning495 q) (meaning497 q) hs
  change valuationOf q 495 = false ∨ valuationOf q 497 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1228 (q : Snake 81) (h : Conditions q) : valuation q 495 = false ∨ valuation q 497 = true := counterClause1228 (baseVal q)

theorem counterClause1229 (q : Nat → Bool) : valuationOf q 496 = false ∨ valuationOf q 498 = true := by
  have hs : count497 q = (countLit q [239, 240, 241, 242, 243, 244, 245, 246]) + (countLit q [247, 248, 249, 250, 251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [239, 240, 241, 242, 243, 244, 245, 246]) (l₂ := [247, 248, 249, 250, 251, 252, 253, 254])
  have hm := merge_right (literal (valuationOf q) (496)) (literal (valuationOf q) (498)) (countLit q [239, 240, 241, 242, 243, 244, 245, 246]) (countLit q [247, 248, 249, 250, 251, 252, 253, 254]) (count497 q) 2 (meaning496 q) (meaning498 q) hs
  change valuationOf q 496 = false ∨ valuationOf q 498 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1229 (q : Snake 81) (h : Conditions q) : valuation q 496 = false ∨ valuation q 498 = true := counterClause1229 (baseVal q)

theorem counterClause1230 (q : Nat → Bool) : valuationOf q 481 = false ∨ valuationOf q 497 = true := by
  have hs : count497 q = (countLit q [239, 240, 241, 242, 243, 244, 245, 246]) + (countLit q [247, 248, 249, 250, 251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [239, 240, 241, 242, 243, 244, 245, 246]) (l₂ := [247, 248, 249, 250, 251, 252, 253, 254])
  have hm := merge_left (literal (valuationOf q) (481)) (literal (valuationOf q) (497)) (countLit q [239, 240, 241, 242, 243, 244, 245, 246]) (countLit q [247, 248, 249, 250, 251, 252, 253, 254]) (count497 q) 1 (meaning481 q) (meaning497 q) hs
  change valuationOf q 481 = false ∨ valuationOf q 497 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1230 (q : Snake 81) (h : Conditions q) : valuation q 481 = false ∨ valuation q 497 = true := counterClause1230 (baseVal q)

theorem counterClause1231 (q : Nat → Bool) : valuationOf q 481 = false ∨ valuationOf q 495 = false ∨ valuationOf q 498 = true := by
  have hs : count497 q = (countLit q [239, 240, 241, 242, 243, 244, 245, 246]) + (countLit q [247, 248, 249, 250, 251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [239, 240, 241, 242, 243, 244, 245, 246]) (l₂ := [247, 248, 249, 250, 251, 252, 253, 254])
  have hm := merge_two (literal (valuationOf q) (481)) (literal (valuationOf q) (495)) (literal (valuationOf q) (498)) (countLit q [239, 240, 241, 242, 243, 244, 245, 246]) (countLit q [247, 248, 249, 250, 251, 252, 253, 254]) (count497 q) 1 1 (meaning481 q) (meaning495 q) (meaning498 q) hs
  change valuationOf q 481 = false ∨ valuationOf q 495 = false ∨ valuationOf q 498 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1231 (q : Snake 81) (h : Conditions q) : valuation q 481 = false ∨ valuation q 495 = false ∨ valuation q 498 = true := counterClause1231 (baseVal q)

theorem counterClause1232 (q : Nat → Bool) : valuationOf q 482 = false ∨ valuationOf q 498 = true := by
  have hs : count497 q = (countLit q [239, 240, 241, 242, 243, 244, 245, 246]) + (countLit q [247, 248, 249, 250, 251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [239, 240, 241, 242, 243, 244, 245, 246]) (l₂ := [247, 248, 249, 250, 251, 252, 253, 254])
  have hm := merge_left (literal (valuationOf q) (482)) (literal (valuationOf q) (498)) (countLit q [239, 240, 241, 242, 243, 244, 245, 246]) (countLit q [247, 248, 249, 250, 251, 252, 253, 254]) (count497 q) 2 (meaning482 q) (meaning498 q) hs
  change valuationOf q 482 = false ∨ valuationOf q 498 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1232 (q : Snake 81) (h : Conditions q) : valuation q 482 = false ∨ valuation q 498 = true := counterClause1232 (baseVal q)

theorem counterClause1233 (q : Nat → Bool) : valuationOf q 497 = false ∨ valuationOf q 499 = true := by
  have hs : count499 q = (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) + (countLit q [239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) (l₂ := [239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254])
  have hm := merge_right (literal (valuationOf q) (497)) (literal (valuationOf q) (499)) (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) (countLit q [239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) (count499 q) 1 (meaning497 q) (meaning499 q) hs
  change valuationOf q 497 = false ∨ valuationOf q 499 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1233 (q : Snake 81) (h : Conditions q) : valuation q 497 = false ∨ valuation q 499 = true := counterClause1233 (baseVal q)

theorem counterClause1234 (q : Nat → Bool) : valuationOf q 498 = false ∨ valuationOf q 500 = true := by
  have hs : count499 q = (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) + (countLit q [239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) (l₂ := [239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254])
  have hm := merge_right (literal (valuationOf q) (498)) (literal (valuationOf q) (500)) (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) (countLit q [239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) (count499 q) 2 (meaning498 q) (meaning500 q) hs
  change valuationOf q 498 = false ∨ valuationOf q 500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1234 (q : Snake 81) (h : Conditions q) : valuation q 498 = false ∨ valuation q 500 = true := counterClause1234 (baseVal q)

theorem counterClause1235 (q : Nat → Bool) : valuationOf q 467 = false ∨ valuationOf q 499 = true := by
  have hs : count499 q = (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) + (countLit q [239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) (l₂ := [239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254])
  have hm := merge_left (literal (valuationOf q) (467)) (literal (valuationOf q) (499)) (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) (countLit q [239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) (count499 q) 1 (meaning467 q) (meaning499 q) hs
  change valuationOf q 467 = false ∨ valuationOf q 499 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1235 (q : Snake 81) (h : Conditions q) : valuation q 467 = false ∨ valuation q 499 = true := counterClause1235 (baseVal q)

theorem counterClause1236 (q : Nat → Bool) : valuationOf q 467 = false ∨ valuationOf q 497 = false ∨ valuationOf q 500 = true := by
  have hs : count499 q = (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) + (countLit q [239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) (l₂ := [239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254])
  have hm := merge_two (literal (valuationOf q) (467)) (literal (valuationOf q) (497)) (literal (valuationOf q) (500)) (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) (countLit q [239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) (count499 q) 1 1 (meaning467 q) (meaning497 q) (meaning500 q) hs
  change valuationOf q 467 = false ∨ valuationOf q 497 = false ∨ valuationOf q 500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1236 (q : Snake 81) (h : Conditions q) : valuation q 467 = false ∨ valuation q 497 = false ∨ valuation q 500 = true := counterClause1236 (baseVal q)

theorem counterClause1237 (q : Nat → Bool) : valuationOf q 468 = false ∨ valuationOf q 500 = true := by
  have hs : count499 q = (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) + (countLit q [239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) (l₂ := [239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254])
  have hm := merge_left (literal (valuationOf q) (468)) (literal (valuationOf q) (500)) (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]) (countLit q [239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) (count499 q) 2 (meaning468 q) (meaning500 q) hs
  change valuationOf q 468 = false ∨ valuationOf q 500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1237 (q : Snake 81) (h : Conditions q) : valuation q 468 = false ∨ valuation q 500 = true := counterClause1237 (baseVal q)

theorem counterClause1238 (q : Nat → Bool) : valuationOf q 499 = false ∨ valuationOf q 501 = true := by
  have hs : count501 q = (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) + (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (l₂ := [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254])
  have hm := merge_right (literal (valuationOf q) (499)) (literal (valuationOf q) (501)) (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) (count501 q) 1 (meaning499 q) (meaning501 q) hs
  change valuationOf q 499 = false ∨ valuationOf q 501 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1238 (q : Snake 81) (h : Conditions q) : valuation q 499 = false ∨ valuation q 501 = true := counterClause1238 (baseVal q)

theorem counterClause1239 (q : Nat → Bool) : valuationOf q 500 = false ∨ valuationOf q 502 = true := by
  have hs : count501 q = (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) + (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (l₂ := [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254])
  have hm := merge_right (literal (valuationOf q) (500)) (literal (valuationOf q) (502)) (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) (count501 q) 2 (meaning500 q) (meaning502 q) hs
  change valuationOf q 500 = false ∨ valuationOf q 502 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1239 (q : Snake 81) (h : Conditions q) : valuation q 500 = false ∨ valuation q 502 = true := counterClause1239 (baseVal q)

theorem counterClause1240 (q : Nat → Bool) : valuationOf q 437 = false ∨ valuationOf q 501 = true := by
  have hs : count501 q = (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) + (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (l₂ := [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254])
  have hm := merge_left (literal (valuationOf q) (437)) (literal (valuationOf q) (501)) (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) (count501 q) 1 (meaning437 q) (meaning501 q) hs
  change valuationOf q 437 = false ∨ valuationOf q 501 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1240 (q : Snake 81) (h : Conditions q) : valuation q 437 = false ∨ valuation q 501 = true := counterClause1240 (baseVal q)

theorem counterClause1241 (q : Nat → Bool) : valuationOf q 437 = false ∨ valuationOf q 499 = false ∨ valuationOf q 502 = true := by
  have hs : count501 q = (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) + (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (l₂ := [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254])
  have hm := merge_two (literal (valuationOf q) (437)) (literal (valuationOf q) (499)) (literal (valuationOf q) (502)) (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) (count501 q) 1 1 (meaning437 q) (meaning499 q) (meaning502 q) hs
  change valuationOf q 437 = false ∨ valuationOf q 499 = false ∨ valuationOf q 502 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1241 (q : Snake 81) (h : Conditions q) : valuation q 437 = false ∨ valuation q 499 = false ∨ valuation q 502 = true := counterClause1241 (baseVal q)

theorem counterClause1242 (q : Nat → Bool) : valuationOf q 438 = false ∨ valuationOf q 502 = true := by
  have hs : count501 q = (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) + (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (l₂ := [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254])
  have hm := merge_left (literal (valuationOf q) (438)) (literal (valuationOf q) (502)) (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (countLit q [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) (count501 q) 2 (meaning438 q) (meaning502 q) hs
  change valuationOf q 438 = false ∨ valuationOf q 502 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1242 (q : Snake 81) (h : Conditions q) : valuation q 438 = false ∨ valuation q 502 = true := counterClause1242 (baseVal q)

theorem counterClause1243 (q : Nat → Bool) : valuationOf q 502 = false ∨ valuationOf q 504 = true := by
  have hs : count503 q = (countLit q [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) + (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (l₂ := [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254])
  have hm := merge_right (literal (valuationOf q) (502)) (literal (valuationOf q) (504)) (countLit q [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) (count503 q) 2 (meaning502 q) (meaning504 q) hs
  change valuationOf q 502 = false ∨ valuationOf q 504 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1243 (q : Snake 81) (h : Conditions q) : valuation q 502 = false ∨ valuation q 504 = true := counterClause1243 (baseVal q)

theorem counterClause1244 (q : Nat → Bool) : valuationOf q 377 = false ∨ valuationOf q 501 = false ∨ valuationOf q 504 = true := by
  have hs : count503 q = (countLit q [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) + (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (l₂ := [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254])
  have hm := merge_two (literal (valuationOf q) (377)) (literal (valuationOf q) (501)) (literal (valuationOf q) (504)) (countLit q [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) (count503 q) 1 1 (meaning377 q) (meaning501 q) (meaning504 q) hs
  change valuationOf q 377 = false ∨ valuationOf q 501 = false ∨ valuationOf q 504 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1244 (q : Snake 81) (h : Conditions q) : valuation q 377 = false ∨ valuation q 501 = false ∨ valuation q 504 = true := counterClause1244 (baseVal q)

theorem counterClause1245 (q : Nat → Bool) : valuationOf q 378 = false ∨ valuationOf q 504 = true := by
  have hs : count503 q = (countLit q [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) + (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) := List.countP_append (p := literal q) (l₁ := [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (l₂ := [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254])
  have hm := merge_left (literal (valuationOf q) (378)) (literal (valuationOf q) (504)) (countLit q [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]) (count503 q) 2 (meaning378 q) (meaning504 q) hs
  change valuationOf q 378 = false ∨ valuationOf q 504 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1245 (q : Snake 81) (h : Conditions q) : valuation q 378 = false ∨ valuation q 504 = true := counterClause1245 (baseVal q)

theorem clause1246 (q : Snake 81) (h : Conditions q) : valuation q 504 = false := by
  rw [value504]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count503 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem counterClause1247 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 1543 = true := by
  have hs : count1543 q = (countLit q [-1]) + (countLit q [-3]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-3])
  have hm := merge_right (literal (valuationOf q) (-3)) (literal (valuationOf q) (1543)) (countLit q [-1]) (countLit q [-3]) (count1543 q) 1 (meaningNeg3 q) (meaning1543 q) hs
  change (! (valuationOf q 3)) = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1247 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 1543 = true := counterClause1247 (baseVal q)

theorem counterClause1248 (q : Nat → Bool) : valuationOf q 7 = true ∨ valuationOf q 1545 = true := by
  have hs : count1545 q = (countLit q [-5]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-5]) (l₂ := [-7])
  have hm := merge_right (literal (valuationOf q) (-7)) (literal (valuationOf q) (1545)) (countLit q [-5]) (countLit q [-7]) (count1545 q) 1 (meaningNeg7 q) (meaning1545 q) hs
  change (! (valuationOf q 7)) = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1248 (q : Snake 81) (h : Conditions q) : valuation q 7 = true ∨ valuation q 1545 = true := counterClause1248 (baseVal q)

theorem block38 (q : Snake 81) (h : Conditions q) : B112E052.Block38 (valuation q) :=
  ⟨clause1217 q h, clause1218 q h, clause1219 q h, clause1220 q h, clause1221 q h, clause1222 q h, clause1223 q h, clause1224 q h, clause1225 q h, clause1226 q h, clause1227 q h, clause1228 q h, clause1229 q h, clause1230 q h, clause1231 q h, clause1232 q h, clause1233 q h, clause1234 q h, clause1235 q h, clause1236 q h, clause1237 q h, clause1238 q h, clause1239 q h, clause1240 q h, clause1241 q h, clause1242 q h, clause1243 q h, clause1244 q h, clause1245 q h, clause1246 q h, clause1247 q h, clause1248 q h⟩

end
end Snake9.Regrowth.E112052
