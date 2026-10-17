import E112019Semantics
import B112E019Inputs
namespace Snake9.Regrowth.E112019
noncomputable section
local instance blockDec38 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1217 (q : Nat → Bool) : valuationOf q 1495 = false ∨ valuationOf q 1497 = true := by
  have hs : count1497 q = (countLit q [-18]) + (countLit q [-19, -21]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-19, -21])
  have hm := merge_right (literal (valuationOf q) (1495)) (literal (valuationOf q) (1497)) (countLit q [-18]) (countLit q [-19, -21]) (count1497 q) 1 (meaning1495 q) (meaning1497 q) hs
  change valuationOf q 1495 = false ∨ valuationOf q 1497 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1217 (q : Snake 81) (h : Conditions q) : valuation q 1495 = false ∨ valuation q 1497 = true := counterClause1217 (baseVal q)

theorem counterClause1218 (q : Nat → Bool) : valuationOf q 1496 = false ∨ valuationOf q 1498 = true := by
  have hs : count1497 q = (countLit q [-18]) + (countLit q [-19, -21]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-19, -21])
  have hm := merge_right (literal (valuationOf q) (1496)) (literal (valuationOf q) (1498)) (countLit q [-18]) (countLit q [-19, -21]) (count1497 q) 2 (meaning1496 q) (meaning1498 q) hs
  change valuationOf q 1496 = false ∨ valuationOf q 1498 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1218 (q : Snake 81) (h : Conditions q) : valuation q 1496 = false ∨ valuation q 1498 = true := counterClause1218 (baseVal q)

theorem counterClause1219 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 1497 = true := by
  have hs : count1497 q = (countLit q [-18]) + (countLit q [-19, -21]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-19, -21])
  have hm := merge_left (literal (valuationOf q) (-18)) (literal (valuationOf q) (1497)) (countLit q [-18]) (countLit q [-19, -21]) (count1497 q) 1 (meaningNeg18 q) (meaning1497 q) hs
  change (! (valuationOf q 18)) = false ∨ valuationOf q 1497 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1219 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 1497 = true := counterClause1219 (baseVal q)

theorem counterClause1220 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 1495 = false ∨ valuationOf q 1498 = true := by
  have hs : count1497 q = (countLit q [-18]) + (countLit q [-19, -21]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-19, -21])
  have hm := merge_two (literal (valuationOf q) (-18)) (literal (valuationOf q) (1495)) (literal (valuationOf q) (1498)) (countLit q [-18]) (countLit q [-19, -21]) (count1497 q) 1 1 (meaningNeg18 q) (meaning1495 q) (meaning1498 q) hs
  change (! (valuationOf q 18)) = false ∨ valuationOf q 1495 = false ∨ valuationOf q 1498 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1220 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 1495 = false ∨ valuation q 1498 = true := counterClause1220 (baseVal q)

theorem counterClause1221 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 1496 = false ∨ valuationOf q 1499 = true := by
  have hs : count1497 q = (countLit q [-18]) + (countLit q [-19, -21]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-19, -21])
  have hm := merge_two (literal (valuationOf q) (-18)) (literal (valuationOf q) (1496)) (literal (valuationOf q) (1499)) (countLit q [-18]) (countLit q [-19, -21]) (count1497 q) 1 2 (meaningNeg18 q) (meaning1496 q) (meaning1499 q) hs
  change (! (valuationOf q 18)) = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1499 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1221 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 1496 = false ∨ valuation q 1499 = true := counterClause1221 (baseVal q)

theorem counterClause1222 (q : Nat → Bool) : valuationOf q 26 = true ∨ valuationOf q 1500 = true := by
  have hs : count1500 q = (countLit q [-24]) + (countLit q [-26]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-26])
  have hm := merge_right (literal (valuationOf q) (-26)) (literal (valuationOf q) (1500)) (countLit q [-24]) (countLit q [-26]) (count1500 q) 1 (meaningNeg26 q) (meaning1500 q) hs
  change (! (valuationOf q 26)) = false ∨ valuationOf q 1500 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1222 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 1500 = true := counterClause1222 (baseVal q)

theorem counterClause1223 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 1500 = true := by
  have hs : count1500 q = (countLit q [-24]) + (countLit q [-26]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-26])
  have hm := merge_left (literal (valuationOf q) (-24)) (literal (valuationOf q) (1500)) (countLit q [-24]) (countLit q [-26]) (count1500 q) 1 (meaningNeg24 q) (meaning1500 q) hs
  change (! (valuationOf q 24)) = false ∨ valuationOf q 1500 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1223 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 1500 = true := counterClause1223 (baseVal q)

theorem counterClause1224 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 26 = true ∨ valuationOf q 1501 = true := by
  have hs : count1500 q = (countLit q [-24]) + (countLit q [-26]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-26])
  have hm := merge_two (literal (valuationOf q) (-24)) (literal (valuationOf q) (-26)) (literal (valuationOf q) (1501)) (countLit q [-24]) (countLit q [-26]) (count1500 q) 1 1 (meaningNeg24 q) (meaningNeg26 q) (meaning1501 q) hs
  change (! (valuationOf q 24)) = false ∨ (! (valuationOf q 26)) = false ∨ valuationOf q 1501 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1224 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 26 = true ∨ valuation q 1501 = true := counterClause1224 (baseVal q)

theorem counterClause1225 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 1502 = true := by
  have hs : count1502 q = (countLit q [-28]) + (countLit q [-31]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-31])
  have hm := merge_right (literal (valuationOf q) (-31)) (literal (valuationOf q) (1502)) (countLit q [-28]) (countLit q [-31]) (count1502 q) 1 (meaningNeg31 q) (meaning1502 q) hs
  change (! (valuationOf q 31)) = false ∨ valuationOf q 1502 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1225 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 1502 = true := counterClause1225 (baseVal q)

theorem counterClause1226 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 1502 = true := by
  have hs : count1502 q = (countLit q [-28]) + (countLit q [-31]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-31])
  have hm := merge_left (literal (valuationOf q) (-28)) (literal (valuationOf q) (1502)) (countLit q [-28]) (countLit q [-31]) (count1502 q) 1 (meaningNeg28 q) (meaning1502 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 1502 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1226 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 1502 = true := counterClause1226 (baseVal q)

theorem counterClause1227 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 31 = true ∨ valuationOf q 1503 = true := by
  have hs : count1502 q = (countLit q [-28]) + (countLit q [-31]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-31])
  have hm := merge_two (literal (valuationOf q) (-28)) (literal (valuationOf q) (-31)) (literal (valuationOf q) (1503)) (countLit q [-28]) (countLit q [-31]) (count1502 q) 1 1 (meaningNeg28 q) (meaningNeg31 q) (meaning1503 q) hs
  change (! (valuationOf q 28)) = false ∨ (! (valuationOf q 31)) = false ∨ valuationOf q 1503 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1227 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 31 = true ∨ valuation q 1503 = true := counterClause1227 (baseVal q)

theorem counterClause1228 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1504 = true := by
  have hs : count1504 q = (countLit q [-24, -26]) + (countLit q [-28, -31]) := List.countP_append (p := literal q) (l₁ := [-24, -26]) (l₂ := [-28, -31])
  have hm := merge_right (literal (valuationOf q) (1502)) (literal (valuationOf q) (1504)) (countLit q [-24, -26]) (countLit q [-28, -31]) (count1504 q) 1 (meaning1502 q) (meaning1504 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1504 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1228 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1504 = true := counterClause1228 (baseVal q)

theorem counterClause1229 (q : Nat → Bool) : valuationOf q 1503 = false ∨ valuationOf q 1505 = true := by
  have hs : count1504 q = (countLit q [-24, -26]) + (countLit q [-28, -31]) := List.countP_append (p := literal q) (l₁ := [-24, -26]) (l₂ := [-28, -31])
  have hm := merge_right (literal (valuationOf q) (1503)) (literal (valuationOf q) (1505)) (countLit q [-24, -26]) (countLit q [-28, -31]) (count1504 q) 2 (meaning1503 q) (meaning1505 q) hs
  change valuationOf q 1503 = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1229 (q : Snake 81) (h : Conditions q) : valuation q 1503 = false ∨ valuation q 1505 = true := counterClause1229 (baseVal q)

theorem counterClause1230 (q : Nat → Bool) : valuationOf q 1500 = false ∨ valuationOf q 1504 = true := by
  have hs : count1504 q = (countLit q [-24, -26]) + (countLit q [-28, -31]) := List.countP_append (p := literal q) (l₁ := [-24, -26]) (l₂ := [-28, -31])
  have hm := merge_left (literal (valuationOf q) (1500)) (literal (valuationOf q) (1504)) (countLit q [-24, -26]) (countLit q [-28, -31]) (count1504 q) 1 (meaning1500 q) (meaning1504 q) hs
  change valuationOf q 1500 = false ∨ valuationOf q 1504 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1230 (q : Snake 81) (h : Conditions q) : valuation q 1500 = false ∨ valuation q 1504 = true := counterClause1230 (baseVal q)

theorem counterClause1231 (q : Nat → Bool) : valuationOf q 1500 = false ∨ valuationOf q 1502 = false ∨ valuationOf q 1505 = true := by
  have hs : count1504 q = (countLit q [-24, -26]) + (countLit q [-28, -31]) := List.countP_append (p := literal q) (l₁ := [-24, -26]) (l₂ := [-28, -31])
  have hm := merge_two (literal (valuationOf q) (1500)) (literal (valuationOf q) (1502)) (literal (valuationOf q) (1505)) (countLit q [-24, -26]) (countLit q [-28, -31]) (count1504 q) 1 1 (meaning1500 q) (meaning1502 q) (meaning1505 q) hs
  change valuationOf q 1500 = false ∨ valuationOf q 1502 = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1231 (q : Snake 81) (h : Conditions q) : valuation q 1500 = false ∨ valuation q 1502 = false ∨ valuation q 1505 = true := counterClause1231 (baseVal q)

theorem counterClause1232 (q : Nat → Bool) : valuationOf q 1500 = false ∨ valuationOf q 1503 = false ∨ valuationOf q 1506 = true := by
  have hs : count1504 q = (countLit q [-24, -26]) + (countLit q [-28, -31]) := List.countP_append (p := literal q) (l₁ := [-24, -26]) (l₂ := [-28, -31])
  have hm := merge_two (literal (valuationOf q) (1500)) (literal (valuationOf q) (1503)) (literal (valuationOf q) (1506)) (countLit q [-24, -26]) (countLit q [-28, -31]) (count1504 q) 1 2 (meaning1500 q) (meaning1503 q) (meaning1506 q) hs
  change valuationOf q 1500 = false ∨ valuationOf q 1503 = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1232 (q : Snake 81) (h : Conditions q) : valuation q 1500 = false ∨ valuation q 1503 = false ∨ valuation q 1506 = true := counterClause1232 (baseVal q)

theorem counterClause1233 (q : Nat → Bool) : valuationOf q 1501 = false ∨ valuationOf q 1505 = true := by
  have hs : count1504 q = (countLit q [-24, -26]) + (countLit q [-28, -31]) := List.countP_append (p := literal q) (l₁ := [-24, -26]) (l₂ := [-28, -31])
  have hm := merge_left (literal (valuationOf q) (1501)) (literal (valuationOf q) (1505)) (countLit q [-24, -26]) (countLit q [-28, -31]) (count1504 q) 2 (meaning1501 q) (meaning1505 q) hs
  change valuationOf q 1501 = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1233 (q : Snake 81) (h : Conditions q) : valuation q 1501 = false ∨ valuation q 1505 = true := counterClause1233 (baseVal q)

theorem counterClause1234 (q : Nat → Bool) : valuationOf q 1501 = false ∨ valuationOf q 1502 = false ∨ valuationOf q 1506 = true := by
  have hs : count1504 q = (countLit q [-24, -26]) + (countLit q [-28, -31]) := List.countP_append (p := literal q) (l₁ := [-24, -26]) (l₂ := [-28, -31])
  have hm := merge_two (literal (valuationOf q) (1501)) (literal (valuationOf q) (1502)) (literal (valuationOf q) (1506)) (countLit q [-24, -26]) (countLit q [-28, -31]) (count1504 q) 2 1 (meaning1501 q) (meaning1502 q) (meaning1506 q) hs
  change valuationOf q 1501 = false ∨ valuationOf q 1502 = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1234 (q : Snake 81) (h : Conditions q) : valuation q 1501 = false ∨ valuation q 1502 = false ∨ valuation q 1506 = true := counterClause1234 (baseVal q)

theorem counterClause1235 (q : Nat → Bool) : valuationOf q 1501 = false ∨ valuationOf q 1503 = false ∨ valuationOf q 1507 = true := by
  have hs : count1504 q = (countLit q [-24, -26]) + (countLit q [-28, -31]) := List.countP_append (p := literal q) (l₁ := [-24, -26]) (l₂ := [-28, -31])
  have hm := merge_two (literal (valuationOf q) (1501)) (literal (valuationOf q) (1503)) (literal (valuationOf q) (1507)) (countLit q [-24, -26]) (countLit q [-28, -31]) (count1504 q) 2 2 (meaning1501 q) (meaning1503 q) (meaning1507 q) hs
  change valuationOf q 1501 = false ∨ valuationOf q 1503 = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1235 (q : Snake 81) (h : Conditions q) : valuation q 1501 = false ∨ valuation q 1503 = false ∨ valuation q 1507 = true := counterClause1235 (baseVal q)

theorem counterClause1236 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1508 = true := by
  have hs : count1508 q = (countLit q [-18, -19, -21]) + (countLit q [-24, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-18, -19, -21]) (l₂ := [-24, -26, -28, -31])
  have hm := merge_right (literal (valuationOf q) (1504)) (literal (valuationOf q) (1508)) (countLit q [-18, -19, -21]) (countLit q [-24, -26, -28, -31]) (count1508 q) 1 (meaning1504 q) (meaning1508 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1236 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1508 = true := counterClause1236 (baseVal q)

theorem counterClause1237 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1509 = true := by
  have hs : count1508 q = (countLit q [-18, -19, -21]) + (countLit q [-24, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-18, -19, -21]) (l₂ := [-24, -26, -28, -31])
  have hm := merge_right (literal (valuationOf q) (1505)) (literal (valuationOf q) (1509)) (countLit q [-18, -19, -21]) (countLit q [-24, -26, -28, -31]) (count1508 q) 2 (meaning1505 q) (meaning1509 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1237 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1509 = true := counterClause1237 (baseVal q)

theorem counterClause1238 (q : Nat → Bool) : valuationOf q 1506 = false ∨ valuationOf q 1510 = true := by
  have hs : count1508 q = (countLit q [-18, -19, -21]) + (countLit q [-24, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-18, -19, -21]) (l₂ := [-24, -26, -28, -31])
  have hm := merge_right (literal (valuationOf q) (1506)) (literal (valuationOf q) (1510)) (countLit q [-18, -19, -21]) (countLit q [-24, -26, -28, -31]) (count1508 q) 3 (meaning1506 q) (meaning1510 q) hs
  change valuationOf q 1506 = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1238 (q : Snake 81) (h : Conditions q) : valuation q 1506 = false ∨ valuation q 1510 = true := counterClause1238 (baseVal q)

theorem counterClause1239 (q : Nat → Bool) : valuationOf q 1497 = false ∨ valuationOf q 1508 = true := by
  have hs : count1508 q = (countLit q [-18, -19, -21]) + (countLit q [-24, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-18, -19, -21]) (l₂ := [-24, -26, -28, -31])
  have hm := merge_left (literal (valuationOf q) (1497)) (literal (valuationOf q) (1508)) (countLit q [-18, -19, -21]) (countLit q [-24, -26, -28, -31]) (count1508 q) 1 (meaning1497 q) (meaning1508 q) hs
  change valuationOf q 1497 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1239 (q : Snake 81) (h : Conditions q) : valuation q 1497 = false ∨ valuation q 1508 = true := counterClause1239 (baseVal q)

theorem counterClause1240 (q : Nat → Bool) : valuationOf q 1497 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1509 = true := by
  have hs : count1508 q = (countLit q [-18, -19, -21]) + (countLit q [-24, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-18, -19, -21]) (l₂ := [-24, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1497)) (literal (valuationOf q) (1504)) (literal (valuationOf q) (1509)) (countLit q [-18, -19, -21]) (countLit q [-24, -26, -28, -31]) (count1508 q) 1 1 (meaning1497 q) (meaning1504 q) (meaning1509 q) hs
  change valuationOf q 1497 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1240 (q : Snake 81) (h : Conditions q) : valuation q 1497 = false ∨ valuation q 1504 = false ∨ valuation q 1509 = true := counterClause1240 (baseVal q)

theorem counterClause1241 (q : Nat → Bool) : valuationOf q 1497 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1510 = true := by
  have hs : count1508 q = (countLit q [-18, -19, -21]) + (countLit q [-24, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-18, -19, -21]) (l₂ := [-24, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1497)) (literal (valuationOf q) (1505)) (literal (valuationOf q) (1510)) (countLit q [-18, -19, -21]) (countLit q [-24, -26, -28, -31]) (count1508 q) 1 2 (meaning1497 q) (meaning1505 q) (meaning1510 q) hs
  change valuationOf q 1497 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1241 (q : Snake 81) (h : Conditions q) : valuation q 1497 = false ∨ valuation q 1505 = false ∨ valuation q 1510 = true := counterClause1241 (baseVal q)

theorem counterClause1242 (q : Nat → Bool) : valuationOf q 1497 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1511 = true := by
  have hs : count1508 q = (countLit q [-18, -19, -21]) + (countLit q [-24, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-18, -19, -21]) (l₂ := [-24, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1497)) (literal (valuationOf q) (1506)) (literal (valuationOf q) (1511)) (countLit q [-18, -19, -21]) (countLit q [-24, -26, -28, -31]) (count1508 q) 1 3 (meaning1497 q) (meaning1506 q) (meaning1511 q) hs
  change valuationOf q 1497 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1242 (q : Snake 81) (h : Conditions q) : valuation q 1497 = false ∨ valuation q 1506 = false ∨ valuation q 1511 = true := counterClause1242 (baseVal q)

theorem counterClause1243 (q : Nat → Bool) : valuationOf q 1497 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1512 = true := by
  have hs : count1508 q = (countLit q [-18, -19, -21]) + (countLit q [-24, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-18, -19, -21]) (l₂ := [-24, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1497)) (literal (valuationOf q) (1507)) (literal (valuationOf q) (1512)) (countLit q [-18, -19, -21]) (countLit q [-24, -26, -28, -31]) (count1508 q) 1 4 (meaning1497 q) (meaning1507 q) (meaning1512 q) hs
  change valuationOf q 1497 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1243 (q : Snake 81) (h : Conditions q) : valuation q 1497 = false ∨ valuation q 1507 = false ∨ valuation q 1512 = true := counterClause1243 (baseVal q)

theorem counterClause1244 (q : Nat → Bool) : valuationOf q 1498 = false ∨ valuationOf q 1509 = true := by
  have hs : count1508 q = (countLit q [-18, -19, -21]) + (countLit q [-24, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-18, -19, -21]) (l₂ := [-24, -26, -28, -31])
  have hm := merge_left (literal (valuationOf q) (1498)) (literal (valuationOf q) (1509)) (countLit q [-18, -19, -21]) (countLit q [-24, -26, -28, -31]) (count1508 q) 2 (meaning1498 q) (meaning1509 q) hs
  change valuationOf q 1498 = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1244 (q : Snake 81) (h : Conditions q) : valuation q 1498 = false ∨ valuation q 1509 = true := counterClause1244 (baseVal q)

theorem counterClause1245 (q : Nat → Bool) : valuationOf q 1498 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1510 = true := by
  have hs : count1508 q = (countLit q [-18, -19, -21]) + (countLit q [-24, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-18, -19, -21]) (l₂ := [-24, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1498)) (literal (valuationOf q) (1504)) (literal (valuationOf q) (1510)) (countLit q [-18, -19, -21]) (countLit q [-24, -26, -28, -31]) (count1508 q) 2 1 (meaning1498 q) (meaning1504 q) (meaning1510 q) hs
  change valuationOf q 1498 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1245 (q : Snake 81) (h : Conditions q) : valuation q 1498 = false ∨ valuation q 1504 = false ∨ valuation q 1510 = true := counterClause1245 (baseVal q)

theorem counterClause1246 (q : Nat → Bool) : valuationOf q 1498 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1511 = true := by
  have hs : count1508 q = (countLit q [-18, -19, -21]) + (countLit q [-24, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-18, -19, -21]) (l₂ := [-24, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1498)) (literal (valuationOf q) (1505)) (literal (valuationOf q) (1511)) (countLit q [-18, -19, -21]) (countLit q [-24, -26, -28, -31]) (count1508 q) 2 2 (meaning1498 q) (meaning1505 q) (meaning1511 q) hs
  change valuationOf q 1498 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1246 (q : Snake 81) (h : Conditions q) : valuation q 1498 = false ∨ valuation q 1505 = false ∨ valuation q 1511 = true := counterClause1246 (baseVal q)

theorem counterClause1247 (q : Nat → Bool) : valuationOf q 1498 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1512 = true := by
  have hs : count1508 q = (countLit q [-18, -19, -21]) + (countLit q [-24, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-18, -19, -21]) (l₂ := [-24, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1498)) (literal (valuationOf q) (1506)) (literal (valuationOf q) (1512)) (countLit q [-18, -19, -21]) (countLit q [-24, -26, -28, -31]) (count1508 q) 2 3 (meaning1498 q) (meaning1506 q) (meaning1512 q) hs
  change valuationOf q 1498 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1247 (q : Snake 81) (h : Conditions q) : valuation q 1498 = false ∨ valuation q 1506 = false ∨ valuation q 1512 = true := counterClause1247 (baseVal q)

theorem counterClause1248 (q : Nat → Bool) : valuationOf q 1499 = false ∨ valuationOf q 1510 = true := by
  have hs : count1508 q = (countLit q [-18, -19, -21]) + (countLit q [-24, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-18, -19, -21]) (l₂ := [-24, -26, -28, -31])
  have hm := merge_left (literal (valuationOf q) (1499)) (literal (valuationOf q) (1510)) (countLit q [-18, -19, -21]) (countLit q [-24, -26, -28, -31]) (count1508 q) 3 (meaning1499 q) (meaning1510 q) hs
  change valuationOf q 1499 = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1248 (q : Snake 81) (h : Conditions q) : valuation q 1499 = false ∨ valuation q 1510 = true := counterClause1248 (baseVal q)

theorem block38 (q : Snake 81) (h : Conditions q) : B112E019.Block38 (valuation q) :=
  ⟨clause1217 q h, clause1218 q h, clause1219 q h, clause1220 q h, clause1221 q h, clause1222 q h, clause1223 q h, clause1224 q h, clause1225 q h, clause1226 q h, clause1227 q h, clause1228 q h, clause1229 q h, clause1230 q h, clause1231 q h, clause1232 q h, clause1233 q h, clause1234 q h, clause1235 q h, clause1236 q h, clause1237 q h, clause1238 q h, clause1239 q h, clause1240 q h, clause1241 q h, clause1242 q h, clause1243 q h, clause1244 q h, clause1245 q h, clause1246 q h, clause1247 q h, clause1248 q h⟩

end
end Snake9.Regrowth.E112019
