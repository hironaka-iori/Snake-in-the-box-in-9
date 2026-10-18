import E112050Semantics
import B112E050Inputs
namespace Snake9.Regrowth.E112050
noncomputable section
local instance blockDec37 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1185 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1596 = false ∨ valuationOf q 1610 = true := by
  have hs : count1602 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) + (countLit q [-13, -16, -18, -19, -21, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12]) (l₂ := [-13, -16, -18, -19, -21, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1575)) (literal (valuationOf q) (1596)) (literal (valuationOf q) (1610)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12]) (countLit q [-13, -16, -18, -19, -21, -25, -27, -28]) (count1602 q) 6 3 (meaning1575 q) (meaning1596 q) (meaning1610 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1596 = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1185 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1596 = false ∨ valuation q 1610 = true := counterClause1185 (baseVal q)

theorem counterClause1186 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 1618 = true := by
  have hs : count1618 q = (countLit q [-30]) + (countLit q [-33]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-33])
  have hm := merge_right (literal (valuationOf q) (-33)) (literal (valuationOf q) (1618)) (countLit q [-30]) (countLit q [-33]) (count1618 q) 1 (meaningNeg33 q) (meaning1618 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1186 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 1618 = true := counterClause1186 (baseVal q)

theorem counterClause1187 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 1618 = true := by
  have hs : count1618 q = (countLit q [-30]) + (countLit q [-33]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-33])
  have hm := merge_left (literal (valuationOf q) (-30)) (literal (valuationOf q) (1618)) (countLit q [-30]) (countLit q [-33]) (count1618 q) 1 (meaningNeg30 q) (meaning1618 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1187 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 1618 = true := counterClause1187 (baseVal q)

theorem counterClause1188 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 33 = true ∨ valuationOf q 1619 = true := by
  have hs : count1618 q = (countLit q [-30]) + (countLit q [-33]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-33])
  have hm := merge_two (literal (valuationOf q) (-30)) (literal (valuationOf q) (-33)) (literal (valuationOf q) (1619)) (countLit q [-30]) (countLit q [-33]) (count1618 q) 1 1 (meaningNeg30 q) (meaningNeg33 q) (meaning1619 q) hs
  change (! (valuationOf q 30)) = false ∨ (! (valuationOf q 33)) = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1188 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 33 = true ∨ valuation q 1619 = true := counterClause1188 (baseVal q)

theorem counterClause1189 (q : Nat → Bool) : valuationOf q 36 = true ∨ valuationOf q 1620 = true := by
  have hs : count1620 q = (countLit q [-35]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-36])
  have hm := merge_right (literal (valuationOf q) (-36)) (literal (valuationOf q) (1620)) (countLit q [-35]) (countLit q [-36]) (count1620 q) 1 (meaningNeg36 q) (meaning1620 q) hs
  change (! (valuationOf q 36)) = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1189 (q : Snake 81) (h : Conditions q) : valuation q 36 = true ∨ valuation q 1620 = true := counterClause1189 (baseVal q)

theorem counterClause1190 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 1620 = true := by
  have hs : count1620 q = (countLit q [-35]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-36])
  have hm := merge_left (literal (valuationOf q) (-35)) (literal (valuationOf q) (1620)) (countLit q [-35]) (countLit q [-36]) (count1620 q) 1 (meaningNeg35 q) (meaning1620 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1190 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1620 = true := counterClause1190 (baseVal q)

theorem counterClause1191 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 36 = true ∨ valuationOf q 1621 = true := by
  have hs : count1620 q = (countLit q [-35]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-36])
  have hm := merge_two (literal (valuationOf q) (-35)) (literal (valuationOf q) (-36)) (literal (valuationOf q) (1621)) (countLit q [-35]) (countLit q [-36]) (count1620 q) 1 1 (meaningNeg35 q) (meaningNeg36 q) (meaning1621 q) hs
  change (! (valuationOf q 35)) = false ∨ (! (valuationOf q 36)) = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1191 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 36 = true ∨ valuation q 1621 = true := counterClause1191 (baseVal q)

theorem counterClause1192 (q : Nat → Bool) : valuationOf q 1620 = false ∨ valuationOf q 1622 = true := by
  have hs : count1622 q = (countLit q [-30, -33]) + (countLit q [-35, -36]) := List.countP_append (p := literal q) (l₁ := [-30, -33]) (l₂ := [-35, -36])
  have hm := merge_right (literal (valuationOf q) (1620)) (literal (valuationOf q) (1622)) (countLit q [-30, -33]) (countLit q [-35, -36]) (count1622 q) 1 (meaning1620 q) (meaning1622 q) hs
  change valuationOf q 1620 = false ∨ valuationOf q 1622 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1192 (q : Snake 81) (h : Conditions q) : valuation q 1620 = false ∨ valuation q 1622 = true := counterClause1192 (baseVal q)

theorem counterClause1193 (q : Nat → Bool) : valuationOf q 1621 = false ∨ valuationOf q 1623 = true := by
  have hs : count1622 q = (countLit q [-30, -33]) + (countLit q [-35, -36]) := List.countP_append (p := literal q) (l₁ := [-30, -33]) (l₂ := [-35, -36])
  have hm := merge_right (literal (valuationOf q) (1621)) (literal (valuationOf q) (1623)) (countLit q [-30, -33]) (countLit q [-35, -36]) (count1622 q) 2 (meaning1621 q) (meaning1623 q) hs
  change valuationOf q 1621 = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1193 (q : Snake 81) (h : Conditions q) : valuation q 1621 = false ∨ valuation q 1623 = true := counterClause1193 (baseVal q)

theorem counterClause1194 (q : Nat → Bool) : valuationOf q 1618 = false ∨ valuationOf q 1622 = true := by
  have hs : count1622 q = (countLit q [-30, -33]) + (countLit q [-35, -36]) := List.countP_append (p := literal q) (l₁ := [-30, -33]) (l₂ := [-35, -36])
  have hm := merge_left (literal (valuationOf q) (1618)) (literal (valuationOf q) (1622)) (countLit q [-30, -33]) (countLit q [-35, -36]) (count1622 q) 1 (meaning1618 q) (meaning1622 q) hs
  change valuationOf q 1618 = false ∨ valuationOf q 1622 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1194 (q : Snake 81) (h : Conditions q) : valuation q 1618 = false ∨ valuation q 1622 = true := counterClause1194 (baseVal q)

theorem counterClause1195 (q : Nat → Bool) : valuationOf q 1618 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1623 = true := by
  have hs : count1622 q = (countLit q [-30, -33]) + (countLit q [-35, -36]) := List.countP_append (p := literal q) (l₁ := [-30, -33]) (l₂ := [-35, -36])
  have hm := merge_two (literal (valuationOf q) (1618)) (literal (valuationOf q) (1620)) (literal (valuationOf q) (1623)) (countLit q [-30, -33]) (countLit q [-35, -36]) (count1622 q) 1 1 (meaning1618 q) (meaning1620 q) (meaning1623 q) hs
  change valuationOf q 1618 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1195 (q : Snake 81) (h : Conditions q) : valuation q 1618 = false ∨ valuation q 1620 = false ∨ valuation q 1623 = true := counterClause1195 (baseVal q)

theorem counterClause1196 (q : Nat → Bool) : valuationOf q 1618 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1624 = true := by
  have hs : count1622 q = (countLit q [-30, -33]) + (countLit q [-35, -36]) := List.countP_append (p := literal q) (l₁ := [-30, -33]) (l₂ := [-35, -36])
  have hm := merge_two (literal (valuationOf q) (1618)) (literal (valuationOf q) (1621)) (literal (valuationOf q) (1624)) (countLit q [-30, -33]) (countLit q [-35, -36]) (count1622 q) 1 2 (meaning1618 q) (meaning1621 q) (meaning1624 q) hs
  change valuationOf q 1618 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1624 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1196 (q : Snake 81) (h : Conditions q) : valuation q 1618 = false ∨ valuation q 1621 = false ∨ valuation q 1624 = true := counterClause1196 (baseVal q)

theorem counterClause1197 (q : Nat → Bool) : valuationOf q 1619 = false ∨ valuationOf q 1623 = true := by
  have hs : count1622 q = (countLit q [-30, -33]) + (countLit q [-35, -36]) := List.countP_append (p := literal q) (l₁ := [-30, -33]) (l₂ := [-35, -36])
  have hm := merge_left (literal (valuationOf q) (1619)) (literal (valuationOf q) (1623)) (countLit q [-30, -33]) (countLit q [-35, -36]) (count1622 q) 2 (meaning1619 q) (meaning1623 q) hs
  change valuationOf q 1619 = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1197 (q : Snake 81) (h : Conditions q) : valuation q 1619 = false ∨ valuation q 1623 = true := counterClause1197 (baseVal q)

theorem counterClause1198 (q : Nat → Bool) : valuationOf q 1619 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1624 = true := by
  have hs : count1622 q = (countLit q [-30, -33]) + (countLit q [-35, -36]) := List.countP_append (p := literal q) (l₁ := [-30, -33]) (l₂ := [-35, -36])
  have hm := merge_two (literal (valuationOf q) (1619)) (literal (valuationOf q) (1620)) (literal (valuationOf q) (1624)) (countLit q [-30, -33]) (countLit q [-35, -36]) (count1622 q) 2 1 (meaning1619 q) (meaning1620 q) (meaning1624 q) hs
  change valuationOf q 1619 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1624 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1198 (q : Snake 81) (h : Conditions q) : valuation q 1619 = false ∨ valuation q 1620 = false ∨ valuation q 1624 = true := counterClause1198 (baseVal q)

theorem counterClause1199 (q : Nat → Bool) : valuationOf q 1619 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1625 = true := by
  have hs : count1622 q = (countLit q [-30, -33]) + (countLit q [-35, -36]) := List.countP_append (p := literal q) (l₁ := [-30, -33]) (l₂ := [-35, -36])
  have hm := merge_two (literal (valuationOf q) (1619)) (literal (valuationOf q) (1621)) (literal (valuationOf q) (1625)) (countLit q [-30, -33]) (countLit q [-35, -36]) (count1622 q) 2 2 (meaning1619 q) (meaning1621 q) (meaning1625 q) hs
  change valuationOf q 1619 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1199 (q : Snake 81) (h : Conditions q) : valuation q 1619 = false ∨ valuation q 1621 = false ∨ valuation q 1625 = true := counterClause1199 (baseVal q)

theorem counterClause1200 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 1626 = true := by
  have hs : count1626 q = (countLit q [-39]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-42])
  have hm := merge_right (literal (valuationOf q) (-42)) (literal (valuationOf q) (1626)) (countLit q [-39]) (countLit q [-42]) (count1626 q) 1 (meaningNeg42 q) (meaning1626 q) hs
  change (! (valuationOf q 42)) = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1200 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 1626 = true := counterClause1200 (baseVal q)

theorem counterClause1201 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 1626 = true := by
  have hs : count1626 q = (countLit q [-39]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-42])
  have hm := merge_left (literal (valuationOf q) (-39)) (literal (valuationOf q) (1626)) (countLit q [-39]) (countLit q [-42]) (count1626 q) 1 (meaningNeg39 q) (meaning1626 q) hs
  change (! (valuationOf q 39)) = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1201 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 1626 = true := counterClause1201 (baseVal q)

theorem counterClause1202 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 42 = true ∨ valuationOf q 1627 = true := by
  have hs : count1626 q = (countLit q [-39]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-42])
  have hm := merge_two (literal (valuationOf q) (-39)) (literal (valuationOf q) (-42)) (literal (valuationOf q) (1627)) (countLit q [-39]) (countLit q [-42]) (count1626 q) 1 1 (meaningNeg39 q) (meaningNeg42 q) (meaning1627 q) hs
  change (! (valuationOf q 39)) = false ∨ (! (valuationOf q 42)) = false ∨ valuationOf q 1627 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1202 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 42 = true ∨ valuation q 1627 = true := counterClause1202 (baseVal q)

theorem counterClause1203 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 1628 = true := by
  have hs : count1628 q = (countLit q [-43]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-45])
  have hm := merge_right (literal (valuationOf q) (-45)) (literal (valuationOf q) (1628)) (countLit q [-43]) (countLit q [-45]) (count1628 q) 1 (meaningNeg45 q) (meaning1628 q) hs
  change (! (valuationOf q 45)) = false ∨ valuationOf q 1628 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1203 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 1628 = true := counterClause1203 (baseVal q)

theorem counterClause1204 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 1628 = true := by
  have hs : count1628 q = (countLit q [-43]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-45])
  have hm := merge_left (literal (valuationOf q) (-43)) (literal (valuationOf q) (1628)) (countLit q [-43]) (countLit q [-45]) (count1628 q) 1 (meaningNeg43 q) (meaning1628 q) hs
  change (! (valuationOf q 43)) = false ∨ valuationOf q 1628 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1204 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 1628 = true := counterClause1204 (baseVal q)

theorem counterClause1205 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 45 = true ∨ valuationOf q 1629 = true := by
  have hs : count1628 q = (countLit q [-43]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-45])
  have hm := merge_two (literal (valuationOf q) (-43)) (literal (valuationOf q) (-45)) (literal (valuationOf q) (1629)) (countLit q [-43]) (countLit q [-45]) (count1628 q) 1 1 (meaningNeg43 q) (meaningNeg45 q) (meaning1629 q) hs
  change (! (valuationOf q 43)) = false ∨ (! (valuationOf q 45)) = false ∨ valuationOf q 1629 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1205 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 45 = true ∨ valuation q 1629 = true := counterClause1205 (baseVal q)

theorem counterClause1206 (q : Nat → Bool) : valuationOf q 1628 = false ∨ valuationOf q 1630 = true := by
  have hs : count1630 q = (countLit q [-39, -42]) + (countLit q [-43, -45]) := List.countP_append (p := literal q) (l₁ := [-39, -42]) (l₂ := [-43, -45])
  have hm := merge_right (literal (valuationOf q) (1628)) (literal (valuationOf q) (1630)) (countLit q [-39, -42]) (countLit q [-43, -45]) (count1630 q) 1 (meaning1628 q) (meaning1630 q) hs
  change valuationOf q 1628 = false ∨ valuationOf q 1630 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1206 (q : Snake 81) (h : Conditions q) : valuation q 1628 = false ∨ valuation q 1630 = true := counterClause1206 (baseVal q)

theorem counterClause1207 (q : Nat → Bool) : valuationOf q 1629 = false ∨ valuationOf q 1631 = true := by
  have hs : count1630 q = (countLit q [-39, -42]) + (countLit q [-43, -45]) := List.countP_append (p := literal q) (l₁ := [-39, -42]) (l₂ := [-43, -45])
  have hm := merge_right (literal (valuationOf q) (1629)) (literal (valuationOf q) (1631)) (countLit q [-39, -42]) (countLit q [-43, -45]) (count1630 q) 2 (meaning1629 q) (meaning1631 q) hs
  change valuationOf q 1629 = false ∨ valuationOf q 1631 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1207 (q : Snake 81) (h : Conditions q) : valuation q 1629 = false ∨ valuation q 1631 = true := counterClause1207 (baseVal q)

theorem counterClause1208 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1630 = true := by
  have hs : count1630 q = (countLit q [-39, -42]) + (countLit q [-43, -45]) := List.countP_append (p := literal q) (l₁ := [-39, -42]) (l₂ := [-43, -45])
  have hm := merge_left (literal (valuationOf q) (1626)) (literal (valuationOf q) (1630)) (countLit q [-39, -42]) (countLit q [-43, -45]) (count1630 q) 1 (meaning1626 q) (meaning1630 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1630 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1208 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1630 = true := counterClause1208 (baseVal q)

theorem counterClause1209 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1631 = true := by
  have hs : count1630 q = (countLit q [-39, -42]) + (countLit q [-43, -45]) := List.countP_append (p := literal q) (l₁ := [-39, -42]) (l₂ := [-43, -45])
  have hm := merge_two (literal (valuationOf q) (1626)) (literal (valuationOf q) (1628)) (literal (valuationOf q) (1631)) (countLit q [-39, -42]) (countLit q [-43, -45]) (count1630 q) 1 1 (meaning1626 q) (meaning1628 q) (meaning1631 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1631 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1209 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1628 = false ∨ valuation q 1631 = true := counterClause1209 (baseVal q)

theorem counterClause1210 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1629 = false ∨ valuationOf q 1632 = true := by
  have hs : count1630 q = (countLit q [-39, -42]) + (countLit q [-43, -45]) := List.countP_append (p := literal q) (l₁ := [-39, -42]) (l₂ := [-43, -45])
  have hm := merge_two (literal (valuationOf q) (1626)) (literal (valuationOf q) (1629)) (literal (valuationOf q) (1632)) (countLit q [-39, -42]) (countLit q [-43, -45]) (count1630 q) 1 2 (meaning1626 q) (meaning1629 q) (meaning1632 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1629 = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1210 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1629 = false ∨ valuation q 1632 = true := counterClause1210 (baseVal q)

theorem counterClause1211 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1631 = true := by
  have hs : count1630 q = (countLit q [-39, -42]) + (countLit q [-43, -45]) := List.countP_append (p := literal q) (l₁ := [-39, -42]) (l₂ := [-43, -45])
  have hm := merge_left (literal (valuationOf q) (1627)) (literal (valuationOf q) (1631)) (countLit q [-39, -42]) (countLit q [-43, -45]) (count1630 q) 2 (meaning1627 q) (meaning1631 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1631 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1211 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1631 = true := counterClause1211 (baseVal q)

theorem counterClause1212 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1632 = true := by
  have hs : count1630 q = (countLit q [-39, -42]) + (countLit q [-43, -45]) := List.countP_append (p := literal q) (l₁ := [-39, -42]) (l₂ := [-43, -45])
  have hm := merge_two (literal (valuationOf q) (1627)) (literal (valuationOf q) (1628)) (literal (valuationOf q) (1632)) (countLit q [-39, -42]) (countLit q [-43, -45]) (count1630 q) 2 1 (meaning1627 q) (meaning1628 q) (meaning1632 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1212 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1628 = false ∨ valuation q 1632 = true := counterClause1212 (baseVal q)

theorem counterClause1213 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1629 = false ∨ valuationOf q 1633 = true := by
  have hs : count1630 q = (countLit q [-39, -42]) + (countLit q [-43, -45]) := List.countP_append (p := literal q) (l₁ := [-39, -42]) (l₂ := [-43, -45])
  have hm := merge_two (literal (valuationOf q) (1627)) (literal (valuationOf q) (1629)) (literal (valuationOf q) (1633)) (countLit q [-39, -42]) (countLit q [-43, -45]) (count1630 q) 2 2 (meaning1627 q) (meaning1629 q) (meaning1633 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1629 = false ∨ valuationOf q 1633 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1213 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1629 = false ∨ valuation q 1633 = true := counterClause1213 (baseVal q)

theorem counterClause1214 (q : Nat → Bool) : valuationOf q 1630 = false ∨ valuationOf q 1634 = true := by
  have hs : count1634 q = (countLit q [-30, -33, -35, -36]) + (countLit q [-39, -42, -43, -45]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36]) (l₂ := [-39, -42, -43, -45])
  have hm := merge_right (literal (valuationOf q) (1630)) (literal (valuationOf q) (1634)) (countLit q [-30, -33, -35, -36]) (countLit q [-39, -42, -43, -45]) (count1634 q) 1 (meaning1630 q) (meaning1634 q) hs
  change valuationOf q 1630 = false ∨ valuationOf q 1634 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1214 (q : Snake 81) (h : Conditions q) : valuation q 1630 = false ∨ valuation q 1634 = true := counterClause1214 (baseVal q)

theorem counterClause1215 (q : Nat → Bool) : valuationOf q 1631 = false ∨ valuationOf q 1635 = true := by
  have hs : count1634 q = (countLit q [-30, -33, -35, -36]) + (countLit q [-39, -42, -43, -45]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36]) (l₂ := [-39, -42, -43, -45])
  have hm := merge_right (literal (valuationOf q) (1631)) (literal (valuationOf q) (1635)) (countLit q [-30, -33, -35, -36]) (countLit q [-39, -42, -43, -45]) (count1634 q) 2 (meaning1631 q) (meaning1635 q) hs
  change valuationOf q 1631 = false ∨ valuationOf q 1635 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1215 (q : Snake 81) (h : Conditions q) : valuation q 1631 = false ∨ valuation q 1635 = true := counterClause1215 (baseVal q)

theorem counterClause1216 (q : Nat → Bool) : valuationOf q 1632 = false ∨ valuationOf q 1636 = true := by
  have hs : count1634 q = (countLit q [-30, -33, -35, -36]) + (countLit q [-39, -42, -43, -45]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36]) (l₂ := [-39, -42, -43, -45])
  have hm := merge_right (literal (valuationOf q) (1632)) (literal (valuationOf q) (1636)) (countLit q [-30, -33, -35, -36]) (countLit q [-39, -42, -43, -45]) (count1634 q) 3 (meaning1632 q) (meaning1636 q) hs
  change valuationOf q 1632 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1216 (q : Snake 81) (h : Conditions q) : valuation q 1632 = false ∨ valuation q 1636 = true := counterClause1216 (baseVal q)

theorem block37 (q : Snake 81) (h : Conditions q) : B112E050.Block37 (valuation q) :=
  ⟨clause1185 q h, clause1186 q h, clause1187 q h, clause1188 q h, clause1189 q h, clause1190 q h, clause1191 q h, clause1192 q h, clause1193 q h, clause1194 q h, clause1195 q h, clause1196 q h, clause1197 q h, clause1198 q h, clause1199 q h, clause1200 q h, clause1201 q h, clause1202 q h, clause1203 q h, clause1204 q h, clause1205 q h, clause1206 q h, clause1207 q h, clause1208 q h, clause1209 q h, clause1210 q h, clause1211 q h, clause1212 q h, clause1213 q h, clause1214 q h, clause1215 q h, clause1216 q h⟩

end
end Snake9.Regrowth.E112050
