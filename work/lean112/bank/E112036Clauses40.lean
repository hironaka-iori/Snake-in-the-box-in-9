import E112036Semantics
import B112E036Inputs
namespace Snake9.Regrowth.E112036
noncomputable section
local instance blockDec40 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1281 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 1707 = true := by
  have hs : count1707 q = (countLit q [-63]) + (countLit q [-64]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-64])
  have hm := merge_left (literal (valuationOf q) (-63)) (literal (valuationOf q) (1707)) (countLit q [-63]) (countLit q [-64]) (count1707 q) 1 (meaningNeg63 q) (meaning1707 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 1707 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1281 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 1707 = true := counterClause1281 (baseVal q)

theorem counterClause1282 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 64 = true ∨ valuationOf q 1708 = true := by
  have hs : count1707 q = (countLit q [-63]) + (countLit q [-64]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-64])
  have hm := merge_two (literal (valuationOf q) (-63)) (literal (valuationOf q) (-64)) (literal (valuationOf q) (1708)) (countLit q [-63]) (countLit q [-64]) (count1707 q) 1 1 (meaningNeg63 q) (meaningNeg64 q) (meaning1708 q) hs
  change (! (valuationOf q 63)) = false ∨ (! (valuationOf q 64)) = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1282 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 64 = true ∨ valuation q 1708 = true := counterClause1282 (baseVal q)

theorem counterClause1283 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 1709 = true := by
  have hs : count1709 q = (countLit q [-67]) + (countLit q [-70]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-70])
  have hm := merge_right (literal (valuationOf q) (-70)) (literal (valuationOf q) (1709)) (countLit q [-67]) (countLit q [-70]) (count1709 q) 1 (meaningNeg70 q) (meaning1709 q) hs
  change (! (valuationOf q 70)) = false ∨ valuationOf q 1709 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1283 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 1709 = true := counterClause1283 (baseVal q)

theorem counterClause1284 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 1709 = true := by
  have hs : count1709 q = (countLit q [-67]) + (countLit q [-70]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-70])
  have hm := merge_left (literal (valuationOf q) (-67)) (literal (valuationOf q) (1709)) (countLit q [-67]) (countLit q [-70]) (count1709 q) 1 (meaningNeg67 q) (meaning1709 q) hs
  change (! (valuationOf q 67)) = false ∨ valuationOf q 1709 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1284 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 1709 = true := counterClause1284 (baseVal q)

theorem counterClause1285 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 70 = true ∨ valuationOf q 1710 = true := by
  have hs : count1709 q = (countLit q [-67]) + (countLit q [-70]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-70])
  have hm := merge_two (literal (valuationOf q) (-67)) (literal (valuationOf q) (-70)) (literal (valuationOf q) (1710)) (countLit q [-67]) (countLit q [-70]) (count1709 q) 1 1 (meaningNeg67 q) (meaningNeg70 q) (meaning1710 q) hs
  change (! (valuationOf q 67)) = false ∨ (! (valuationOf q 70)) = false ∨ valuationOf q 1710 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1285 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 70 = true ∨ valuation q 1710 = true := counterClause1285 (baseVal q)

theorem counterClause1286 (q : Nat → Bool) : valuationOf q 1709 = false ∨ valuationOf q 1711 = true := by
  have hs : count1711 q = (countLit q [-63, -64]) + (countLit q [-67, -70]) := List.countP_append (p := literal q) (l₁ := [-63, -64]) (l₂ := [-67, -70])
  have hm := merge_right (literal (valuationOf q) (1709)) (literal (valuationOf q) (1711)) (countLit q [-63, -64]) (countLit q [-67, -70]) (count1711 q) 1 (meaning1709 q) (meaning1711 q) hs
  change valuationOf q 1709 = false ∨ valuationOf q 1711 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1286 (q : Snake 81) (h : Conditions q) : valuation q 1709 = false ∨ valuation q 1711 = true := counterClause1286 (baseVal q)

theorem counterClause1287 (q : Nat → Bool) : valuationOf q 1710 = false ∨ valuationOf q 1712 = true := by
  have hs : count1711 q = (countLit q [-63, -64]) + (countLit q [-67, -70]) := List.countP_append (p := literal q) (l₁ := [-63, -64]) (l₂ := [-67, -70])
  have hm := merge_right (literal (valuationOf q) (1710)) (literal (valuationOf q) (1712)) (countLit q [-63, -64]) (countLit q [-67, -70]) (count1711 q) 2 (meaning1710 q) (meaning1712 q) hs
  change valuationOf q 1710 = false ∨ valuationOf q 1712 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1287 (q : Snake 81) (h : Conditions q) : valuation q 1710 = false ∨ valuation q 1712 = true := counterClause1287 (baseVal q)

theorem counterClause1288 (q : Nat → Bool) : valuationOf q 1707 = false ∨ valuationOf q 1711 = true := by
  have hs : count1711 q = (countLit q [-63, -64]) + (countLit q [-67, -70]) := List.countP_append (p := literal q) (l₁ := [-63, -64]) (l₂ := [-67, -70])
  have hm := merge_left (literal (valuationOf q) (1707)) (literal (valuationOf q) (1711)) (countLit q [-63, -64]) (countLit q [-67, -70]) (count1711 q) 1 (meaning1707 q) (meaning1711 q) hs
  change valuationOf q 1707 = false ∨ valuationOf q 1711 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1288 (q : Snake 81) (h : Conditions q) : valuation q 1707 = false ∨ valuation q 1711 = true := counterClause1288 (baseVal q)

theorem counterClause1289 (q : Nat → Bool) : valuationOf q 1707 = false ∨ valuationOf q 1709 = false ∨ valuationOf q 1712 = true := by
  have hs : count1711 q = (countLit q [-63, -64]) + (countLit q [-67, -70]) := List.countP_append (p := literal q) (l₁ := [-63, -64]) (l₂ := [-67, -70])
  have hm := merge_two (literal (valuationOf q) (1707)) (literal (valuationOf q) (1709)) (literal (valuationOf q) (1712)) (countLit q [-63, -64]) (countLit q [-67, -70]) (count1711 q) 1 1 (meaning1707 q) (meaning1709 q) (meaning1712 q) hs
  change valuationOf q 1707 = false ∨ valuationOf q 1709 = false ∨ valuationOf q 1712 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1289 (q : Snake 81) (h : Conditions q) : valuation q 1707 = false ∨ valuation q 1709 = false ∨ valuation q 1712 = true := counterClause1289 (baseVal q)

theorem counterClause1290 (q : Nat → Bool) : valuationOf q 1707 = false ∨ valuationOf q 1710 = false ∨ valuationOf q 1713 = true := by
  have hs : count1711 q = (countLit q [-63, -64]) + (countLit q [-67, -70]) := List.countP_append (p := literal q) (l₁ := [-63, -64]) (l₂ := [-67, -70])
  have hm := merge_two (literal (valuationOf q) (1707)) (literal (valuationOf q) (1710)) (literal (valuationOf q) (1713)) (countLit q [-63, -64]) (countLit q [-67, -70]) (count1711 q) 1 2 (meaning1707 q) (meaning1710 q) (meaning1713 q) hs
  change valuationOf q 1707 = false ∨ valuationOf q 1710 = false ∨ valuationOf q 1713 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1290 (q : Snake 81) (h : Conditions q) : valuation q 1707 = false ∨ valuation q 1710 = false ∨ valuation q 1713 = true := counterClause1290 (baseVal q)

theorem counterClause1291 (q : Nat → Bool) : valuationOf q 1708 = false ∨ valuationOf q 1712 = true := by
  have hs : count1711 q = (countLit q [-63, -64]) + (countLit q [-67, -70]) := List.countP_append (p := literal q) (l₁ := [-63, -64]) (l₂ := [-67, -70])
  have hm := merge_left (literal (valuationOf q) (1708)) (literal (valuationOf q) (1712)) (countLit q [-63, -64]) (countLit q [-67, -70]) (count1711 q) 2 (meaning1708 q) (meaning1712 q) hs
  change valuationOf q 1708 = false ∨ valuationOf q 1712 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1291 (q : Snake 81) (h : Conditions q) : valuation q 1708 = false ∨ valuation q 1712 = true := counterClause1291 (baseVal q)

theorem counterClause1292 (q : Nat → Bool) : valuationOf q 1708 = false ∨ valuationOf q 1709 = false ∨ valuationOf q 1713 = true := by
  have hs : count1711 q = (countLit q [-63, -64]) + (countLit q [-67, -70]) := List.countP_append (p := literal q) (l₁ := [-63, -64]) (l₂ := [-67, -70])
  have hm := merge_two (literal (valuationOf q) (1708)) (literal (valuationOf q) (1709)) (literal (valuationOf q) (1713)) (countLit q [-63, -64]) (countLit q [-67, -70]) (count1711 q) 2 1 (meaning1708 q) (meaning1709 q) (meaning1713 q) hs
  change valuationOf q 1708 = false ∨ valuationOf q 1709 = false ∨ valuationOf q 1713 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1292 (q : Snake 81) (h : Conditions q) : valuation q 1708 = false ∨ valuation q 1709 = false ∨ valuation q 1713 = true := counterClause1292 (baseVal q)

theorem counterClause1293 (q : Nat → Bool) : valuationOf q 1708 = false ∨ valuationOf q 1710 = false ∨ valuationOf q 1714 = true := by
  have hs : count1711 q = (countLit q [-63, -64]) + (countLit q [-67, -70]) := List.countP_append (p := literal q) (l₁ := [-63, -64]) (l₂ := [-67, -70])
  have hm := merge_two (literal (valuationOf q) (1708)) (literal (valuationOf q) (1710)) (literal (valuationOf q) (1714)) (countLit q [-63, -64]) (countLit q [-67, -70]) (count1711 q) 2 2 (meaning1708 q) (meaning1710 q) (meaning1714 q) hs
  change valuationOf q 1708 = false ∨ valuationOf q 1710 = false ∨ valuationOf q 1714 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1293 (q : Snake 81) (h : Conditions q) : valuation q 1708 = false ∨ valuation q 1710 = false ∨ valuation q 1714 = true := counterClause1293 (baseVal q)

theorem counterClause1294 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 1715 = true := by
  have hs : count1715 q = (countLit q [-72]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-73])
  have hm := merge_right (literal (valuationOf q) (-73)) (literal (valuationOf q) (1715)) (countLit q [-72]) (countLit q [-73]) (count1715 q) 1 (meaningNeg73 q) (meaning1715 q) hs
  change (! (valuationOf q 73)) = false ∨ valuationOf q 1715 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1294 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 1715 = true := counterClause1294 (baseVal q)

theorem counterClause1295 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 1715 = true := by
  have hs : count1715 q = (countLit q [-72]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-73])
  have hm := merge_left (literal (valuationOf q) (-72)) (literal (valuationOf q) (1715)) (countLit q [-72]) (countLit q [-73]) (count1715 q) 1 (meaningNeg72 q) (meaning1715 q) hs
  change (! (valuationOf q 72)) = false ∨ valuationOf q 1715 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1295 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 1715 = true := counterClause1295 (baseVal q)

theorem counterClause1296 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 73 = true ∨ valuationOf q 1716 = true := by
  have hs : count1715 q = (countLit q [-72]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-73])
  have hm := merge_two (literal (valuationOf q) (-72)) (literal (valuationOf q) (-73)) (literal (valuationOf q) (1716)) (countLit q [-72]) (countLit q [-73]) (count1715 q) 1 1 (meaningNeg72 q) (meaningNeg73 q) (meaning1716 q) hs
  change (! (valuationOf q 72)) = false ∨ (! (valuationOf q 73)) = false ∨ valuationOf q 1716 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1296 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 73 = true ∨ valuation q 1716 = true := counterClause1296 (baseVal q)

theorem counterClause1297 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 1717 = true := by
  have hs : count1717 q = (countLit q [-75]) + (countLit q [-76]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-76])
  have hm := merge_right (literal (valuationOf q) (-76)) (literal (valuationOf q) (1717)) (countLit q [-75]) (countLit q [-76]) (count1717 q) 1 (meaningNeg76 q) (meaning1717 q) hs
  change (! (valuationOf q 76)) = false ∨ valuationOf q 1717 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1297 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 1717 = true := counterClause1297 (baseVal q)

theorem counterClause1298 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 1717 = true := by
  have hs : count1717 q = (countLit q [-75]) + (countLit q [-76]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-76])
  have hm := merge_left (literal (valuationOf q) (-75)) (literal (valuationOf q) (1717)) (countLit q [-75]) (countLit q [-76]) (count1717 q) 1 (meaningNeg75 q) (meaning1717 q) hs
  change (! (valuationOf q 75)) = false ∨ valuationOf q 1717 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1298 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 1717 = true := counterClause1298 (baseVal q)

theorem counterClause1299 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 76 = true ∨ valuationOf q 1718 = true := by
  have hs : count1717 q = (countLit q [-75]) + (countLit q [-76]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-76])
  have hm := merge_two (literal (valuationOf q) (-75)) (literal (valuationOf q) (-76)) (literal (valuationOf q) (1718)) (countLit q [-75]) (countLit q [-76]) (count1717 q) 1 1 (meaningNeg75 q) (meaningNeg76 q) (meaning1718 q) hs
  change (! (valuationOf q 75)) = false ∨ (! (valuationOf q 76)) = false ∨ valuationOf q 1718 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1299 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 76 = true ∨ valuation q 1718 = true := counterClause1299 (baseVal q)

theorem counterClause1300 (q : Nat → Bool) : valuationOf q 1717 = false ∨ valuationOf q 1719 = true := by
  have hs : count1719 q = (countLit q [-72, -73]) + (countLit q [-75, -76]) := List.countP_append (p := literal q) (l₁ := [-72, -73]) (l₂ := [-75, -76])
  have hm := merge_right (literal (valuationOf q) (1717)) (literal (valuationOf q) (1719)) (countLit q [-72, -73]) (countLit q [-75, -76]) (count1719 q) 1 (meaning1717 q) (meaning1719 q) hs
  change valuationOf q 1717 = false ∨ valuationOf q 1719 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1300 (q : Snake 81) (h : Conditions q) : valuation q 1717 = false ∨ valuation q 1719 = true := counterClause1300 (baseVal q)

theorem counterClause1301 (q : Nat → Bool) : valuationOf q 1718 = false ∨ valuationOf q 1720 = true := by
  have hs : count1719 q = (countLit q [-72, -73]) + (countLit q [-75, -76]) := List.countP_append (p := literal q) (l₁ := [-72, -73]) (l₂ := [-75, -76])
  have hm := merge_right (literal (valuationOf q) (1718)) (literal (valuationOf q) (1720)) (countLit q [-72, -73]) (countLit q [-75, -76]) (count1719 q) 2 (meaning1718 q) (meaning1720 q) hs
  change valuationOf q 1718 = false ∨ valuationOf q 1720 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1301 (q : Snake 81) (h : Conditions q) : valuation q 1718 = false ∨ valuation q 1720 = true := counterClause1301 (baseVal q)

theorem counterClause1302 (q : Nat → Bool) : valuationOf q 1715 = false ∨ valuationOf q 1719 = true := by
  have hs : count1719 q = (countLit q [-72, -73]) + (countLit q [-75, -76]) := List.countP_append (p := literal q) (l₁ := [-72, -73]) (l₂ := [-75, -76])
  have hm := merge_left (literal (valuationOf q) (1715)) (literal (valuationOf q) (1719)) (countLit q [-72, -73]) (countLit q [-75, -76]) (count1719 q) 1 (meaning1715 q) (meaning1719 q) hs
  change valuationOf q 1715 = false ∨ valuationOf q 1719 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1302 (q : Snake 81) (h : Conditions q) : valuation q 1715 = false ∨ valuation q 1719 = true := counterClause1302 (baseVal q)

theorem counterClause1303 (q : Nat → Bool) : valuationOf q 1715 = false ∨ valuationOf q 1717 = false ∨ valuationOf q 1720 = true := by
  have hs : count1719 q = (countLit q [-72, -73]) + (countLit q [-75, -76]) := List.countP_append (p := literal q) (l₁ := [-72, -73]) (l₂ := [-75, -76])
  have hm := merge_two (literal (valuationOf q) (1715)) (literal (valuationOf q) (1717)) (literal (valuationOf q) (1720)) (countLit q [-72, -73]) (countLit q [-75, -76]) (count1719 q) 1 1 (meaning1715 q) (meaning1717 q) (meaning1720 q) hs
  change valuationOf q 1715 = false ∨ valuationOf q 1717 = false ∨ valuationOf q 1720 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1303 (q : Snake 81) (h : Conditions q) : valuation q 1715 = false ∨ valuation q 1717 = false ∨ valuation q 1720 = true := counterClause1303 (baseVal q)

theorem counterClause1304 (q : Nat → Bool) : valuationOf q 1715 = false ∨ valuationOf q 1718 = false ∨ valuationOf q 1721 = true := by
  have hs : count1719 q = (countLit q [-72, -73]) + (countLit q [-75, -76]) := List.countP_append (p := literal q) (l₁ := [-72, -73]) (l₂ := [-75, -76])
  have hm := merge_two (literal (valuationOf q) (1715)) (literal (valuationOf q) (1718)) (literal (valuationOf q) (1721)) (countLit q [-72, -73]) (countLit q [-75, -76]) (count1719 q) 1 2 (meaning1715 q) (meaning1718 q) (meaning1721 q) hs
  change valuationOf q 1715 = false ∨ valuationOf q 1718 = false ∨ valuationOf q 1721 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1304 (q : Snake 81) (h : Conditions q) : valuation q 1715 = false ∨ valuation q 1718 = false ∨ valuation q 1721 = true := counterClause1304 (baseVal q)

theorem counterClause1305 (q : Nat → Bool) : valuationOf q 1716 = false ∨ valuationOf q 1720 = true := by
  have hs : count1719 q = (countLit q [-72, -73]) + (countLit q [-75, -76]) := List.countP_append (p := literal q) (l₁ := [-72, -73]) (l₂ := [-75, -76])
  have hm := merge_left (literal (valuationOf q) (1716)) (literal (valuationOf q) (1720)) (countLit q [-72, -73]) (countLit q [-75, -76]) (count1719 q) 2 (meaning1716 q) (meaning1720 q) hs
  change valuationOf q 1716 = false ∨ valuationOf q 1720 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1305 (q : Snake 81) (h : Conditions q) : valuation q 1716 = false ∨ valuation q 1720 = true := counterClause1305 (baseVal q)

theorem counterClause1306 (q : Nat → Bool) : valuationOf q 1716 = false ∨ valuationOf q 1717 = false ∨ valuationOf q 1721 = true := by
  have hs : count1719 q = (countLit q [-72, -73]) + (countLit q [-75, -76]) := List.countP_append (p := literal q) (l₁ := [-72, -73]) (l₂ := [-75, -76])
  have hm := merge_two (literal (valuationOf q) (1716)) (literal (valuationOf q) (1717)) (literal (valuationOf q) (1721)) (countLit q [-72, -73]) (countLit q [-75, -76]) (count1719 q) 2 1 (meaning1716 q) (meaning1717 q) (meaning1721 q) hs
  change valuationOf q 1716 = false ∨ valuationOf q 1717 = false ∨ valuationOf q 1721 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1306 (q : Snake 81) (h : Conditions q) : valuation q 1716 = false ∨ valuation q 1717 = false ∨ valuation q 1721 = true := counterClause1306 (baseVal q)

theorem counterClause1307 (q : Nat → Bool) : valuationOf q 1719 = false ∨ valuationOf q 1723 = true := by
  have hs : count1723 q = (countLit q [-63, -64, -67, -70]) + (countLit q [-72, -73, -75, -76]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70]) (l₂ := [-72, -73, -75, -76])
  have hm := merge_right (literal (valuationOf q) (1719)) (literal (valuationOf q) (1723)) (countLit q [-63, -64, -67, -70]) (countLit q [-72, -73, -75, -76]) (count1723 q) 1 (meaning1719 q) (meaning1723 q) hs
  change valuationOf q 1719 = false ∨ valuationOf q 1723 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1307 (q : Snake 81) (h : Conditions q) : valuation q 1719 = false ∨ valuation q 1723 = true := counterClause1307 (baseVal q)

theorem counterClause1308 (q : Nat → Bool) : valuationOf q 1720 = false ∨ valuationOf q 1724 = true := by
  have hs : count1723 q = (countLit q [-63, -64, -67, -70]) + (countLit q [-72, -73, -75, -76]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70]) (l₂ := [-72, -73, -75, -76])
  have hm := merge_right (literal (valuationOf q) (1720)) (literal (valuationOf q) (1724)) (countLit q [-63, -64, -67, -70]) (countLit q [-72, -73, -75, -76]) (count1723 q) 2 (meaning1720 q) (meaning1724 q) hs
  change valuationOf q 1720 = false ∨ valuationOf q 1724 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1308 (q : Snake 81) (h : Conditions q) : valuation q 1720 = false ∨ valuation q 1724 = true := counterClause1308 (baseVal q)

theorem counterClause1309 (q : Nat → Bool) : valuationOf q 1721 = false ∨ valuationOf q 1725 = true := by
  have hs : count1723 q = (countLit q [-63, -64, -67, -70]) + (countLit q [-72, -73, -75, -76]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70]) (l₂ := [-72, -73, -75, -76])
  have hm := merge_right (literal (valuationOf q) (1721)) (literal (valuationOf q) (1725)) (countLit q [-63, -64, -67, -70]) (countLit q [-72, -73, -75, -76]) (count1723 q) 3 (meaning1721 q) (meaning1725 q) hs
  change valuationOf q 1721 = false ∨ valuationOf q 1725 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1309 (q : Snake 81) (h : Conditions q) : valuation q 1721 = false ∨ valuation q 1725 = true := counterClause1309 (baseVal q)

theorem counterClause1310 (q : Nat → Bool) : valuationOf q 1711 = false ∨ valuationOf q 1719 = false ∨ valuationOf q 1724 = true := by
  have hs : count1723 q = (countLit q [-63, -64, -67, -70]) + (countLit q [-72, -73, -75, -76]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70]) (l₂ := [-72, -73, -75, -76])
  have hm := merge_two (literal (valuationOf q) (1711)) (literal (valuationOf q) (1719)) (literal (valuationOf q) (1724)) (countLit q [-63, -64, -67, -70]) (countLit q [-72, -73, -75, -76]) (count1723 q) 1 1 (meaning1711 q) (meaning1719 q) (meaning1724 q) hs
  change valuationOf q 1711 = false ∨ valuationOf q 1719 = false ∨ valuationOf q 1724 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1310 (q : Snake 81) (h : Conditions q) : valuation q 1711 = false ∨ valuation q 1719 = false ∨ valuation q 1724 = true := counterClause1310 (baseVal q)

theorem counterClause1311 (q : Nat → Bool) : valuationOf q 1711 = false ∨ valuationOf q 1720 = false ∨ valuationOf q 1725 = true := by
  have hs : count1723 q = (countLit q [-63, -64, -67, -70]) + (countLit q [-72, -73, -75, -76]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70]) (l₂ := [-72, -73, -75, -76])
  have hm := merge_two (literal (valuationOf q) (1711)) (literal (valuationOf q) (1720)) (literal (valuationOf q) (1725)) (countLit q [-63, -64, -67, -70]) (countLit q [-72, -73, -75, -76]) (count1723 q) 1 2 (meaning1711 q) (meaning1720 q) (meaning1725 q) hs
  change valuationOf q 1711 = false ∨ valuationOf q 1720 = false ∨ valuationOf q 1725 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1311 (q : Snake 81) (h : Conditions q) : valuation q 1711 = false ∨ valuation q 1720 = false ∨ valuation q 1725 = true := counterClause1311 (baseVal q)

theorem counterClause1312 (q : Nat → Bool) : valuationOf q 1711 = false ∨ valuationOf q 1721 = false ∨ valuationOf q 1726 = true := by
  have hs : count1723 q = (countLit q [-63, -64, -67, -70]) + (countLit q [-72, -73, -75, -76]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70]) (l₂ := [-72, -73, -75, -76])
  have hm := merge_two (literal (valuationOf q) (1711)) (literal (valuationOf q) (1721)) (literal (valuationOf q) (1726)) (countLit q [-63, -64, -67, -70]) (countLit q [-72, -73, -75, -76]) (count1723 q) 1 3 (meaning1711 q) (meaning1721 q) (meaning1726 q) hs
  change valuationOf q 1711 = false ∨ valuationOf q 1721 = false ∨ valuationOf q 1726 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1312 (q : Snake 81) (h : Conditions q) : valuation q 1711 = false ∨ valuation q 1721 = false ∨ valuation q 1726 = true := counterClause1312 (baseVal q)

theorem block40 (q : Snake 81) (h : Conditions q) : B112E036.Block40 (valuation q) :=
  ⟨clause1281 q h, clause1282 q h, clause1283 q h, clause1284 q h, clause1285 q h, clause1286 q h, clause1287 q h, clause1288 q h, clause1289 q h, clause1290 q h, clause1291 q h, clause1292 q h, clause1293 q h, clause1294 q h, clause1295 q h, clause1296 q h, clause1297 q h, clause1298 q h, clause1299 q h, clause1300 q h, clause1301 q h, clause1302 q h, clause1303 q h, clause1304 q h, clause1305 q h, clause1306 q h, clause1307 q h, clause1308 q h, clause1309 q h, clause1310 q h, clause1311 q h, clause1312 q h⟩

end
end Snake9.Regrowth.E112036
