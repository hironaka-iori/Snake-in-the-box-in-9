import E112186Semantics
import B112E186Inputs
namespace Snake9.Regrowth.E112186
noncomputable section
local instance blockDec37 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1185 (q : Nat → Bool) : valuationOf q 100 = true ∨ valuationOf q 1709 = true := by
  have hs : count1709 q = (countLit q [-98]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-100])
  have hm := merge_right (literal (valuationOf q) (-100)) (literal (valuationOf q) (1709)) (countLit q [-98]) (countLit q [-100]) (count1709 q) 1 (meaningNeg100 q) (meaning1709 q) hs
  change (! (valuationOf q 100)) = false ∨ valuationOf q 1709 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1185 (q : Snake 81) (h : Conditions q) : valuation q 100 = true ∨ valuation q 1709 = true := counterClause1185 (baseVal q)

theorem counterClause1186 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 1709 = true := by
  have hs : count1709 q = (countLit q [-98]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-100])
  have hm := merge_left (literal (valuationOf q) (-98)) (literal (valuationOf q) (1709)) (countLit q [-98]) (countLit q [-100]) (count1709 q) 1 (meaningNeg98 q) (meaning1709 q) hs
  change (! (valuationOf q 98)) = false ∨ valuationOf q 1709 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1186 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 1709 = true := counterClause1186 (baseVal q)

theorem counterClause1187 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 100 = true ∨ valuationOf q 1710 = true := by
  have hs : count1709 q = (countLit q [-98]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-100])
  have hm := merge_two (literal (valuationOf q) (-98)) (literal (valuationOf q) (-100)) (literal (valuationOf q) (1710)) (countLit q [-98]) (countLit q [-100]) (count1709 q) 1 1 (meaningNeg98 q) (meaningNeg100 q) (meaning1710 q) hs
  change (! (valuationOf q 98)) = false ∨ (! (valuationOf q 100)) = false ∨ valuationOf q 1710 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1187 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 100 = true ∨ valuation q 1710 = true := counterClause1187 (baseVal q)

theorem counterClause1188 (q : Nat → Bool) : valuationOf q 1709 = false ∨ valuationOf q 1711 = true := by
  have hs : count1711 q = (countLit q [-94, -97]) + (countLit q [-98, -100]) := List.countP_append (p := literal q) (l₁ := [-94, -97]) (l₂ := [-98, -100])
  have hm := merge_right (literal (valuationOf q) (1709)) (literal (valuationOf q) (1711)) (countLit q [-94, -97]) (countLit q [-98, -100]) (count1711 q) 1 (meaning1709 q) (meaning1711 q) hs
  change valuationOf q 1709 = false ∨ valuationOf q 1711 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1188 (q : Snake 81) (h : Conditions q) : valuation q 1709 = false ∨ valuation q 1711 = true := counterClause1188 (baseVal q)

theorem counterClause1189 (q : Nat → Bool) : valuationOf q 1710 = false ∨ valuationOf q 1712 = true := by
  have hs : count1711 q = (countLit q [-94, -97]) + (countLit q [-98, -100]) := List.countP_append (p := literal q) (l₁ := [-94, -97]) (l₂ := [-98, -100])
  have hm := merge_right (literal (valuationOf q) (1710)) (literal (valuationOf q) (1712)) (countLit q [-94, -97]) (countLit q [-98, -100]) (count1711 q) 2 (meaning1710 q) (meaning1712 q) hs
  change valuationOf q 1710 = false ∨ valuationOf q 1712 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1189 (q : Snake 81) (h : Conditions q) : valuation q 1710 = false ∨ valuation q 1712 = true := counterClause1189 (baseVal q)

theorem counterClause1190 (q : Nat → Bool) : valuationOf q 1707 = false ∨ valuationOf q 1711 = true := by
  have hs : count1711 q = (countLit q [-94, -97]) + (countLit q [-98, -100]) := List.countP_append (p := literal q) (l₁ := [-94, -97]) (l₂ := [-98, -100])
  have hm := merge_left (literal (valuationOf q) (1707)) (literal (valuationOf q) (1711)) (countLit q [-94, -97]) (countLit q [-98, -100]) (count1711 q) 1 (meaning1707 q) (meaning1711 q) hs
  change valuationOf q 1707 = false ∨ valuationOf q 1711 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1190 (q : Snake 81) (h : Conditions q) : valuation q 1707 = false ∨ valuation q 1711 = true := counterClause1190 (baseVal q)

theorem counterClause1191 (q : Nat → Bool) : valuationOf q 1707 = false ∨ valuationOf q 1709 = false ∨ valuationOf q 1712 = true := by
  have hs : count1711 q = (countLit q [-94, -97]) + (countLit q [-98, -100]) := List.countP_append (p := literal q) (l₁ := [-94, -97]) (l₂ := [-98, -100])
  have hm := merge_two (literal (valuationOf q) (1707)) (literal (valuationOf q) (1709)) (literal (valuationOf q) (1712)) (countLit q [-94, -97]) (countLit q [-98, -100]) (count1711 q) 1 1 (meaning1707 q) (meaning1709 q) (meaning1712 q) hs
  change valuationOf q 1707 = false ∨ valuationOf q 1709 = false ∨ valuationOf q 1712 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1191 (q : Snake 81) (h : Conditions q) : valuation q 1707 = false ∨ valuation q 1709 = false ∨ valuation q 1712 = true := counterClause1191 (baseVal q)

theorem counterClause1192 (q : Nat → Bool) : valuationOf q 1707 = false ∨ valuationOf q 1710 = false ∨ valuationOf q 1713 = true := by
  have hs : count1711 q = (countLit q [-94, -97]) + (countLit q [-98, -100]) := List.countP_append (p := literal q) (l₁ := [-94, -97]) (l₂ := [-98, -100])
  have hm := merge_two (literal (valuationOf q) (1707)) (literal (valuationOf q) (1710)) (literal (valuationOf q) (1713)) (countLit q [-94, -97]) (countLit q [-98, -100]) (count1711 q) 1 2 (meaning1707 q) (meaning1710 q) (meaning1713 q) hs
  change valuationOf q 1707 = false ∨ valuationOf q 1710 = false ∨ valuationOf q 1713 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1192 (q : Snake 81) (h : Conditions q) : valuation q 1707 = false ∨ valuation q 1710 = false ∨ valuation q 1713 = true := counterClause1192 (baseVal q)

theorem counterClause1193 (q : Nat → Bool) : valuationOf q 1708 = false ∨ valuationOf q 1712 = true := by
  have hs : count1711 q = (countLit q [-94, -97]) + (countLit q [-98, -100]) := List.countP_append (p := literal q) (l₁ := [-94, -97]) (l₂ := [-98, -100])
  have hm := merge_left (literal (valuationOf q) (1708)) (literal (valuationOf q) (1712)) (countLit q [-94, -97]) (countLit q [-98, -100]) (count1711 q) 2 (meaning1708 q) (meaning1712 q) hs
  change valuationOf q 1708 = false ∨ valuationOf q 1712 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1193 (q : Snake 81) (h : Conditions q) : valuation q 1708 = false ∨ valuation q 1712 = true := counterClause1193 (baseVal q)

theorem counterClause1194 (q : Nat → Bool) : valuationOf q 1708 = false ∨ valuationOf q 1709 = false ∨ valuationOf q 1713 = true := by
  have hs : count1711 q = (countLit q [-94, -97]) + (countLit q [-98, -100]) := List.countP_append (p := literal q) (l₁ := [-94, -97]) (l₂ := [-98, -100])
  have hm := merge_two (literal (valuationOf q) (1708)) (literal (valuationOf q) (1709)) (literal (valuationOf q) (1713)) (countLit q [-94, -97]) (countLit q [-98, -100]) (count1711 q) 2 1 (meaning1708 q) (meaning1709 q) (meaning1713 q) hs
  change valuationOf q 1708 = false ∨ valuationOf q 1709 = false ∨ valuationOf q 1713 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1194 (q : Snake 81) (h : Conditions q) : valuation q 1708 = false ∨ valuation q 1709 = false ∨ valuation q 1713 = true := counterClause1194 (baseVal q)

theorem counterClause1195 (q : Nat → Bool) : valuationOf q 1708 = false ∨ valuationOf q 1710 = false ∨ valuationOf q 1714 = true := by
  have hs : count1711 q = (countLit q [-94, -97]) + (countLit q [-98, -100]) := List.countP_append (p := literal q) (l₁ := [-94, -97]) (l₂ := [-98, -100])
  have hm := merge_two (literal (valuationOf q) (1708)) (literal (valuationOf q) (1710)) (literal (valuationOf q) (1714)) (countLit q [-94, -97]) (countLit q [-98, -100]) (count1711 q) 2 2 (meaning1708 q) (meaning1710 q) (meaning1714 q) hs
  change valuationOf q 1708 = false ∨ valuationOf q 1710 = false ∨ valuationOf q 1714 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1195 (q : Snake 81) (h : Conditions q) : valuation q 1708 = false ∨ valuation q 1710 = false ∨ valuation q 1714 = true := counterClause1195 (baseVal q)

theorem counterClause1196 (q : Nat → Bool) : valuationOf q 102 = true ∨ valuationOf q 1715 = true := by
  have hs : count1715 q = (countLit q [-101]) + (countLit q [-102]) := List.countP_append (p := literal q) (l₁ := [-101]) (l₂ := [-102])
  have hm := merge_right (literal (valuationOf q) (-102)) (literal (valuationOf q) (1715)) (countLit q [-101]) (countLit q [-102]) (count1715 q) 1 (meaningNeg102 q) (meaning1715 q) hs
  change (! (valuationOf q 102)) = false ∨ valuationOf q 1715 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1196 (q : Snake 81) (h : Conditions q) : valuation q 102 = true ∨ valuation q 1715 = true := counterClause1196 (baseVal q)

theorem counterClause1197 (q : Nat → Bool) : valuationOf q 101 = true ∨ valuationOf q 1715 = true := by
  have hs : count1715 q = (countLit q [-101]) + (countLit q [-102]) := List.countP_append (p := literal q) (l₁ := [-101]) (l₂ := [-102])
  have hm := merge_left (literal (valuationOf q) (-101)) (literal (valuationOf q) (1715)) (countLit q [-101]) (countLit q [-102]) (count1715 q) 1 (meaningNeg101 q) (meaning1715 q) hs
  change (! (valuationOf q 101)) = false ∨ valuationOf q 1715 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1197 (q : Snake 81) (h : Conditions q) : valuation q 101 = true ∨ valuation q 1715 = true := counterClause1197 (baseVal q)

theorem counterClause1198 (q : Nat → Bool) : valuationOf q 101 = true ∨ valuationOf q 102 = true ∨ valuationOf q 1716 = true := by
  have hs : count1715 q = (countLit q [-101]) + (countLit q [-102]) := List.countP_append (p := literal q) (l₁ := [-101]) (l₂ := [-102])
  have hm := merge_two (literal (valuationOf q) (-101)) (literal (valuationOf q) (-102)) (literal (valuationOf q) (1716)) (countLit q [-101]) (countLit q [-102]) (count1715 q) 1 1 (meaningNeg101 q) (meaningNeg102 q) (meaning1716 q) hs
  change (! (valuationOf q 101)) = false ∨ (! (valuationOf q 102)) = false ∨ valuationOf q 1716 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1198 (q : Snake 81) (h : Conditions q) : valuation q 101 = true ∨ valuation q 102 = true ∨ valuation q 1716 = true := counterClause1198 (baseVal q)

theorem counterClause1199 (q : Nat → Bool) : valuationOf q 107 = true ∨ valuationOf q 1717 = true := by
  have hs : count1717 q = (countLit q [-105]) + (countLit q [-107]) := List.countP_append (p := literal q) (l₁ := [-105]) (l₂ := [-107])
  have hm := merge_right (literal (valuationOf q) (-107)) (literal (valuationOf q) (1717)) (countLit q [-105]) (countLit q [-107]) (count1717 q) 1 (meaningNeg107 q) (meaning1717 q) hs
  change (! (valuationOf q 107)) = false ∨ valuationOf q 1717 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1199 (q : Snake 81) (h : Conditions q) : valuation q 107 = true ∨ valuation q 1717 = true := counterClause1199 (baseVal q)

theorem counterClause1200 (q : Nat → Bool) : valuationOf q 105 = true ∨ valuationOf q 1717 = true := by
  have hs : count1717 q = (countLit q [-105]) + (countLit q [-107]) := List.countP_append (p := literal q) (l₁ := [-105]) (l₂ := [-107])
  have hm := merge_left (literal (valuationOf q) (-105)) (literal (valuationOf q) (1717)) (countLit q [-105]) (countLit q [-107]) (count1717 q) 1 (meaningNeg105 q) (meaning1717 q) hs
  change (! (valuationOf q 105)) = false ∨ valuationOf q 1717 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1200 (q : Snake 81) (h : Conditions q) : valuation q 105 = true ∨ valuation q 1717 = true := counterClause1200 (baseVal q)

theorem counterClause1201 (q : Nat → Bool) : valuationOf q 105 = true ∨ valuationOf q 107 = true ∨ valuationOf q 1718 = true := by
  have hs : count1717 q = (countLit q [-105]) + (countLit q [-107]) := List.countP_append (p := literal q) (l₁ := [-105]) (l₂ := [-107])
  have hm := merge_two (literal (valuationOf q) (-105)) (literal (valuationOf q) (-107)) (literal (valuationOf q) (1718)) (countLit q [-105]) (countLit q [-107]) (count1717 q) 1 1 (meaningNeg105 q) (meaningNeg107 q) (meaning1718 q) hs
  change (! (valuationOf q 105)) = false ∨ (! (valuationOf q 107)) = false ∨ valuationOf q 1718 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1201 (q : Snake 81) (h : Conditions q) : valuation q 105 = true ∨ valuation q 107 = true ∨ valuation q 1718 = true := counterClause1201 (baseVal q)

theorem counterClause1202 (q : Nat → Bool) : valuationOf q 1717 = false ∨ valuationOf q 1719 = true := by
  have hs : count1719 q = (countLit q [-101, -102]) + (countLit q [-105, -107]) := List.countP_append (p := literal q) (l₁ := [-101, -102]) (l₂ := [-105, -107])
  have hm := merge_right (literal (valuationOf q) (1717)) (literal (valuationOf q) (1719)) (countLit q [-101, -102]) (countLit q [-105, -107]) (count1719 q) 1 (meaning1717 q) (meaning1719 q) hs
  change valuationOf q 1717 = false ∨ valuationOf q 1719 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1202 (q : Snake 81) (h : Conditions q) : valuation q 1717 = false ∨ valuation q 1719 = true := counterClause1202 (baseVal q)

theorem counterClause1203 (q : Nat → Bool) : valuationOf q 1718 = false ∨ valuationOf q 1720 = true := by
  have hs : count1719 q = (countLit q [-101, -102]) + (countLit q [-105, -107]) := List.countP_append (p := literal q) (l₁ := [-101, -102]) (l₂ := [-105, -107])
  have hm := merge_right (literal (valuationOf q) (1718)) (literal (valuationOf q) (1720)) (countLit q [-101, -102]) (countLit q [-105, -107]) (count1719 q) 2 (meaning1718 q) (meaning1720 q) hs
  change valuationOf q 1718 = false ∨ valuationOf q 1720 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1203 (q : Snake 81) (h : Conditions q) : valuation q 1718 = false ∨ valuation q 1720 = true := counterClause1203 (baseVal q)

theorem counterClause1204 (q : Nat → Bool) : valuationOf q 1715 = false ∨ valuationOf q 1719 = true := by
  have hs : count1719 q = (countLit q [-101, -102]) + (countLit q [-105, -107]) := List.countP_append (p := literal q) (l₁ := [-101, -102]) (l₂ := [-105, -107])
  have hm := merge_left (literal (valuationOf q) (1715)) (literal (valuationOf q) (1719)) (countLit q [-101, -102]) (countLit q [-105, -107]) (count1719 q) 1 (meaning1715 q) (meaning1719 q) hs
  change valuationOf q 1715 = false ∨ valuationOf q 1719 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1204 (q : Snake 81) (h : Conditions q) : valuation q 1715 = false ∨ valuation q 1719 = true := counterClause1204 (baseVal q)

theorem counterClause1205 (q : Nat → Bool) : valuationOf q 1715 = false ∨ valuationOf q 1717 = false ∨ valuationOf q 1720 = true := by
  have hs : count1719 q = (countLit q [-101, -102]) + (countLit q [-105, -107]) := List.countP_append (p := literal q) (l₁ := [-101, -102]) (l₂ := [-105, -107])
  have hm := merge_two (literal (valuationOf q) (1715)) (literal (valuationOf q) (1717)) (literal (valuationOf q) (1720)) (countLit q [-101, -102]) (countLit q [-105, -107]) (count1719 q) 1 1 (meaning1715 q) (meaning1717 q) (meaning1720 q) hs
  change valuationOf q 1715 = false ∨ valuationOf q 1717 = false ∨ valuationOf q 1720 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1205 (q : Snake 81) (h : Conditions q) : valuation q 1715 = false ∨ valuation q 1717 = false ∨ valuation q 1720 = true := counterClause1205 (baseVal q)

theorem counterClause1206 (q : Nat → Bool) : valuationOf q 1715 = false ∨ valuationOf q 1718 = false ∨ valuationOf q 1721 = true := by
  have hs : count1719 q = (countLit q [-101, -102]) + (countLit q [-105, -107]) := List.countP_append (p := literal q) (l₁ := [-101, -102]) (l₂ := [-105, -107])
  have hm := merge_two (literal (valuationOf q) (1715)) (literal (valuationOf q) (1718)) (literal (valuationOf q) (1721)) (countLit q [-101, -102]) (countLit q [-105, -107]) (count1719 q) 1 2 (meaning1715 q) (meaning1718 q) (meaning1721 q) hs
  change valuationOf q 1715 = false ∨ valuationOf q 1718 = false ∨ valuationOf q 1721 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1206 (q : Snake 81) (h : Conditions q) : valuation q 1715 = false ∨ valuation q 1718 = false ∨ valuation q 1721 = true := counterClause1206 (baseVal q)

theorem counterClause1207 (q : Nat → Bool) : valuationOf q 1716 = false ∨ valuationOf q 1720 = true := by
  have hs : count1719 q = (countLit q [-101, -102]) + (countLit q [-105, -107]) := List.countP_append (p := literal q) (l₁ := [-101, -102]) (l₂ := [-105, -107])
  have hm := merge_left (literal (valuationOf q) (1716)) (literal (valuationOf q) (1720)) (countLit q [-101, -102]) (countLit q [-105, -107]) (count1719 q) 2 (meaning1716 q) (meaning1720 q) hs
  change valuationOf q 1716 = false ∨ valuationOf q 1720 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1207 (q : Snake 81) (h : Conditions q) : valuation q 1716 = false ∨ valuation q 1720 = true := counterClause1207 (baseVal q)

theorem counterClause1208 (q : Nat → Bool) : valuationOf q 1716 = false ∨ valuationOf q 1717 = false ∨ valuationOf q 1721 = true := by
  have hs : count1719 q = (countLit q [-101, -102]) + (countLit q [-105, -107]) := List.countP_append (p := literal q) (l₁ := [-101, -102]) (l₂ := [-105, -107])
  have hm := merge_two (literal (valuationOf q) (1716)) (literal (valuationOf q) (1717)) (literal (valuationOf q) (1721)) (countLit q [-101, -102]) (countLit q [-105, -107]) (count1719 q) 2 1 (meaning1716 q) (meaning1717 q) (meaning1721 q) hs
  change valuationOf q 1716 = false ∨ valuationOf q 1717 = false ∨ valuationOf q 1721 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1208 (q : Snake 81) (h : Conditions q) : valuation q 1716 = false ∨ valuation q 1717 = false ∨ valuation q 1721 = true := counterClause1208 (baseVal q)

theorem counterClause1209 (q : Nat → Bool) : valuationOf q 1716 = false ∨ valuationOf q 1718 = false ∨ valuationOf q 1722 = true := by
  have hs : count1719 q = (countLit q [-101, -102]) + (countLit q [-105, -107]) := List.countP_append (p := literal q) (l₁ := [-101, -102]) (l₂ := [-105, -107])
  have hm := merge_two (literal (valuationOf q) (1716)) (literal (valuationOf q) (1718)) (literal (valuationOf q) (1722)) (countLit q [-101, -102]) (countLit q [-105, -107]) (count1719 q) 2 2 (meaning1716 q) (meaning1718 q) (meaning1722 q) hs
  change valuationOf q 1716 = false ∨ valuationOf q 1718 = false ∨ valuationOf q 1722 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1209 (q : Snake 81) (h : Conditions q) : valuation q 1716 = false ∨ valuation q 1718 = false ∨ valuation q 1722 = true := counterClause1209 (baseVal q)

theorem counterClause1210 (q : Nat → Bool) : valuationOf q 1711 = false ∨ valuationOf q 1723 = true := by
  have hs : count1723 q = (countLit q [-94, -97, -98, -100]) + (countLit q [-101, -102, -105, -107]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -98, -100]) (l₂ := [-101, -102, -105, -107])
  have hm := merge_left (literal (valuationOf q) (1711)) (literal (valuationOf q) (1723)) (countLit q [-94, -97, -98, -100]) (countLit q [-101, -102, -105, -107]) (count1723 q) 1 (meaning1711 q) (meaning1723 q) hs
  change valuationOf q 1711 = false ∨ valuationOf q 1723 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1210 (q : Snake 81) (h : Conditions q) : valuation q 1711 = false ∨ valuation q 1723 = true := counterClause1210 (baseVal q)

theorem counterClause1211 (q : Nat → Bool) : valuationOf q 1711 = false ∨ valuationOf q 1719 = false ∨ valuationOf q 1724 = true := by
  have hs : count1723 q = (countLit q [-94, -97, -98, -100]) + (countLit q [-101, -102, -105, -107]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -98, -100]) (l₂ := [-101, -102, -105, -107])
  have hm := merge_two (literal (valuationOf q) (1711)) (literal (valuationOf q) (1719)) (literal (valuationOf q) (1724)) (countLit q [-94, -97, -98, -100]) (countLit q [-101, -102, -105, -107]) (count1723 q) 1 1 (meaning1711 q) (meaning1719 q) (meaning1724 q) hs
  change valuationOf q 1711 = false ∨ valuationOf q 1719 = false ∨ valuationOf q 1724 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1211 (q : Snake 81) (h : Conditions q) : valuation q 1711 = false ∨ valuation q 1719 = false ∨ valuation q 1724 = true := counterClause1211 (baseVal q)

theorem counterClause1212 (q : Nat → Bool) : valuationOf q 1711 = false ∨ valuationOf q 1720 = false ∨ valuationOf q 1725 = true := by
  have hs : count1723 q = (countLit q [-94, -97, -98, -100]) + (countLit q [-101, -102, -105, -107]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -98, -100]) (l₂ := [-101, -102, -105, -107])
  have hm := merge_two (literal (valuationOf q) (1711)) (literal (valuationOf q) (1720)) (literal (valuationOf q) (1725)) (countLit q [-94, -97, -98, -100]) (countLit q [-101, -102, -105, -107]) (count1723 q) 1 2 (meaning1711 q) (meaning1720 q) (meaning1725 q) hs
  change valuationOf q 1711 = false ∨ valuationOf q 1720 = false ∨ valuationOf q 1725 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1212 (q : Snake 81) (h : Conditions q) : valuation q 1711 = false ∨ valuation q 1720 = false ∨ valuation q 1725 = true := counterClause1212 (baseVal q)

theorem counterClause1213 (q : Nat → Bool) : valuationOf q 1711 = false ∨ valuationOf q 1721 = false ∨ valuationOf q 1726 = true := by
  have hs : count1723 q = (countLit q [-94, -97, -98, -100]) + (countLit q [-101, -102, -105, -107]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -98, -100]) (l₂ := [-101, -102, -105, -107])
  have hm := merge_two (literal (valuationOf q) (1711)) (literal (valuationOf q) (1721)) (literal (valuationOf q) (1726)) (countLit q [-94, -97, -98, -100]) (countLit q [-101, -102, -105, -107]) (count1723 q) 1 3 (meaning1711 q) (meaning1721 q) (meaning1726 q) hs
  change valuationOf q 1711 = false ∨ valuationOf q 1721 = false ∨ valuationOf q 1726 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1213 (q : Snake 81) (h : Conditions q) : valuation q 1711 = false ∨ valuation q 1721 = false ∨ valuation q 1726 = true := counterClause1213 (baseVal q)

theorem counterClause1214 (q : Nat → Bool) : valuationOf q 1711 = false ∨ valuationOf q 1722 = false ∨ valuationOf q 1727 = true := by
  have hs : count1723 q = (countLit q [-94, -97, -98, -100]) + (countLit q [-101, -102, -105, -107]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -98, -100]) (l₂ := [-101, -102, -105, -107])
  have hm := merge_two (literal (valuationOf q) (1711)) (literal (valuationOf q) (1722)) (literal (valuationOf q) (1727)) (countLit q [-94, -97, -98, -100]) (countLit q [-101, -102, -105, -107]) (count1723 q) 1 4 (meaning1711 q) (meaning1722 q) (meaning1727 q) hs
  change valuationOf q 1711 = false ∨ valuationOf q 1722 = false ∨ valuationOf q 1727 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1214 (q : Snake 81) (h : Conditions q) : valuation q 1711 = false ∨ valuation q 1722 = false ∨ valuation q 1727 = true := counterClause1214 (baseVal q)

theorem counterClause1215 (q : Nat → Bool) : valuationOf q 1712 = false ∨ valuationOf q 1724 = true := by
  have hs : count1723 q = (countLit q [-94, -97, -98, -100]) + (countLit q [-101, -102, -105, -107]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -98, -100]) (l₂ := [-101, -102, -105, -107])
  have hm := merge_left (literal (valuationOf q) (1712)) (literal (valuationOf q) (1724)) (countLit q [-94, -97, -98, -100]) (countLit q [-101, -102, -105, -107]) (count1723 q) 2 (meaning1712 q) (meaning1724 q) hs
  change valuationOf q 1712 = false ∨ valuationOf q 1724 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1215 (q : Snake 81) (h : Conditions q) : valuation q 1712 = false ∨ valuation q 1724 = true := counterClause1215 (baseVal q)

theorem counterClause1216 (q : Nat → Bool) : valuationOf q 1712 = false ∨ valuationOf q 1719 = false ∨ valuationOf q 1725 = true := by
  have hs : count1723 q = (countLit q [-94, -97, -98, -100]) + (countLit q [-101, -102, -105, -107]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -98, -100]) (l₂ := [-101, -102, -105, -107])
  have hm := merge_two (literal (valuationOf q) (1712)) (literal (valuationOf q) (1719)) (literal (valuationOf q) (1725)) (countLit q [-94, -97, -98, -100]) (countLit q [-101, -102, -105, -107]) (count1723 q) 2 1 (meaning1712 q) (meaning1719 q) (meaning1725 q) hs
  change valuationOf q 1712 = false ∨ valuationOf q 1719 = false ∨ valuationOf q 1725 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1216 (q : Snake 81) (h : Conditions q) : valuation q 1712 = false ∨ valuation q 1719 = false ∨ valuation q 1725 = true := counterClause1216 (baseVal q)

theorem block37 (q : Snake 81) (h : Conditions q) : B112E186.Block37 (valuation q) :=
  ⟨clause1185 q h, clause1186 q h, clause1187 q h, clause1188 q h, clause1189 q h, clause1190 q h, clause1191 q h, clause1192 q h, clause1193 q h, clause1194 q h, clause1195 q h, clause1196 q h, clause1197 q h, clause1198 q h, clause1199 q h, clause1200 q h, clause1201 q h, clause1202 q h, clause1203 q h, clause1204 q h, clause1205 q h, clause1206 q h, clause1207 q h, clause1208 q h, clause1209 q h, clause1210 q h, clause1211 q h, clause1212 q h, clause1213 q h, clause1214 q h, clause1215 q h, clause1216 q h⟩

end
end Snake9.Regrowth.E112186
