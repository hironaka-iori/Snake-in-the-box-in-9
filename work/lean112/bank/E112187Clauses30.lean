import E112187Semantics
import B112E187Inputs
namespace Snake9.Regrowth.E112187
noncomputable section
local instance blockDec30 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause961 (q : Nat → Bool) : valuationOf q 1649 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1683 = true := by
  have hs : count1676 q = (countLit q [-90, -92, -93, -95, -97, -98, -101]) + (countLit q [-104, -107, -108, -109, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93, -95, -97, -98, -101]) (l₂ := [-104, -107, -108, -109, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1649)) (literal (valuationOf q) (1670)) (literal (valuationOf q) (1683)) (countLit q [-90, -92, -93, -95, -97, -98, -101]) (countLit q [-104, -107, -108, -109, -111, -114, -115, -117]) (count1676 q) 5 3 (meaning1649 q) (meaning1670 q) (meaning1683 q) hs
  change valuationOf q 1649 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause961 (q : Snake 81) (h : Conditions q) : valuation q 1649 = false ∨ valuation q 1670 = false ∨ valuation q 1683 = true := counterClause961 (baseVal q)

theorem counterClause962 (q : Nat → Bool) : valuationOf q 1649 = false ∨ valuationOf q 1671 = false ∨ valuationOf q 1684 = true := by
  have hs : count1676 q = (countLit q [-90, -92, -93, -95, -97, -98, -101]) + (countLit q [-104, -107, -108, -109, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93, -95, -97, -98, -101]) (l₂ := [-104, -107, -108, -109, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1649)) (literal (valuationOf q) (1671)) (literal (valuationOf q) (1684)) (countLit q [-90, -92, -93, -95, -97, -98, -101]) (countLit q [-104, -107, -108, -109, -111, -114, -115, -117]) (count1676 q) 5 4 (meaning1649 q) (meaning1671 q) (meaning1684 q) hs
  change valuationOf q 1649 = false ∨ valuationOf q 1671 = false ∨ valuationOf q 1684 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause962 (q : Snake 81) (h : Conditions q) : valuation q 1649 = false ∨ valuation q 1671 = false ∨ valuation q 1684 = true := counterClause962 (baseVal q)

theorem counterClause963 (q : Nat → Bool) : valuationOf q 1649 = false ∨ valuationOf q 1672 = false ∨ valuationOf q 1685 = true := by
  have hs : count1676 q = (countLit q [-90, -92, -93, -95, -97, -98, -101]) + (countLit q [-104, -107, -108, -109, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93, -95, -97, -98, -101]) (l₂ := [-104, -107, -108, -109, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1649)) (literal (valuationOf q) (1672)) (literal (valuationOf q) (1685)) (countLit q [-90, -92, -93, -95, -97, -98, -101]) (countLit q [-104, -107, -108, -109, -111, -114, -115, -117]) (count1676 q) 5 5 (meaning1649 q) (meaning1672 q) (meaning1685 q) hs
  change valuationOf q 1649 = false ∨ valuationOf q 1672 = false ∨ valuationOf q 1685 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause963 (q : Snake 81) (h : Conditions q) : valuation q 1649 = false ∨ valuation q 1672 = false ∨ valuation q 1685 = true := counterClause963 (baseVal q)

theorem counterClause964 (q : Nat → Bool) : valuationOf q 1650 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1683 = true := by
  have hs : count1676 q = (countLit q [-90, -92, -93, -95, -97, -98, -101]) + (countLit q [-104, -107, -108, -109, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93, -95, -97, -98, -101]) (l₂ := [-104, -107, -108, -109, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1650)) (literal (valuationOf q) (1669)) (literal (valuationOf q) (1683)) (countLit q [-90, -92, -93, -95, -97, -98, -101]) (countLit q [-104, -107, -108, -109, -111, -114, -115, -117]) (count1676 q) 6 2 (meaning1650 q) (meaning1669 q) (meaning1683 q) hs
  change valuationOf q 1650 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause964 (q : Snake 81) (h : Conditions q) : valuation q 1650 = false ∨ valuation q 1669 = false ∨ valuation q 1683 = true := counterClause964 (baseVal q)

theorem counterClause965 (q : Nat → Bool) : valuationOf q 1650 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1684 = true := by
  have hs : count1676 q = (countLit q [-90, -92, -93, -95, -97, -98, -101]) + (countLit q [-104, -107, -108, -109, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93, -95, -97, -98, -101]) (l₂ := [-104, -107, -108, -109, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1650)) (literal (valuationOf q) (1670)) (literal (valuationOf q) (1684)) (countLit q [-90, -92, -93, -95, -97, -98, -101]) (countLit q [-104, -107, -108, -109, -111, -114, -115, -117]) (count1676 q) 6 3 (meaning1650 q) (meaning1670 q) (meaning1684 q) hs
  change valuationOf q 1650 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1684 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause965 (q : Snake 81) (h : Conditions q) : valuation q 1650 = false ∨ valuation q 1670 = false ∨ valuation q 1684 = true := counterClause965 (baseVal q)

theorem counterClause966 (q : Nat → Bool) : valuationOf q 1619 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1700 = true := by
  have hs : count1691 q = (countLit q [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) + (countLit q [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) (l₂ := [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1619)) (literal (valuationOf q) (1683)) (literal (valuationOf q) (1700)) (countLit q [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) (countLit q [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117]) (count1691 q) 2 8 (meaning1619 q) (meaning1683 q) (meaning1700 q) hs
  change valuationOf q 1619 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1700 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause966 (q : Snake 81) (h : Conditions q) : valuation q 1619 = false ∨ valuation q 1683 = false ∨ valuation q 1700 = true := counterClause966 (baseVal q)

theorem counterClause967 (q : Nat → Bool) : valuationOf q 1619 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1701 = true := by
  have hs : count1691 q = (countLit q [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) + (countLit q [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) (l₂ := [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1619)) (literal (valuationOf q) (1684)) (literal (valuationOf q) (1701)) (countLit q [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) (countLit q [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117]) (count1691 q) 2 9 (meaning1619 q) (meaning1684 q) (meaning1701 q) hs
  change valuationOf q 1619 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1701 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause967 (q : Snake 81) (h : Conditions q) : valuation q 1619 = false ∨ valuation q 1684 = false ∨ valuation q 1701 = true := counterClause967 (baseVal q)

theorem counterClause968 (q : Nat → Bool) : valuationOf q 1619 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1702 = true := by
  have hs : count1691 q = (countLit q [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) + (countLit q [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) (l₂ := [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1619)) (literal (valuationOf q) (1685)) (literal (valuationOf q) (1702)) (countLit q [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) (countLit q [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117]) (count1691 q) 2 10 (meaning1619 q) (meaning1685 q) (meaning1702 q) hs
  change valuationOf q 1619 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1702 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause968 (q : Snake 81) (h : Conditions q) : valuation q 1619 = false ∨ valuation q 1685 = false ∨ valuation q 1702 = true := counterClause968 (baseVal q)

theorem counterClause969 (q : Nat → Bool) : valuationOf q 1620 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1700 = true := by
  have hs : count1691 q = (countLit q [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) + (countLit q [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) (l₂ := [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1620)) (literal (valuationOf q) (1682)) (literal (valuationOf q) (1700)) (countLit q [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) (countLit q [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117]) (count1691 q) 3 7 (meaning1620 q) (meaning1682 q) (meaning1700 q) hs
  change valuationOf q 1620 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1700 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause969 (q : Snake 81) (h : Conditions q) : valuation q 1620 = false ∨ valuation q 1682 = false ∨ valuation q 1700 = true := counterClause969 (baseVal q)

theorem counterClause970 (q : Nat → Bool) : valuationOf q 1620 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1701 = true := by
  have hs : count1691 q = (countLit q [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) + (countLit q [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) (l₂ := [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1620)) (literal (valuationOf q) (1683)) (literal (valuationOf q) (1701)) (countLit q [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) (countLit q [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117]) (count1691 q) 3 8 (meaning1620 q) (meaning1683 q) (meaning1701 q) hs
  change valuationOf q 1620 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1701 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause970 (q : Snake 81) (h : Conditions q) : valuation q 1620 = false ∨ valuation q 1683 = false ∨ valuation q 1701 = true := counterClause970 (baseVal q)

theorem counterClause971 (q : Nat → Bool) : valuationOf q 1620 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1702 = true := by
  have hs : count1691 q = (countLit q [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) + (countLit q [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) (l₂ := [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1620)) (literal (valuationOf q) (1684)) (literal (valuationOf q) (1702)) (countLit q [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) (countLit q [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117]) (count1691 q) 3 9 (meaning1620 q) (meaning1684 q) (meaning1702 q) hs
  change valuationOf q 1620 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1702 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause971 (q : Snake 81) (h : Conditions q) : valuation q 1620 = false ∨ valuation q 1684 = false ∨ valuation q 1702 = true := counterClause971 (baseVal q)

theorem counterClause972 (q : Nat → Bool) : valuationOf q 1621 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1700 = true := by
  have hs : count1691 q = (countLit q [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) + (countLit q [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) (l₂ := [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1621)) (literal (valuationOf q) (1681)) (literal (valuationOf q) (1700)) (countLit q [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) (countLit q [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117]) (count1691 q) 4 6 (meaning1621 q) (meaning1681 q) (meaning1700 q) hs
  change valuationOf q 1621 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1700 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause972 (q : Snake 81) (h : Conditions q) : valuation q 1621 = false ∨ valuation q 1681 = false ∨ valuation q 1700 = true := counterClause972 (baseVal q)

theorem counterClause973 (q : Nat → Bool) : valuationOf q 1621 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1701 = true := by
  have hs : count1691 q = (countLit q [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) + (countLit q [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) (l₂ := [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1621)) (literal (valuationOf q) (1682)) (literal (valuationOf q) (1701)) (countLit q [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) (countLit q [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117]) (count1691 q) 4 7 (meaning1621 q) (meaning1682 q) (meaning1701 q) hs
  change valuationOf q 1621 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1701 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause973 (q : Snake 81) (h : Conditions q) : valuation q 1621 = false ∨ valuation q 1682 = false ∨ valuation q 1701 = true := counterClause973 (baseVal q)

theorem counterClause974 (q : Nat → Bool) : valuationOf q 1621 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1702 = true := by
  have hs : count1691 q = (countLit q [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) + (countLit q [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) (l₂ := [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1621)) (literal (valuationOf q) (1683)) (literal (valuationOf q) (1702)) (countLit q [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) (countLit q [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117]) (count1691 q) 4 8 (meaning1621 q) (meaning1683 q) (meaning1702 q) hs
  change valuationOf q 1621 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1702 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause974 (q : Snake 81) (h : Conditions q) : valuation q 1621 = false ∨ valuation q 1683 = false ∨ valuation q 1702 = true := counterClause974 (baseVal q)

theorem counterClause975 (q : Nat → Bool) : valuationOf q 1621 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1703 = true := by
  have hs : count1691 q = (countLit q [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) + (countLit q [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) (l₂ := [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1621)) (literal (valuationOf q) (1684)) (literal (valuationOf q) (1703)) (countLit q [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) (countLit q [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117]) (count1691 q) 4 9 (meaning1621 q) (meaning1684 q) (meaning1703 q) hs
  change valuationOf q 1621 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1703 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause975 (q : Snake 81) (h : Conditions q) : valuation q 1621 = false ∨ valuation q 1684 = false ∨ valuation q 1703 = true := counterClause975 (baseVal q)

theorem counterClause976 (q : Nat → Bool) : valuationOf q 1622 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1700 = true := by
  have hs : count1691 q = (countLit q [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) + (countLit q [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) (l₂ := [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1622)) (literal (valuationOf q) (1680)) (literal (valuationOf q) (1700)) (countLit q [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) (countLit q [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117]) (count1691 q) 5 5 (meaning1622 q) (meaning1680 q) (meaning1700 q) hs
  change valuationOf q 1622 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1700 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause976 (q : Snake 81) (h : Conditions q) : valuation q 1622 = false ∨ valuation q 1680 = false ∨ valuation q 1700 = true := counterClause976 (baseVal q)

theorem counterClause977 (q : Nat → Bool) : valuationOf q 1622 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1701 = true := by
  have hs : count1691 q = (countLit q [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) + (countLit q [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) (l₂ := [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1622)) (literal (valuationOf q) (1681)) (literal (valuationOf q) (1701)) (countLit q [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) (countLit q [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117]) (count1691 q) 5 6 (meaning1622 q) (meaning1681 q) (meaning1701 q) hs
  change valuationOf q 1622 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1701 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause977 (q : Snake 81) (h : Conditions q) : valuation q 1622 = false ∨ valuation q 1681 = false ∨ valuation q 1701 = true := counterClause977 (baseVal q)

theorem counterClause978 (q : Nat → Bool) : valuationOf q 1622 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1702 = true := by
  have hs : count1691 q = (countLit q [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) + (countLit q [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) (l₂ := [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1622)) (literal (valuationOf q) (1682)) (literal (valuationOf q) (1702)) (countLit q [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) (countLit q [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117]) (count1691 q) 5 7 (meaning1622 q) (meaning1682 q) (meaning1702 q) hs
  change valuationOf q 1622 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1702 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause978 (q : Snake 81) (h : Conditions q) : valuation q 1622 = false ∨ valuation q 1682 = false ∨ valuation q 1702 = true := counterClause978 (baseVal q)

theorem counterClause979 (q : Nat → Bool) : valuationOf q 1622 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1703 = true := by
  have hs : count1691 q = (countLit q [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) + (countLit q [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) (l₂ := [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1622)) (literal (valuationOf q) (1683)) (literal (valuationOf q) (1703)) (countLit q [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) (countLit q [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117]) (count1691 q) 5 8 (meaning1622 q) (meaning1683 q) (meaning1703 q) hs
  change valuationOf q 1622 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1703 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause979 (q : Snake 81) (h : Conditions q) : valuation q 1622 = false ∨ valuation q 1683 = false ∨ valuation q 1703 = true := counterClause979 (baseVal q)

theorem counterClause980 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1700 = true := by
  have hs : count1691 q = (countLit q [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) + (countLit q [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) (l₂ := [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1623)) (literal (valuationOf q) (1679)) (literal (valuationOf q) (1700)) (countLit q [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) (countLit q [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117]) (count1691 q) 6 4 (meaning1623 q) (meaning1679 q) (meaning1700 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1700 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause980 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1679 = false ∨ valuation q 1700 = true := counterClause980 (baseVal q)

theorem counterClause981 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1701 = true := by
  have hs : count1691 q = (countLit q [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) + (countLit q [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) (l₂ := [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1623)) (literal (valuationOf q) (1680)) (literal (valuationOf q) (1701)) (countLit q [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) (countLit q [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117]) (count1691 q) 6 5 (meaning1623 q) (meaning1680 q) (meaning1701 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1701 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause981 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1680 = false ∨ valuation q 1701 = true := counterClause981 (baseVal q)

theorem counterClause982 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1702 = true := by
  have hs : count1691 q = (countLit q [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) + (countLit q [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) (l₂ := [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1623)) (literal (valuationOf q) (1681)) (literal (valuationOf q) (1702)) (countLit q [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) (countLit q [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117]) (count1691 q) 6 6 (meaning1623 q) (meaning1681 q) (meaning1702 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1702 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause982 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1681 = false ∨ valuation q 1702 = true := counterClause982 (baseVal q)

theorem counterClause983 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1703 = true := by
  have hs : count1691 q = (countLit q [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) + (countLit q [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) (l₂ := [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1623)) (literal (valuationOf q) (1682)) (literal (valuationOf q) (1703)) (countLit q [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) (countLit q [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117]) (count1691 q) 6 7 (meaning1623 q) (meaning1682 q) (meaning1703 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1703 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause983 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1682 = false ∨ valuation q 1703 = true := counterClause983 (baseVal q)

theorem counterClause984 (q : Nat → Bool) : valuationOf q 1624 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1701 = true := by
  have hs : count1691 q = (countLit q [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) + (countLit q [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) (l₂ := [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1624)) (literal (valuationOf q) (1679)) (literal (valuationOf q) (1701)) (countLit q [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) (countLit q [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117]) (count1691 q) 7 4 (meaning1624 q) (meaning1679 q) (meaning1701 q) hs
  change valuationOf q 1624 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1701 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause984 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1679 = false ∨ valuation q 1701 = true := counterClause984 (baseVal q)

theorem counterClause985 (q : Nat → Bool) : valuationOf q 1624 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1702 = true := by
  have hs : count1691 q = (countLit q [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) + (countLit q [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) (l₂ := [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1624)) (literal (valuationOf q) (1680)) (literal (valuationOf q) (1702)) (countLit q [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) (countLit q [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117]) (count1691 q) 7 5 (meaning1624 q) (meaning1680 q) (meaning1702 q) hs
  change valuationOf q 1624 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1702 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause985 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1680 = false ∨ valuation q 1702 = true := counterClause985 (baseVal q)

theorem counterClause986 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1703 = true := by
  have hs : count1691 q = (countLit q [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) + (countLit q [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) (l₂ := [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1625)) (literal (valuationOf q) (1680)) (literal (valuationOf q) (1703)) (countLit q [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88]) (countLit q [-90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117]) (count1691 q) 8 5 (meaning1625 q) (meaning1680 q) (meaning1703 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1703 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause986 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1680 = false ∨ valuation q 1703 = true := counterClause986 (baseVal q)

theorem counterClause987 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1703 = false ∨ valuationOf q 1726 = true := by
  have hs : count1709 q = (countLit q [-2, -4, -6, -10, -11, -12, -13, -17, -21, -23, -24, -25, -29, -31, -32, -34, -35, -39, -40, -41, -42, -46, -48, -49, -51, -52, -56, -58, -59]) + (countLit q [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88, -90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -10, -11, -12, -13, -17, -21, -23, -24, -25, -29, -31, -32, -34, -35, -39, -40, -41, -42, -46, -48, -49, -51, -52, -56, -58, -59]) (l₂ := [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88, -90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1564)) (literal (valuationOf q) (1703)) (literal (valuationOf q) (1726)) (countLit q [-2, -4, -6, -10, -11, -12, -13, -17, -21, -23, -24, -25, -29, -31, -32, -34, -35, -39, -40, -41, -42, -46, -48, -49, -51, -52, -56, -58, -59]) (countLit q [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88, -90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117]) (count1709 q) 5 13 (meaning1564 q) (meaning1703 q) (meaning1726 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1703 = false ∨ valuationOf q 1726 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause987 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1703 = false ∨ valuation q 1726 = true := counterClause987 (baseVal q)

theorem counterClause988 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1702 = false ∨ valuationOf q 1726 = true := by
  have hs : count1709 q = (countLit q [-2, -4, -6, -10, -11, -12, -13, -17, -21, -23, -24, -25, -29, -31, -32, -34, -35, -39, -40, -41, -42, -46, -48, -49, -51, -52, -56, -58, -59]) + (countLit q [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88, -90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -10, -11, -12, -13, -17, -21, -23, -24, -25, -29, -31, -32, -34, -35, -39, -40, -41, -42, -46, -48, -49, -51, -52, -56, -58, -59]) (l₂ := [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88, -90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1565)) (literal (valuationOf q) (1702)) (literal (valuationOf q) (1726)) (countLit q [-2, -4, -6, -10, -11, -12, -13, -17, -21, -23, -24, -25, -29, -31, -32, -34, -35, -39, -40, -41, -42, -46, -48, -49, -51, -52, -56, -58, -59]) (countLit q [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88, -90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117]) (count1709 q) 6 12 (meaning1565 q) (meaning1702 q) (meaning1726 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1702 = false ∨ valuationOf q 1726 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause988 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1702 = false ∨ valuation q 1726 = true := counterClause988 (baseVal q)

theorem counterClause989 (q : Nat → Bool) : valuationOf q 1566 = false ∨ valuationOf q 1701 = false ∨ valuationOf q 1726 = true := by
  have hs : count1709 q = (countLit q [-2, -4, -6, -10, -11, -12, -13, -17, -21, -23, -24, -25, -29, -31, -32, -34, -35, -39, -40, -41, -42, -46, -48, -49, -51, -52, -56, -58, -59]) + (countLit q [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88, -90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -10, -11, -12, -13, -17, -21, -23, -24, -25, -29, -31, -32, -34, -35, -39, -40, -41, -42, -46, -48, -49, -51, -52, -56, -58, -59]) (l₂ := [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88, -90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1566)) (literal (valuationOf q) (1701)) (literal (valuationOf q) (1726)) (countLit q [-2, -4, -6, -10, -11, -12, -13, -17, -21, -23, -24, -25, -29, -31, -32, -34, -35, -39, -40, -41, -42, -46, -48, -49, -51, -52, -56, -58, -59]) (countLit q [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88, -90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117]) (count1709 q) 7 11 (meaning1566 q) (meaning1701 q) (meaning1726 q) hs
  change valuationOf q 1566 = false ∨ valuationOf q 1701 = false ∨ valuationOf q 1726 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause989 (q : Snake 81) (h : Conditions q) : valuation q 1566 = false ∨ valuation q 1701 = false ∨ valuation q 1726 = true := counterClause989 (baseVal q)

theorem counterClause990 (q : Nat → Bool) : valuationOf q 1567 = false ∨ valuationOf q 1700 = false ∨ valuationOf q 1726 = true := by
  have hs : count1709 q = (countLit q [-2, -4, -6, -10, -11, -12, -13, -17, -21, -23, -24, -25, -29, -31, -32, -34, -35, -39, -40, -41, -42, -46, -48, -49, -51, -52, -56, -58, -59]) + (countLit q [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88, -90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -10, -11, -12, -13, -17, -21, -23, -24, -25, -29, -31, -32, -34, -35, -39, -40, -41, -42, -46, -48, -49, -51, -52, -56, -58, -59]) (l₂ := [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88, -90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1567)) (literal (valuationOf q) (1700)) (literal (valuationOf q) (1726)) (countLit q [-2, -4, -6, -10, -11, -12, -13, -17, -21, -23, -24, -25, -29, -31, -32, -34, -35, -39, -40, -41, -42, -46, -48, -49, -51, -52, -56, -58, -59]) (countLit q [-60, -65, -66, -68, -69, -70, -72, -74, -75, -78, -80, -84, -85, -88, -90, -92, -93, -95, -97, -98, -101, -104, -107, -108, -109, -111, -114, -115, -117]) (count1709 q) 8 10 (meaning1567 q) (meaning1700 q) (meaning1726 q) hs
  change valuationOf q 1567 = false ∨ valuationOf q 1700 = false ∨ valuationOf q 1726 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause990 (q : Snake 81) (h : Conditions q) : valuation q 1567 = false ∨ valuation q 1700 = false ∨ valuation q 1726 = true := counterClause990 (baseVal q)

theorem clause991 (q : Snake 81) (h : Conditions q) : valuation q 1726 = false := by
  rw [value1726]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1709 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause992 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 29 = false ∨ valuation q 32 = false ∨ valuation q 33 = false := by
  rw [value28, value29, value32, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (160 : Vertex) (161 : Vertex) (168 : Vertex) (169 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block30 (q : Snake 81) (h : Conditions q) : B112E187.Block30 (valuation q) :=
  ⟨clause961 q h, clause962 q h, clause963 q h, clause964 q h, clause965 q h, clause966 q h, clause967 q h, clause968 q h, clause969 q h, clause970 q h, clause971 q h, clause972 q h, clause973 q h, clause974 q h, clause975 q h, clause976 q h, clause977 q h, clause978 q h, clause979 q h, clause980 q h, clause981 q h, clause982 q h, clause983 q h, clause984 q h, clause985 q h, clause986 q h, clause987 q h, clause988 q h, clause989 q h, clause990 q h, clause991 q h, clause992 q h⟩

end
end Snake9.Regrowth.E112187
