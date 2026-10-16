import First112Semantics
import Dfs112FirstBooleanInputs
namespace Snake9.Regrowth.First112
noncomputable section
local instance blockDec41 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1313 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 1671 = true := by
  have hs : count1671 q = (countLit q [-92]) + (countLit q [-93]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92]) (l₂ := [-93])
  have hm := merge_right (literal (valuation q) (-93)) (literal (valuation q) (1671)) (countLit q [-92]) (countLit q [-93]) (count1671 q) 1 (meaningNeg93 q) (meaning1671 q) hs
  change (! (valuation q 93)) = false ∨ valuation q 1671 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1314 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 1671 = true := by
  have hs : count1671 q = (countLit q [-92]) + (countLit q [-93]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92]) (l₂ := [-93])
  have hm := merge_left (literal (valuation q) (-92)) (literal (valuation q) (1671)) (countLit q [-92]) (countLit q [-93]) (count1671 q) 1 (meaningNeg92 q) (meaning1671 q) hs
  change (! (valuation q 92)) = false ∨ valuation q 1671 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1315 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 93 = true ∨ valuation q 1672 = true := by
  have hs : count1671 q = (countLit q [-92]) + (countLit q [-93]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92]) (l₂ := [-93])
  have hm := merge_two (literal (valuation q) (-92)) (literal (valuation q) (-93)) (literal (valuation q) (1672)) (countLit q [-92]) (countLit q [-93]) (count1671 q) 1 1 (meaningNeg92 q) (meaningNeg93 q) (meaning1672 q) hs
  change (! (valuation q 92)) = false ∨ (! (valuation q 93)) = false ∨ valuation q 1672 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1316 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 1673 = true := by
  have hs : count1673 q = (countLit q [-95]) + (countLit q [-97]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-95]) (l₂ := [-97])
  have hm := merge_right (literal (valuation q) (-97)) (literal (valuation q) (1673)) (countLit q [-95]) (countLit q [-97]) (count1673 q) 1 (meaningNeg97 q) (meaning1673 q) hs
  change (! (valuation q 97)) = false ∨ valuation q 1673 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1317 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 1673 = true := by
  have hs : count1673 q = (countLit q [-95]) + (countLit q [-97]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-95]) (l₂ := [-97])
  have hm := merge_left (literal (valuation q) (-95)) (literal (valuation q) (1673)) (countLit q [-95]) (countLit q [-97]) (count1673 q) 1 (meaningNeg95 q) (meaning1673 q) hs
  change (! (valuation q 95)) = false ∨ valuation q 1673 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1318 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 97 = true ∨ valuation q 1674 = true := by
  have hs : count1673 q = (countLit q [-95]) + (countLit q [-97]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-95]) (l₂ := [-97])
  have hm := merge_two (literal (valuation q) (-95)) (literal (valuation q) (-97)) (literal (valuation q) (1674)) (countLit q [-95]) (countLit q [-97]) (count1673 q) 1 1 (meaningNeg95 q) (meaningNeg97 q) (meaning1674 q) hs
  change (! (valuation q 95)) = false ∨ (! (valuation q 97)) = false ∨ valuation q 1674 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1319 (q : Snake 81) (h : Conditions q) : valuation q 1673 = false ∨ valuation q 1675 = true := by
  have hs : count1675 q = (countLit q [-92, -93]) + (countLit q [-95, -97]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93]) (l₂ := [-95, -97])
  have hm := merge_right (literal (valuation q) (1673)) (literal (valuation q) (1675)) (countLit q [-92, -93]) (countLit q [-95, -97]) (count1675 q) 1 (meaning1673 q) (meaning1675 q) hs
  change valuation q 1673 = false ∨ valuation q 1675 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1320 (q : Snake 81) (h : Conditions q) : valuation q 1674 = false ∨ valuation q 1676 = true := by
  have hs : count1675 q = (countLit q [-92, -93]) + (countLit q [-95, -97]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93]) (l₂ := [-95, -97])
  have hm := merge_right (literal (valuation q) (1674)) (literal (valuation q) (1676)) (countLit q [-92, -93]) (countLit q [-95, -97]) (count1675 q) 2 (meaning1674 q) (meaning1676 q) hs
  change valuation q 1674 = false ∨ valuation q 1676 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1321 (q : Snake 81) (h : Conditions q) : valuation q 1671 = false ∨ valuation q 1675 = true := by
  have hs : count1675 q = (countLit q [-92, -93]) + (countLit q [-95, -97]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93]) (l₂ := [-95, -97])
  have hm := merge_left (literal (valuation q) (1671)) (literal (valuation q) (1675)) (countLit q [-92, -93]) (countLit q [-95, -97]) (count1675 q) 1 (meaning1671 q) (meaning1675 q) hs
  change valuation q 1671 = false ∨ valuation q 1675 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1322 (q : Snake 81) (h : Conditions q) : valuation q 1671 = false ∨ valuation q 1673 = false ∨ valuation q 1676 = true := by
  have hs : count1675 q = (countLit q [-92, -93]) + (countLit q [-95, -97]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93]) (l₂ := [-95, -97])
  have hm := merge_two (literal (valuation q) (1671)) (literal (valuation q) (1673)) (literal (valuation q) (1676)) (countLit q [-92, -93]) (countLit q [-95, -97]) (count1675 q) 1 1 (meaning1671 q) (meaning1673 q) (meaning1676 q) hs
  change valuation q 1671 = false ∨ valuation q 1673 = false ∨ valuation q 1676 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1323 (q : Snake 81) (h : Conditions q) : valuation q 1671 = false ∨ valuation q 1674 = false ∨ valuation q 1677 = true := by
  have hs : count1675 q = (countLit q [-92, -93]) + (countLit q [-95, -97]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93]) (l₂ := [-95, -97])
  have hm := merge_two (literal (valuation q) (1671)) (literal (valuation q) (1674)) (literal (valuation q) (1677)) (countLit q [-92, -93]) (countLit q [-95, -97]) (count1675 q) 1 2 (meaning1671 q) (meaning1674 q) (meaning1677 q) hs
  change valuation q 1671 = false ∨ valuation q 1674 = false ∨ valuation q 1677 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1324 (q : Snake 81) (h : Conditions q) : valuation q 1672 = false ∨ valuation q 1676 = true := by
  have hs : count1675 q = (countLit q [-92, -93]) + (countLit q [-95, -97]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93]) (l₂ := [-95, -97])
  have hm := merge_left (literal (valuation q) (1672)) (literal (valuation q) (1676)) (countLit q [-92, -93]) (countLit q [-95, -97]) (count1675 q) 2 (meaning1672 q) (meaning1676 q) hs
  change valuation q 1672 = false ∨ valuation q 1676 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1325 (q : Snake 81) (h : Conditions q) : valuation q 1672 = false ∨ valuation q 1673 = false ∨ valuation q 1677 = true := by
  have hs : count1675 q = (countLit q [-92, -93]) + (countLit q [-95, -97]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93]) (l₂ := [-95, -97])
  have hm := merge_two (literal (valuation q) (1672)) (literal (valuation q) (1673)) (literal (valuation q) (1677)) (countLit q [-92, -93]) (countLit q [-95, -97]) (count1675 q) 2 1 (meaning1672 q) (meaning1673 q) (meaning1677 q) hs
  change valuation q 1672 = false ∨ valuation q 1673 = false ∨ valuation q 1677 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1326 (q : Snake 81) (h : Conditions q) : valuation q 1672 = false ∨ valuation q 1674 = false ∨ valuation q 1678 = true := by
  have hs : count1675 q = (countLit q [-92, -93]) + (countLit q [-95, -97]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93]) (l₂ := [-95, -97])
  have hm := merge_two (literal (valuation q) (1672)) (literal (valuation q) (1674)) (literal (valuation q) (1678)) (countLit q [-92, -93]) (countLit q [-95, -97]) (count1675 q) 2 2 (meaning1672 q) (meaning1674 q) (meaning1678 q) hs
  change valuation q 1672 = false ∨ valuation q 1674 = false ∨ valuation q 1678 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1327 (q : Snake 81) (h : Conditions q) : valuation q 101 = true ∨ valuation q 1679 = true := by
  have hs : count1679 q = (countLit q [-98]) + (countLit q [-101]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-98]) (l₂ := [-101])
  have hm := merge_right (literal (valuation q) (-101)) (literal (valuation q) (1679)) (countLit q [-98]) (countLit q [-101]) (count1679 q) 1 (meaningNeg101 q) (meaning1679 q) hs
  change (! (valuation q 101)) = false ∨ valuation q 1679 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1328 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 1679 = true := by
  have hs : count1679 q = (countLit q [-98]) + (countLit q [-101]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-98]) (l₂ := [-101])
  have hm := merge_left (literal (valuation q) (-98)) (literal (valuation q) (1679)) (countLit q [-98]) (countLit q [-101]) (count1679 q) 1 (meaningNeg98 q) (meaning1679 q) hs
  change (! (valuation q 98)) = false ∨ valuation q 1679 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1329 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 101 = true ∨ valuation q 1680 = true := by
  have hs : count1679 q = (countLit q [-98]) + (countLit q [-101]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-98]) (l₂ := [-101])
  have hm := merge_two (literal (valuation q) (-98)) (literal (valuation q) (-101)) (literal (valuation q) (1680)) (countLit q [-98]) (countLit q [-101]) (count1679 q) 1 1 (meaningNeg98 q) (meaningNeg101 q) (meaning1680 q) hs
  change (! (valuation q 98)) = false ∨ (! (valuation q 101)) = false ∨ valuation q 1680 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1330 (q : Snake 81) (h : Conditions q) : valuation q 105 = true ∨ valuation q 1681 = true := by
  have hs : count1681 q = (countLit q [-104]) + (countLit q [-105]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-104]) (l₂ := [-105])
  have hm := merge_right (literal (valuation q) (-105)) (literal (valuation q) (1681)) (countLit q [-104]) (countLit q [-105]) (count1681 q) 1 (meaningNeg105 q) (meaning1681 q) hs
  change (! (valuation q 105)) = false ∨ valuation q 1681 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1331 (q : Snake 81) (h : Conditions q) : valuation q 104 = true ∨ valuation q 1681 = true := by
  have hs : count1681 q = (countLit q [-104]) + (countLit q [-105]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-104]) (l₂ := [-105])
  have hm := merge_left (literal (valuation q) (-104)) (literal (valuation q) (1681)) (countLit q [-104]) (countLit q [-105]) (count1681 q) 1 (meaningNeg104 q) (meaning1681 q) hs
  change (! (valuation q 104)) = false ∨ valuation q 1681 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1332 (q : Snake 81) (h : Conditions q) : valuation q 104 = true ∨ valuation q 105 = true ∨ valuation q 1682 = true := by
  have hs : count1681 q = (countLit q [-104]) + (countLit q [-105]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-104]) (l₂ := [-105])
  have hm := merge_two (literal (valuation q) (-104)) (literal (valuation q) (-105)) (literal (valuation q) (1682)) (countLit q [-104]) (countLit q [-105]) (count1681 q) 1 1 (meaningNeg104 q) (meaningNeg105 q) (meaning1682 q) hs
  change (! (valuation q 104)) = false ∨ (! (valuation q 105)) = false ∨ valuation q 1682 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1333 (q : Snake 81) (h : Conditions q) : valuation q 1681 = false ∨ valuation q 1683 = true := by
  have hs : count1683 q = (countLit q [-98, -101]) + (countLit q [-104, -105]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-98, -101]) (l₂ := [-104, -105])
  have hm := merge_right (literal (valuation q) (1681)) (literal (valuation q) (1683)) (countLit q [-98, -101]) (countLit q [-104, -105]) (count1683 q) 1 (meaning1681 q) (meaning1683 q) hs
  change valuation q 1681 = false ∨ valuation q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1334 (q : Snake 81) (h : Conditions q) : valuation q 1682 = false ∨ valuation q 1684 = true := by
  have hs : count1683 q = (countLit q [-98, -101]) + (countLit q [-104, -105]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-98, -101]) (l₂ := [-104, -105])
  have hm := merge_right (literal (valuation q) (1682)) (literal (valuation q) (1684)) (countLit q [-98, -101]) (countLit q [-104, -105]) (count1683 q) 2 (meaning1682 q) (meaning1684 q) hs
  change valuation q 1682 = false ∨ valuation q 1684 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1335 (q : Snake 81) (h : Conditions q) : valuation q 1679 = false ∨ valuation q 1683 = true := by
  have hs : count1683 q = (countLit q [-98, -101]) + (countLit q [-104, -105]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-98, -101]) (l₂ := [-104, -105])
  have hm := merge_left (literal (valuation q) (1679)) (literal (valuation q) (1683)) (countLit q [-98, -101]) (countLit q [-104, -105]) (count1683 q) 1 (meaning1679 q) (meaning1683 q) hs
  change valuation q 1679 = false ∨ valuation q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1336 (q : Snake 81) (h : Conditions q) : valuation q 1679 = false ∨ valuation q 1681 = false ∨ valuation q 1684 = true := by
  have hs : count1683 q = (countLit q [-98, -101]) + (countLit q [-104, -105]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-98, -101]) (l₂ := [-104, -105])
  have hm := merge_two (literal (valuation q) (1679)) (literal (valuation q) (1681)) (literal (valuation q) (1684)) (countLit q [-98, -101]) (countLit q [-104, -105]) (count1683 q) 1 1 (meaning1679 q) (meaning1681 q) (meaning1684 q) hs
  change valuation q 1679 = false ∨ valuation q 1681 = false ∨ valuation q 1684 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1337 (q : Snake 81) (h : Conditions q) : valuation q 1679 = false ∨ valuation q 1682 = false ∨ valuation q 1685 = true := by
  have hs : count1683 q = (countLit q [-98, -101]) + (countLit q [-104, -105]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-98, -101]) (l₂ := [-104, -105])
  have hm := merge_two (literal (valuation q) (1679)) (literal (valuation q) (1682)) (literal (valuation q) (1685)) (countLit q [-98, -101]) (countLit q [-104, -105]) (count1683 q) 1 2 (meaning1679 q) (meaning1682 q) (meaning1685 q) hs
  change valuation q 1679 = false ∨ valuation q 1682 = false ∨ valuation q 1685 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1338 (q : Snake 81) (h : Conditions q) : valuation q 1680 = false ∨ valuation q 1684 = true := by
  have hs : count1683 q = (countLit q [-98, -101]) + (countLit q [-104, -105]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-98, -101]) (l₂ := [-104, -105])
  have hm := merge_left (literal (valuation q) (1680)) (literal (valuation q) (1684)) (countLit q [-98, -101]) (countLit q [-104, -105]) (count1683 q) 2 (meaning1680 q) (meaning1684 q) hs
  change valuation q 1680 = false ∨ valuation q 1684 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1339 (q : Snake 81) (h : Conditions q) : valuation q 1680 = false ∨ valuation q 1681 = false ∨ valuation q 1685 = true := by
  have hs : count1683 q = (countLit q [-98, -101]) + (countLit q [-104, -105]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-98, -101]) (l₂ := [-104, -105])
  have hm := merge_two (literal (valuation q) (1680)) (literal (valuation q) (1681)) (literal (valuation q) (1685)) (countLit q [-98, -101]) (countLit q [-104, -105]) (count1683 q) 2 1 (meaning1680 q) (meaning1681 q) (meaning1685 q) hs
  change valuation q 1680 = false ∨ valuation q 1681 = false ∨ valuation q 1685 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1340 (q : Snake 81) (h : Conditions q) : valuation q 1680 = false ∨ valuation q 1682 = false ∨ valuation q 1686 = true := by
  have hs : count1683 q = (countLit q [-98, -101]) + (countLit q [-104, -105]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-98, -101]) (l₂ := [-104, -105])
  have hm := merge_two (literal (valuation q) (1680)) (literal (valuation q) (1682)) (literal (valuation q) (1686)) (countLit q [-98, -101]) (countLit q [-104, -105]) (count1683 q) 2 2 (meaning1680 q) (meaning1682 q) (meaning1686 q) hs
  change valuation q 1680 = false ∨ valuation q 1682 = false ∨ valuation q 1686 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1341 (q : Snake 81) (h : Conditions q) : valuation q 1683 = false ∨ valuation q 1687 = true := by
  have hs : count1687 q = (countLit q [-92, -93, -95, -97]) + (countLit q [-98, -101, -104, -105]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97]) (l₂ := [-98, -101, -104, -105])
  have hm := merge_right (literal (valuation q) (1683)) (literal (valuation q) (1687)) (countLit q [-92, -93, -95, -97]) (countLit q [-98, -101, -104, -105]) (count1687 q) 1 (meaning1683 q) (meaning1687 q) hs
  change valuation q 1683 = false ∨ valuation q 1687 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1342 (q : Snake 81) (h : Conditions q) : valuation q 1684 = false ∨ valuation q 1688 = true := by
  have hs : count1687 q = (countLit q [-92, -93, -95, -97]) + (countLit q [-98, -101, -104, -105]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97]) (l₂ := [-98, -101, -104, -105])
  have hm := merge_right (literal (valuation q) (1684)) (literal (valuation q) (1688)) (countLit q [-92, -93, -95, -97]) (countLit q [-98, -101, -104, -105]) (count1687 q) 2 (meaning1684 q) (meaning1688 q) hs
  change valuation q 1684 = false ∨ valuation q 1688 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1343 (q : Snake 81) (h : Conditions q) : valuation q 1685 = false ∨ valuation q 1689 = true := by
  have hs : count1687 q = (countLit q [-92, -93, -95, -97]) + (countLit q [-98, -101, -104, -105]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97]) (l₂ := [-98, -101, -104, -105])
  have hm := merge_right (literal (valuation q) (1685)) (literal (valuation q) (1689)) (countLit q [-92, -93, -95, -97]) (countLit q [-98, -101, -104, -105]) (count1687 q) 3 (meaning1685 q) (meaning1689 q) hs
  change valuation q 1685 = false ∨ valuation q 1689 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1344 (q : Snake 81) (h : Conditions q) : valuation q 1686 = false ∨ valuation q 1690 = true := by
  have hs : count1687 q = (countLit q [-92, -93, -95, -97]) + (countLit q [-98, -101, -104, -105]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-92, -93, -95, -97]) (l₂ := [-98, -101, -104, -105])
  have hm := merge_right (literal (valuation q) (1686)) (literal (valuation q) (1690)) (countLit q [-92, -93, -95, -97]) (countLit q [-98, -101, -104, -105]) (count1687 q) 4 (meaning1686 q) (meaning1690 q) hs
  change valuation q 1686 = false ∨ valuation q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem block41 (q : Snake 81) (h : Conditions q) : Dfs112FirstBoolean.Block41 (valuation q) :=
  ⟨clause1313 q h, clause1314 q h, clause1315 q h, clause1316 q h, clause1317 q h, clause1318 q h, clause1319 q h, clause1320 q h, clause1321 q h, clause1322 q h, clause1323 q h, clause1324 q h, clause1325 q h, clause1326 q h, clause1327 q h, clause1328 q h, clause1329 q h, clause1330 q h, clause1331 q h, clause1332 q h, clause1333 q h, clause1334 q h, clause1335 q h, clause1336 q h, clause1337 q h, clause1338 q h, clause1339 q h, clause1340 q h, clause1341 q h, clause1342 q h, clause1343 q h, clause1344 q h⟩

end
end Snake9.Regrowth.First112
