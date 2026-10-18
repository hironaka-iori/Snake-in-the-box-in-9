import First112Semantics
import Dfs112FirstBooleanInputs
namespace Snake9.Regrowth.First112
noncomputable section
local instance blockDec38 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1217 (q : Snake 81) (h : Conditions q) : valuation q 1622 = false ∨ valuation q 1626 = true := by
  have hs : count1623 q = (countLit q [-61, -62, -64, -67]) + (countLit q [-68, -69, -72, -73]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67]) (l₂ := [-68, -69, -72, -73])
  have hm := merge_right (literal (valuation q) (1622)) (literal (valuation q) (1626)) (countLit q [-61, -62, -64, -67]) (countLit q [-68, -69, -72, -73]) (count1623 q) 4 (meaning1622 q) (meaning1626 q) hs
  change valuation q 1622 = false ∨ valuation q 1626 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1218 (q : Snake 81) (h : Conditions q) : valuation q 1611 = false ∨ valuation q 1623 = true := by
  have hs : count1623 q = (countLit q [-61, -62, -64, -67]) + (countLit q [-68, -69, -72, -73]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67]) (l₂ := [-68, -69, -72, -73])
  have hm := merge_left (literal (valuation q) (1611)) (literal (valuation q) (1623)) (countLit q [-61, -62, -64, -67]) (countLit q [-68, -69, -72, -73]) (count1623 q) 1 (meaning1611 q) (meaning1623 q) hs
  change valuation q 1611 = false ∨ valuation q 1623 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1219 (q : Snake 81) (h : Conditions q) : valuation q 1611 = false ∨ valuation q 1619 = false ∨ valuation q 1624 = true := by
  have hs : count1623 q = (countLit q [-61, -62, -64, -67]) + (countLit q [-68, -69, -72, -73]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67]) (l₂ := [-68, -69, -72, -73])
  have hm := merge_two (literal (valuation q) (1611)) (literal (valuation q) (1619)) (literal (valuation q) (1624)) (countLit q [-61, -62, -64, -67]) (countLit q [-68, -69, -72, -73]) (count1623 q) 1 1 (meaning1611 q) (meaning1619 q) (meaning1624 q) hs
  change valuation q 1611 = false ∨ valuation q 1619 = false ∨ valuation q 1624 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1220 (q : Snake 81) (h : Conditions q) : valuation q 1611 = false ∨ valuation q 1620 = false ∨ valuation q 1625 = true := by
  have hs : count1623 q = (countLit q [-61, -62, -64, -67]) + (countLit q [-68, -69, -72, -73]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67]) (l₂ := [-68, -69, -72, -73])
  have hm := merge_two (literal (valuation q) (1611)) (literal (valuation q) (1620)) (literal (valuation q) (1625)) (countLit q [-61, -62, -64, -67]) (countLit q [-68, -69, -72, -73]) (count1623 q) 1 2 (meaning1611 q) (meaning1620 q) (meaning1625 q) hs
  change valuation q 1611 = false ∨ valuation q 1620 = false ∨ valuation q 1625 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1221 (q : Snake 81) (h : Conditions q) : valuation q 1611 = false ∨ valuation q 1621 = false ∨ valuation q 1626 = true := by
  have hs : count1623 q = (countLit q [-61, -62, -64, -67]) + (countLit q [-68, -69, -72, -73]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67]) (l₂ := [-68, -69, -72, -73])
  have hm := merge_two (literal (valuation q) (1611)) (literal (valuation q) (1621)) (literal (valuation q) (1626)) (countLit q [-61, -62, -64, -67]) (countLit q [-68, -69, -72, -73]) (count1623 q) 1 3 (meaning1611 q) (meaning1621 q) (meaning1626 q) hs
  change valuation q 1611 = false ∨ valuation q 1621 = false ∨ valuation q 1626 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1222 (q : Snake 81) (h : Conditions q) : valuation q 1611 = false ∨ valuation q 1622 = false ∨ valuation q 1627 = true := by
  have hs : count1623 q = (countLit q [-61, -62, -64, -67]) + (countLit q [-68, -69, -72, -73]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67]) (l₂ := [-68, -69, -72, -73])
  have hm := merge_two (literal (valuation q) (1611)) (literal (valuation q) (1622)) (literal (valuation q) (1627)) (countLit q [-61, -62, -64, -67]) (countLit q [-68, -69, -72, -73]) (count1623 q) 1 4 (meaning1611 q) (meaning1622 q) (meaning1627 q) hs
  change valuation q 1611 = false ∨ valuation q 1622 = false ∨ valuation q 1627 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1223 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1624 = true := by
  have hs : count1623 q = (countLit q [-61, -62, -64, -67]) + (countLit q [-68, -69, -72, -73]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67]) (l₂ := [-68, -69, -72, -73])
  have hm := merge_left (literal (valuation q) (1612)) (literal (valuation q) (1624)) (countLit q [-61, -62, -64, -67]) (countLit q [-68, -69, -72, -73]) (count1623 q) 2 (meaning1612 q) (meaning1624 q) hs
  change valuation q 1612 = false ∨ valuation q 1624 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1224 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1619 = false ∨ valuation q 1625 = true := by
  have hs : count1623 q = (countLit q [-61, -62, -64, -67]) + (countLit q [-68, -69, -72, -73]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67]) (l₂ := [-68, -69, -72, -73])
  have hm := merge_two (literal (valuation q) (1612)) (literal (valuation q) (1619)) (literal (valuation q) (1625)) (countLit q [-61, -62, -64, -67]) (countLit q [-68, -69, -72, -73]) (count1623 q) 2 1 (meaning1612 q) (meaning1619 q) (meaning1625 q) hs
  change valuation q 1612 = false ∨ valuation q 1619 = false ∨ valuation q 1625 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1225 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1620 = false ∨ valuation q 1626 = true := by
  have hs : count1623 q = (countLit q [-61, -62, -64, -67]) + (countLit q [-68, -69, -72, -73]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67]) (l₂ := [-68, -69, -72, -73])
  have hm := merge_two (literal (valuation q) (1612)) (literal (valuation q) (1620)) (literal (valuation q) (1626)) (countLit q [-61, -62, -64, -67]) (countLit q [-68, -69, -72, -73]) (count1623 q) 2 2 (meaning1612 q) (meaning1620 q) (meaning1626 q) hs
  change valuation q 1612 = false ∨ valuation q 1620 = false ∨ valuation q 1626 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1226 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1621 = false ∨ valuation q 1627 = true := by
  have hs : count1623 q = (countLit q [-61, -62, -64, -67]) + (countLit q [-68, -69, -72, -73]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67]) (l₂ := [-68, -69, -72, -73])
  have hm := merge_two (literal (valuation q) (1612)) (literal (valuation q) (1621)) (literal (valuation q) (1627)) (countLit q [-61, -62, -64, -67]) (countLit q [-68, -69, -72, -73]) (count1623 q) 2 3 (meaning1612 q) (meaning1621 q) (meaning1627 q) hs
  change valuation q 1612 = false ∨ valuation q 1621 = false ∨ valuation q 1627 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1227 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1622 = false ∨ valuation q 1628 = true := by
  have hs : count1623 q = (countLit q [-61, -62, -64, -67]) + (countLit q [-68, -69, -72, -73]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67]) (l₂ := [-68, -69, -72, -73])
  have hm := merge_two (literal (valuation q) (1612)) (literal (valuation q) (1622)) (literal (valuation q) (1628)) (countLit q [-61, -62, -64, -67]) (countLit q [-68, -69, -72, -73]) (count1623 q) 2 4 (meaning1612 q) (meaning1622 q) (meaning1628 q) hs
  change valuation q 1612 = false ∨ valuation q 1622 = false ∨ valuation q 1628 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1228 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1625 = true := by
  have hs : count1623 q = (countLit q [-61, -62, -64, -67]) + (countLit q [-68, -69, -72, -73]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67]) (l₂ := [-68, -69, -72, -73])
  have hm := merge_left (literal (valuation q) (1613)) (literal (valuation q) (1625)) (countLit q [-61, -62, -64, -67]) (countLit q [-68, -69, -72, -73]) (count1623 q) 3 (meaning1613 q) (meaning1625 q) hs
  change valuation q 1613 = false ∨ valuation q 1625 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1229 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1619 = false ∨ valuation q 1626 = true := by
  have hs : count1623 q = (countLit q [-61, -62, -64, -67]) + (countLit q [-68, -69, -72, -73]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67]) (l₂ := [-68, -69, -72, -73])
  have hm := merge_two (literal (valuation q) (1613)) (literal (valuation q) (1619)) (literal (valuation q) (1626)) (countLit q [-61, -62, -64, -67]) (countLit q [-68, -69, -72, -73]) (count1623 q) 3 1 (meaning1613 q) (meaning1619 q) (meaning1626 q) hs
  change valuation q 1613 = false ∨ valuation q 1619 = false ∨ valuation q 1626 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1230 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1620 = false ∨ valuation q 1627 = true := by
  have hs : count1623 q = (countLit q [-61, -62, -64, -67]) + (countLit q [-68, -69, -72, -73]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67]) (l₂ := [-68, -69, -72, -73])
  have hm := merge_two (literal (valuation q) (1613)) (literal (valuation q) (1620)) (literal (valuation q) (1627)) (countLit q [-61, -62, -64, -67]) (countLit q [-68, -69, -72, -73]) (count1623 q) 3 2 (meaning1613 q) (meaning1620 q) (meaning1627 q) hs
  change valuation q 1613 = false ∨ valuation q 1620 = false ∨ valuation q 1627 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1231 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1621 = false ∨ valuation q 1628 = true := by
  have hs : count1623 q = (countLit q [-61, -62, -64, -67]) + (countLit q [-68, -69, -72, -73]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67]) (l₂ := [-68, -69, -72, -73])
  have hm := merge_two (literal (valuation q) (1613)) (literal (valuation q) (1621)) (literal (valuation q) (1628)) (countLit q [-61, -62, -64, -67]) (countLit q [-68, -69, -72, -73]) (count1623 q) 3 3 (meaning1613 q) (meaning1621 q) (meaning1628 q) hs
  change valuation q 1613 = false ∨ valuation q 1621 = false ∨ valuation q 1628 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1232 (q : Snake 81) (h : Conditions q) : valuation q 1614 = false ∨ valuation q 1619 = false ∨ valuation q 1627 = true := by
  have hs : count1623 q = (countLit q [-61, -62, -64, -67]) + (countLit q [-68, -69, -72, -73]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67]) (l₂ := [-68, -69, -72, -73])
  have hm := merge_two (literal (valuation q) (1614)) (literal (valuation q) (1619)) (literal (valuation q) (1627)) (countLit q [-61, -62, -64, -67]) (countLit q [-68, -69, -72, -73]) (count1623 q) 4 1 (meaning1614 q) (meaning1619 q) (meaning1627 q) hs
  change valuation q 1614 = false ∨ valuation q 1619 = false ∨ valuation q 1627 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1233 (q : Snake 81) (h : Conditions q) : valuation q 1614 = false ∨ valuation q 1620 = false ∨ valuation q 1628 = true := by
  have hs : count1623 q = (countLit q [-61, -62, -64, -67]) + (countLit q [-68, -69, -72, -73]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67]) (l₂ := [-68, -69, -72, -73])
  have hm := merge_two (literal (valuation q) (1614)) (literal (valuation q) (1620)) (literal (valuation q) (1628)) (countLit q [-61, -62, -64, -67]) (countLit q [-68, -69, -72, -73]) (count1623 q) 4 2 (meaning1614 q) (meaning1620 q) (meaning1628 q) hs
  change valuation q 1614 = false ∨ valuation q 1620 = false ∨ valuation q 1628 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1234 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 1631 = true := by
  have hs : count1631 q = (countLit q [-76]) + (countLit q [-77]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-76]) (l₂ := [-77])
  have hm := merge_right (literal (valuation q) (-77)) (literal (valuation q) (1631)) (countLit q [-76]) (countLit q [-77]) (count1631 q) 1 (meaningNeg77 q) (meaning1631 q) hs
  change (! (valuation q 77)) = false ∨ valuation q 1631 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1235 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 1633 = true := by
  have hs : count1633 q = (countLit q [-79]) + (countLit q [-80]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-79]) (l₂ := [-80])
  have hm := merge_right (literal (valuation q) (-80)) (literal (valuation q) (1633)) (countLit q [-79]) (countLit q [-80]) (count1633 q) 1 (meaningNeg80 q) (meaning1633 q) hs
  change (! (valuation q 80)) = false ∨ valuation q 1633 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1236 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 1633 = true := by
  have hs : count1633 q = (countLit q [-79]) + (countLit q [-80]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-79]) (l₂ := [-80])
  have hm := merge_left (literal (valuation q) (-79)) (literal (valuation q) (1633)) (countLit q [-79]) (countLit q [-80]) (count1633 q) 1 (meaningNeg79 q) (meaning1633 q) hs
  change (! (valuation q 79)) = false ∨ valuation q 1633 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1237 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 80 = true ∨ valuation q 1634 = true := by
  have hs : count1633 q = (countLit q [-79]) + (countLit q [-80]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-79]) (l₂ := [-80])
  have hm := merge_two (literal (valuation q) (-79)) (literal (valuation q) (-80)) (literal (valuation q) (1634)) (countLit q [-79]) (countLit q [-80]) (count1633 q) 1 1 (meaningNeg79 q) (meaningNeg80 q) (meaning1634 q) hs
  change (! (valuation q 79)) = false ∨ (! (valuation q 80)) = false ∨ valuation q 1634 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1238 (q : Snake 81) (h : Conditions q) : valuation q 1633 = false ∨ valuation q 1635 = true := by
  have hs : count1635 q = (countLit q [-76, -77]) + (countLit q [-79, -80]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-76, -77]) (l₂ := [-79, -80])
  have hm := merge_right (literal (valuation q) (1633)) (literal (valuation q) (1635)) (countLit q [-76, -77]) (countLit q [-79, -80]) (count1635 q) 1 (meaning1633 q) (meaning1635 q) hs
  change valuation q 1633 = false ∨ valuation q 1635 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1239 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1636 = true := by
  have hs : count1635 q = (countLit q [-76, -77]) + (countLit q [-79, -80]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-76, -77]) (l₂ := [-79, -80])
  have hm := merge_right (literal (valuation q) (1634)) (literal (valuation q) (1636)) (countLit q [-76, -77]) (countLit q [-79, -80]) (count1635 q) 2 (meaning1634 q) (meaning1636 q) hs
  change valuation q 1634 = false ∨ valuation q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1240 (q : Snake 81) (h : Conditions q) : valuation q 1631 = false ∨ valuation q 1635 = true := by
  have hs : count1635 q = (countLit q [-76, -77]) + (countLit q [-79, -80]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-76, -77]) (l₂ := [-79, -80])
  have hm := merge_left (literal (valuation q) (1631)) (literal (valuation q) (1635)) (countLit q [-76, -77]) (countLit q [-79, -80]) (count1635 q) 1 (meaning1631 q) (meaning1635 q) hs
  change valuation q 1631 = false ∨ valuation q 1635 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1241 (q : Snake 81) (h : Conditions q) : valuation q 1631 = false ∨ valuation q 1633 = false ∨ valuation q 1636 = true := by
  have hs : count1635 q = (countLit q [-76, -77]) + (countLit q [-79, -80]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-76, -77]) (l₂ := [-79, -80])
  have hm := merge_two (literal (valuation q) (1631)) (literal (valuation q) (1633)) (literal (valuation q) (1636)) (countLit q [-76, -77]) (countLit q [-79, -80]) (count1635 q) 1 1 (meaning1631 q) (meaning1633 q) (meaning1636 q) hs
  change valuation q 1631 = false ∨ valuation q 1633 = false ∨ valuation q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1242 (q : Snake 81) (h : Conditions q) : valuation q 1631 = false ∨ valuation q 1634 = false ∨ valuation q 1637 = true := by
  have hs : count1635 q = (countLit q [-76, -77]) + (countLit q [-79, -80]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-76, -77]) (l₂ := [-79, -80])
  have hm := merge_two (literal (valuation q) (1631)) (literal (valuation q) (1634)) (literal (valuation q) (1637)) (countLit q [-76, -77]) (countLit q [-79, -80]) (count1635 q) 1 2 (meaning1631 q) (meaning1634 q) (meaning1637 q) hs
  change valuation q 1631 = false ∨ valuation q 1634 = false ∨ valuation q 1637 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1243 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 1639 = true := by
  have hs : count1639 q = (countLit q [-84]) + (countLit q [-85]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-84]) (l₂ := [-85])
  have hm := merge_right (literal (valuation q) (-85)) (literal (valuation q) (1639)) (countLit q [-84]) (countLit q [-85]) (count1639 q) 1 (meaningNeg85 q) (meaning1639 q) hs
  change (! (valuation q 85)) = false ∨ valuation q 1639 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1244 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 1639 = true := by
  have hs : count1639 q = (countLit q [-84]) + (countLit q [-85]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-84]) (l₂ := [-85])
  have hm := merge_left (literal (valuation q) (-84)) (literal (valuation q) (1639)) (countLit q [-84]) (countLit q [-85]) (count1639 q) 1 (meaningNeg84 q) (meaning1639 q) hs
  change (! (valuation q 84)) = false ∨ valuation q 1639 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1245 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 85 = true ∨ valuation q 1640 = true := by
  have hs : count1639 q = (countLit q [-84]) + (countLit q [-85]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-84]) (l₂ := [-85])
  have hm := merge_two (literal (valuation q) (-84)) (literal (valuation q) (-85)) (literal (valuation q) (1640)) (countLit q [-84]) (countLit q [-85]) (count1639 q) 1 1 (meaningNeg84 q) (meaningNeg85 q) (meaning1640 q) hs
  change (! (valuation q 84)) = false ∨ (! (valuation q 85)) = false ∨ valuation q 1640 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1246 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 1641 = true := by
  have hs : count1641 q = (countLit q [-88]) + (countLit q [-90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-88]) (l₂ := [-90])
  have hm := merge_right (literal (valuation q) (-90)) (literal (valuation q) (1641)) (countLit q [-88]) (countLit q [-90]) (count1641 q) 1 (meaningNeg90 q) (meaning1641 q) hs
  change (! (valuation q 90)) = false ∨ valuation q 1641 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1247 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 1641 = true := by
  have hs : count1641 q = (countLit q [-88]) + (countLit q [-90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-88]) (l₂ := [-90])
  have hm := merge_left (literal (valuation q) (-88)) (literal (valuation q) (1641)) (countLit q [-88]) (countLit q [-90]) (count1641 q) 1 (meaningNeg88 q) (meaning1641 q) hs
  change (! (valuation q 88)) = false ∨ valuation q 1641 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1248 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 90 = true ∨ valuation q 1642 = true := by
  have hs : count1641 q = (countLit q [-88]) + (countLit q [-90]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-88]) (l₂ := [-90])
  have hm := merge_two (literal (valuation q) (-88)) (literal (valuation q) (-90)) (literal (valuation q) (1642)) (countLit q [-88]) (countLit q [-90]) (count1641 q) 1 1 (meaningNeg88 q) (meaningNeg90 q) (meaning1642 q) hs
  change (! (valuation q 88)) = false ∨ (! (valuation q 90)) = false ∨ valuation q 1642 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem block38 (q : Snake 81) (h : Conditions q) : Dfs112FirstBoolean.Block38 (valuation q) :=
  ⟨clause1217 q h, clause1218 q h, clause1219 q h, clause1220 q h, clause1221 q h, clause1222 q h, clause1223 q h, clause1224 q h, clause1225 q h, clause1226 q h, clause1227 q h, clause1228 q h, clause1229 q h, clause1230 q h, clause1231 q h, clause1232 q h, clause1233 q h, clause1234 q h, clause1235 q h, clause1236 q h, clause1237 q h, clause1238 q h, clause1239 q h, clause1240 q h, clause1241 q h, clause1242 q h, clause1243 q h, clause1244 q h, clause1245 q h, clause1246 q h, clause1247 q h, clause1248 q h⟩

end
end Snake9.Regrowth.First112
