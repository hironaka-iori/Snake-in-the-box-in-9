import First112Semantics
import Dfs112FirstBooleanInputs
namespace Snake9.Regrowth.First112
noncomputable section
local instance blockDec37 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1185 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1571 = false ∨ valuation q 1596 = true := by
  have hs : count1584 q = (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) + (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (l₂ := [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1513)) (literal (valuation q) (1571)) (literal (valuation q) (1596)) (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) (count1584 q) 9 4 (meaning1513 q) (meaning1571 q) (meaning1596 q) hs
  change valuation q 1513 = false ∨ valuation q 1571 = false ∨ valuation q 1596 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1186 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1572 = false ∨ valuation q 1597 = true := by
  have hs : count1584 q = (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) + (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (l₂ := [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1513)) (literal (valuation q) (1572)) (literal (valuation q) (1597)) (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) (count1584 q) 9 5 (meaning1513 q) (meaning1572 q) (meaning1597 q) hs
  change valuation q 1513 = false ∨ valuation q 1572 = false ∨ valuation q 1597 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1187 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 1607 = true := by
  have hs : count1607 q = (countLit q [-61]) + (countLit q [-62]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61]) (l₂ := [-62])
  have hm := merge_right (literal (valuation q) (-62)) (literal (valuation q) (1607)) (countLit q [-61]) (countLit q [-62]) (count1607 q) 1 (meaningNeg62 q) (meaning1607 q) hs
  change (! (valuation q 62)) = false ∨ valuation q 1607 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1188 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 1607 = true := by
  have hs : count1607 q = (countLit q [-61]) + (countLit q [-62]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61]) (l₂ := [-62])
  have hm := merge_left (literal (valuation q) (-61)) (literal (valuation q) (1607)) (countLit q [-61]) (countLit q [-62]) (count1607 q) 1 (meaningNeg61 q) (meaning1607 q) hs
  change (! (valuation q 61)) = false ∨ valuation q 1607 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1189 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 62 = true ∨ valuation q 1608 = true := by
  have hs : count1607 q = (countLit q [-61]) + (countLit q [-62]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61]) (l₂ := [-62])
  have hm := merge_two (literal (valuation q) (-61)) (literal (valuation q) (-62)) (literal (valuation q) (1608)) (countLit q [-61]) (countLit q [-62]) (count1607 q) 1 1 (meaningNeg61 q) (meaningNeg62 q) (meaning1608 q) hs
  change (! (valuation q 61)) = false ∨ (! (valuation q 62)) = false ∨ valuation q 1608 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1190 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 1609 = true := by
  have hs : count1609 q = (countLit q [-64]) + (countLit q [-67]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-64]) (l₂ := [-67])
  have hm := merge_right (literal (valuation q) (-67)) (literal (valuation q) (1609)) (countLit q [-64]) (countLit q [-67]) (count1609 q) 1 (meaningNeg67 q) (meaning1609 q) hs
  change (! (valuation q 67)) = false ∨ valuation q 1609 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1191 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 1609 = true := by
  have hs : count1609 q = (countLit q [-64]) + (countLit q [-67]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-64]) (l₂ := [-67])
  have hm := merge_left (literal (valuation q) (-64)) (literal (valuation q) (1609)) (countLit q [-64]) (countLit q [-67]) (count1609 q) 1 (meaningNeg64 q) (meaning1609 q) hs
  change (! (valuation q 64)) = false ∨ valuation q 1609 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1192 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 67 = true ∨ valuation q 1610 = true := by
  have hs : count1609 q = (countLit q [-64]) + (countLit q [-67]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-64]) (l₂ := [-67])
  have hm := merge_two (literal (valuation q) (-64)) (literal (valuation q) (-67)) (literal (valuation q) (1610)) (countLit q [-64]) (countLit q [-67]) (count1609 q) 1 1 (meaningNeg64 q) (meaningNeg67 q) (meaning1610 q) hs
  change (! (valuation q 64)) = false ∨ (! (valuation q 67)) = false ∨ valuation q 1610 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1193 (q : Snake 81) (h : Conditions q) : valuation q 1609 = false ∨ valuation q 1611 = true := by
  have hs : count1611 q = (countLit q [-61, -62]) + (countLit q [-64, -67]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62]) (l₂ := [-64, -67])
  have hm := merge_right (literal (valuation q) (1609)) (literal (valuation q) (1611)) (countLit q [-61, -62]) (countLit q [-64, -67]) (count1611 q) 1 (meaning1609 q) (meaning1611 q) hs
  change valuation q 1609 = false ∨ valuation q 1611 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1194 (q : Snake 81) (h : Conditions q) : valuation q 1610 = false ∨ valuation q 1612 = true := by
  have hs : count1611 q = (countLit q [-61, -62]) + (countLit q [-64, -67]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62]) (l₂ := [-64, -67])
  have hm := merge_right (literal (valuation q) (1610)) (literal (valuation q) (1612)) (countLit q [-61, -62]) (countLit q [-64, -67]) (count1611 q) 2 (meaning1610 q) (meaning1612 q) hs
  change valuation q 1610 = false ∨ valuation q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1195 (q : Snake 81) (h : Conditions q) : valuation q 1607 = false ∨ valuation q 1611 = true := by
  have hs : count1611 q = (countLit q [-61, -62]) + (countLit q [-64, -67]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62]) (l₂ := [-64, -67])
  have hm := merge_left (literal (valuation q) (1607)) (literal (valuation q) (1611)) (countLit q [-61, -62]) (countLit q [-64, -67]) (count1611 q) 1 (meaning1607 q) (meaning1611 q) hs
  change valuation q 1607 = false ∨ valuation q 1611 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1196 (q : Snake 81) (h : Conditions q) : valuation q 1607 = false ∨ valuation q 1609 = false ∨ valuation q 1612 = true := by
  have hs : count1611 q = (countLit q [-61, -62]) + (countLit q [-64, -67]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62]) (l₂ := [-64, -67])
  have hm := merge_two (literal (valuation q) (1607)) (literal (valuation q) (1609)) (literal (valuation q) (1612)) (countLit q [-61, -62]) (countLit q [-64, -67]) (count1611 q) 1 1 (meaning1607 q) (meaning1609 q) (meaning1612 q) hs
  change valuation q 1607 = false ∨ valuation q 1609 = false ∨ valuation q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1197 (q : Snake 81) (h : Conditions q) : valuation q 1607 = false ∨ valuation q 1610 = false ∨ valuation q 1613 = true := by
  have hs : count1611 q = (countLit q [-61, -62]) + (countLit q [-64, -67]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62]) (l₂ := [-64, -67])
  have hm := merge_two (literal (valuation q) (1607)) (literal (valuation q) (1610)) (literal (valuation q) (1613)) (countLit q [-61, -62]) (countLit q [-64, -67]) (count1611 q) 1 2 (meaning1607 q) (meaning1610 q) (meaning1613 q) hs
  change valuation q 1607 = false ∨ valuation q 1610 = false ∨ valuation q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1198 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1612 = true := by
  have hs : count1611 q = (countLit q [-61, -62]) + (countLit q [-64, -67]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62]) (l₂ := [-64, -67])
  have hm := merge_left (literal (valuation q) (1608)) (literal (valuation q) (1612)) (countLit q [-61, -62]) (countLit q [-64, -67]) (count1611 q) 2 (meaning1608 q) (meaning1612 q) hs
  change valuation q 1608 = false ∨ valuation q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1199 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1609 = false ∨ valuation q 1613 = true := by
  have hs : count1611 q = (countLit q [-61, -62]) + (countLit q [-64, -67]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62]) (l₂ := [-64, -67])
  have hm := merge_two (literal (valuation q) (1608)) (literal (valuation q) (1609)) (literal (valuation q) (1613)) (countLit q [-61, -62]) (countLit q [-64, -67]) (count1611 q) 2 1 (meaning1608 q) (meaning1609 q) (meaning1613 q) hs
  change valuation q 1608 = false ∨ valuation q 1609 = false ∨ valuation q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1200 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1610 = false ∨ valuation q 1614 = true := by
  have hs : count1611 q = (countLit q [-61, -62]) + (countLit q [-64, -67]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62]) (l₂ := [-64, -67])
  have hm := merge_two (literal (valuation q) (1608)) (literal (valuation q) (1610)) (literal (valuation q) (1614)) (countLit q [-61, -62]) (countLit q [-64, -67]) (count1611 q) 2 2 (meaning1608 q) (meaning1610 q) (meaning1614 q) hs
  change valuation q 1608 = false ∨ valuation q 1610 = false ∨ valuation q 1614 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1201 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 1615 = true := by
  have hs : count1615 q = (countLit q [-68]) + (countLit q [-69]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-68]) (l₂ := [-69])
  have hm := merge_right (literal (valuation q) (-69)) (literal (valuation q) (1615)) (countLit q [-68]) (countLit q [-69]) (count1615 q) 1 (meaningNeg69 q) (meaning1615 q) hs
  change (! (valuation q 69)) = false ∨ valuation q 1615 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1202 (q : Snake 81) (h : Conditions q) : valuation q 68 = true ∨ valuation q 1615 = true := by
  have hs : count1615 q = (countLit q [-68]) + (countLit q [-69]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-68]) (l₂ := [-69])
  have hm := merge_left (literal (valuation q) (-68)) (literal (valuation q) (1615)) (countLit q [-68]) (countLit q [-69]) (count1615 q) 1 (meaningNeg68 q) (meaning1615 q) hs
  change (! (valuation q 68)) = false ∨ valuation q 1615 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1203 (q : Snake 81) (h : Conditions q) : valuation q 68 = true ∨ valuation q 69 = true ∨ valuation q 1616 = true := by
  have hs : count1615 q = (countLit q [-68]) + (countLit q [-69]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-68]) (l₂ := [-69])
  have hm := merge_two (literal (valuation q) (-68)) (literal (valuation q) (-69)) (literal (valuation q) (1616)) (countLit q [-68]) (countLit q [-69]) (count1615 q) 1 1 (meaningNeg68 q) (meaningNeg69 q) (meaning1616 q) hs
  change (! (valuation q 68)) = false ∨ (! (valuation q 69)) = false ∨ valuation q 1616 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1204 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 1617 = true := by
  have hs : count1617 q = (countLit q [-72]) + (countLit q [-73]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-72]) (l₂ := [-73])
  have hm := merge_right (literal (valuation q) (-73)) (literal (valuation q) (1617)) (countLit q [-72]) (countLit q [-73]) (count1617 q) 1 (meaningNeg73 q) (meaning1617 q) hs
  change (! (valuation q 73)) = false ∨ valuation q 1617 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1205 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 1617 = true := by
  have hs : count1617 q = (countLit q [-72]) + (countLit q [-73]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-72]) (l₂ := [-73])
  have hm := merge_left (literal (valuation q) (-72)) (literal (valuation q) (1617)) (countLit q [-72]) (countLit q [-73]) (count1617 q) 1 (meaningNeg72 q) (meaning1617 q) hs
  change (! (valuation q 72)) = false ∨ valuation q 1617 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1206 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 73 = true ∨ valuation q 1618 = true := by
  have hs : count1617 q = (countLit q [-72]) + (countLit q [-73]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-72]) (l₂ := [-73])
  have hm := merge_two (literal (valuation q) (-72)) (literal (valuation q) (-73)) (literal (valuation q) (1618)) (countLit q [-72]) (countLit q [-73]) (count1617 q) 1 1 (meaningNeg72 q) (meaningNeg73 q) (meaning1618 q) hs
  change (! (valuation q 72)) = false ∨ (! (valuation q 73)) = false ∨ valuation q 1618 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1207 (q : Snake 81) (h : Conditions q) : valuation q 1617 = false ∨ valuation q 1619 = true := by
  have hs : count1619 q = (countLit q [-68, -69]) + (countLit q [-72, -73]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-68, -69]) (l₂ := [-72, -73])
  have hm := merge_right (literal (valuation q) (1617)) (literal (valuation q) (1619)) (countLit q [-68, -69]) (countLit q [-72, -73]) (count1619 q) 1 (meaning1617 q) (meaning1619 q) hs
  change valuation q 1617 = false ∨ valuation q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1208 (q : Snake 81) (h : Conditions q) : valuation q 1618 = false ∨ valuation q 1620 = true := by
  have hs : count1619 q = (countLit q [-68, -69]) + (countLit q [-72, -73]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-68, -69]) (l₂ := [-72, -73])
  have hm := merge_right (literal (valuation q) (1618)) (literal (valuation q) (1620)) (countLit q [-68, -69]) (countLit q [-72, -73]) (count1619 q) 2 (meaning1618 q) (meaning1620 q) hs
  change valuation q 1618 = false ∨ valuation q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1209 (q : Snake 81) (h : Conditions q) : valuation q 1615 = false ∨ valuation q 1619 = true := by
  have hs : count1619 q = (countLit q [-68, -69]) + (countLit q [-72, -73]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-68, -69]) (l₂ := [-72, -73])
  have hm := merge_left (literal (valuation q) (1615)) (literal (valuation q) (1619)) (countLit q [-68, -69]) (countLit q [-72, -73]) (count1619 q) 1 (meaning1615 q) (meaning1619 q) hs
  change valuation q 1615 = false ∨ valuation q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1210 (q : Snake 81) (h : Conditions q) : valuation q 1615 = false ∨ valuation q 1617 = false ∨ valuation q 1620 = true := by
  have hs : count1619 q = (countLit q [-68, -69]) + (countLit q [-72, -73]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-68, -69]) (l₂ := [-72, -73])
  have hm := merge_two (literal (valuation q) (1615)) (literal (valuation q) (1617)) (literal (valuation q) (1620)) (countLit q [-68, -69]) (countLit q [-72, -73]) (count1619 q) 1 1 (meaning1615 q) (meaning1617 q) (meaning1620 q) hs
  change valuation q 1615 = false ∨ valuation q 1617 = false ∨ valuation q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1211 (q : Snake 81) (h : Conditions q) : valuation q 1615 = false ∨ valuation q 1618 = false ∨ valuation q 1621 = true := by
  have hs : count1619 q = (countLit q [-68, -69]) + (countLit q [-72, -73]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-68, -69]) (l₂ := [-72, -73])
  have hm := merge_two (literal (valuation q) (1615)) (literal (valuation q) (1618)) (literal (valuation q) (1621)) (countLit q [-68, -69]) (countLit q [-72, -73]) (count1619 q) 1 2 (meaning1615 q) (meaning1618 q) (meaning1621 q) hs
  change valuation q 1615 = false ∨ valuation q 1618 = false ∨ valuation q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1212 (q : Snake 81) (h : Conditions q) : valuation q 1616 = false ∨ valuation q 1617 = false ∨ valuation q 1621 = true := by
  have hs : count1619 q = (countLit q [-68, -69]) + (countLit q [-72, -73]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-68, -69]) (l₂ := [-72, -73])
  have hm := merge_two (literal (valuation q) (1616)) (literal (valuation q) (1617)) (literal (valuation q) (1621)) (countLit q [-68, -69]) (countLit q [-72, -73]) (count1619 q) 2 1 (meaning1616 q) (meaning1617 q) (meaning1621 q) hs
  change valuation q 1616 = false ∨ valuation q 1617 = false ∨ valuation q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1213 (q : Snake 81) (h : Conditions q) : valuation q 1616 = false ∨ valuation q 1618 = false ∨ valuation q 1622 = true := by
  have hs : count1619 q = (countLit q [-68, -69]) + (countLit q [-72, -73]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-68, -69]) (l₂ := [-72, -73])
  have hm := merge_two (literal (valuation q) (1616)) (literal (valuation q) (1618)) (literal (valuation q) (1622)) (countLit q [-68, -69]) (countLit q [-72, -73]) (count1619 q) 2 2 (meaning1616 q) (meaning1618 q) (meaning1622 q) hs
  change valuation q 1616 = false ∨ valuation q 1618 = false ∨ valuation q 1622 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1214 (q : Snake 81) (h : Conditions q) : valuation q 1619 = false ∨ valuation q 1623 = true := by
  have hs : count1623 q = (countLit q [-61, -62, -64, -67]) + (countLit q [-68, -69, -72, -73]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67]) (l₂ := [-68, -69, -72, -73])
  have hm := merge_right (literal (valuation q) (1619)) (literal (valuation q) (1623)) (countLit q [-61, -62, -64, -67]) (countLit q [-68, -69, -72, -73]) (count1623 q) 1 (meaning1619 q) (meaning1623 q) hs
  change valuation q 1619 = false ∨ valuation q 1623 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1215 (q : Snake 81) (h : Conditions q) : valuation q 1620 = false ∨ valuation q 1624 = true := by
  have hs : count1623 q = (countLit q [-61, -62, -64, -67]) + (countLit q [-68, -69, -72, -73]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67]) (l₂ := [-68, -69, -72, -73])
  have hm := merge_right (literal (valuation q) (1620)) (literal (valuation q) (1624)) (countLit q [-61, -62, -64, -67]) (countLit q [-68, -69, -72, -73]) (count1623 q) 2 (meaning1620 q) (meaning1624 q) hs
  change valuation q 1620 = false ∨ valuation q 1624 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1216 (q : Snake 81) (h : Conditions q) : valuation q 1621 = false ∨ valuation q 1625 = true := by
  have hs : count1623 q = (countLit q [-61, -62, -64, -67]) + (countLit q [-68, -69, -72, -73]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-61, -62, -64, -67]) (l₂ := [-68, -69, -72, -73])
  have hm := merge_right (literal (valuation q) (1621)) (literal (valuation q) (1625)) (countLit q [-61, -62, -64, -67]) (countLit q [-68, -69, -72, -73]) (count1623 q) 3 (meaning1621 q) (meaning1625 q) hs
  change valuation q 1621 = false ∨ valuation q 1625 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem block37 (q : Snake 81) (h : Conditions q) : Dfs112FirstBoolean.Block37 (valuation q) :=
  ⟨clause1185 q h, clause1186 q h, clause1187 q h, clause1188 q h, clause1189 q h, clause1190 q h, clause1191 q h, clause1192 q h, clause1193 q h, clause1194 q h, clause1195 q h, clause1196 q h, clause1197 q h, clause1198 q h, clause1199 q h, clause1200 q h, clause1201 q h, clause1202 q h, clause1203 q h, clause1204 q h, clause1205 q h, clause1206 q h, clause1207 q h, clause1208 q h, clause1209 q h, clause1210 q h, clause1211 q h, clause1212 q h, clause1213 q h, clause1214 q h, clause1215 q h, clause1216 q h⟩

end
end Snake9.Regrowth.First112
