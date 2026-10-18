import E112203Semantics
import B112E203Inputs
namespace Snake9.Regrowth.E112203
noncomputable section
local instance blockDec38 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1217 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 1603 = true := by
  have hs : count1603 q = (countLit q [-99]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-100])
  have hm := merge_left (literal (valuationOf q) (-99)) (literal (valuationOf q) (1603)) (countLit q [-99]) (countLit q [-100]) (count1603 q) 1 (meaningNeg99 q) (meaning1603 q) hs
  change (! (valuationOf q 99)) = false ∨ valuationOf q 1603 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1217 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 1603 = true := counterClause1217 (baseVal q)

theorem counterClause1218 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1605 = true := by
  have hs : count1605 q = (countLit q [-95, -98]) + (countLit q [-99, -100]) := List.countP_append (p := literal q) (l₁ := [-95, -98]) (l₂ := [-99, -100])
  have hm := merge_left (literal (valuationOf q) (1601)) (literal (valuationOf q) (1605)) (countLit q [-95, -98]) (countLit q [-99, -100]) (count1605 q) 1 (meaning1601 q) (meaning1605 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1218 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1605 = true := counterClause1218 (baseVal q)

theorem counterClause1219 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1606 = true := by
  have hs : count1605 q = (countLit q [-95, -98]) + (countLit q [-99, -100]) := List.countP_append (p := literal q) (l₁ := [-95, -98]) (l₂ := [-99, -100])
  have hm := merge_two (literal (valuationOf q) (1601)) (literal (valuationOf q) (1603)) (literal (valuationOf q) (1606)) (countLit q [-95, -98]) (countLit q [-99, -100]) (count1605 q) 1 1 (meaning1601 q) (meaning1603 q) (meaning1606 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1219 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1603 = false ∨ valuation q 1606 = true := counterClause1219 (baseVal q)

theorem counterClause1220 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1609 = true := by
  have hs : count1609 q = (countLit q [-90, -92, -93]) + (countLit q [-95, -98, -99, -100]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93]) (l₂ := [-95, -98, -99, -100])
  have hm := merge_right (literal (valuationOf q) (1605)) (literal (valuationOf q) (1609)) (countLit q [-90, -92, -93]) (countLit q [-95, -98, -99, -100]) (count1609 q) 1 (meaning1605 q) (meaning1609 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1220 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1609 = true := counterClause1220 (baseVal q)

theorem counterClause1221 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1610 = true := by
  have hs : count1609 q = (countLit q [-90, -92, -93]) + (countLit q [-95, -98, -99, -100]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93]) (l₂ := [-95, -98, -99, -100])
  have hm := merge_right (literal (valuationOf q) (1606)) (literal (valuationOf q) (1610)) (countLit q [-90, -92, -93]) (countLit q [-95, -98, -99, -100]) (count1609 q) 2 (meaning1606 q) (meaning1610 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1221 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1610 = true := counterClause1221 (baseVal q)

theorem counterClause1222 (q : Nat → Bool) : valuationOf q 101 = true ∨ valuationOf q 1616 = true := by
  have hs : count1616 q = (countLit q [-101]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-101]) (l₂ := [-105])
  have hm := merge_left (literal (valuationOf q) (-101)) (literal (valuationOf q) (1616)) (countLit q [-101]) (countLit q [-105]) (count1616 q) 1 (meaningNeg101 q) (meaning1616 q) hs
  change (! (valuationOf q 101)) = false ∨ valuationOf q 1616 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1222 (q : Snake 81) (h : Conditions q) : valuation q 101 = true ∨ valuation q 1616 = true := counterClause1222 (baseVal q)

theorem counterClause1223 (q : Nat → Bool) : valuationOf q 1616 = false ∨ valuationOf q 1620 = true := by
  have hs : count1620 q = (countLit q [-101, -105]) + (countLit q [-107, -108]) := List.countP_append (p := literal q) (l₁ := [-101, -105]) (l₂ := [-107, -108])
  have hm := merge_left (literal (valuationOf q) (1616)) (literal (valuationOf q) (1620)) (countLit q [-101, -105]) (countLit q [-107, -108]) (count1620 q) 1 (meaning1616 q) (meaning1620 q) hs
  change valuationOf q 1616 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1223 (q : Snake 81) (h : Conditions q) : valuation q 1616 = false ∨ valuation q 1620 = true := counterClause1223 (baseVal q)

theorem counterClause1224 (q : Nat → Bool) : valuationOf q 113 = true ∨ valuationOf q 1624 = true := by
  have hs : count1624 q = (countLit q [-112]) + (countLit q [-113]) := List.countP_append (p := literal q) (l₁ := [-112]) (l₂ := [-113])
  have hm := merge_right (literal (valuationOf q) (-113)) (literal (valuationOf q) (1624)) (countLit q [-112]) (countLit q [-113]) (count1624 q) 1 (meaningNeg113 q) (meaning1624 q) hs
  change (! (valuationOf q 113)) = false ∨ valuationOf q 1624 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1224 (q : Snake 81) (h : Conditions q) : valuation q 113 = true ∨ valuation q 1624 = true := counterClause1224 (baseVal q)

theorem counterClause1225 (q : Nat → Bool) : valuationOf q 112 = true ∨ valuationOf q 1624 = true := by
  have hs : count1624 q = (countLit q [-112]) + (countLit q [-113]) := List.countP_append (p := literal q) (l₁ := [-112]) (l₂ := [-113])
  have hm := merge_left (literal (valuationOf q) (-112)) (literal (valuationOf q) (1624)) (countLit q [-112]) (countLit q [-113]) (count1624 q) 1 (meaningNeg112 q) (meaning1624 q) hs
  change (! (valuationOf q 112)) = false ∨ valuationOf q 1624 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1225 (q : Snake 81) (h : Conditions q) : valuation q 112 = true ∨ valuation q 1624 = true := counterClause1225 (baseVal q)

theorem counterClause1226 (q : Nat → Bool) : valuationOf q 115 = true ∨ valuationOf q 1626 = true := by
  have hs : count1626 q = (countLit q [-114]) + (countLit q [-115]) := List.countP_append (p := literal q) (l₁ := [-114]) (l₂ := [-115])
  have hm := merge_right (literal (valuationOf q) (-115)) (literal (valuationOf q) (1626)) (countLit q [-114]) (countLit q [-115]) (count1626 q) 1 (meaningNeg115 q) (meaning1626 q) hs
  change (! (valuationOf q 115)) = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1226 (q : Snake 81) (h : Conditions q) : valuation q 115 = true ∨ valuation q 1626 = true := counterClause1226 (baseVal q)

theorem counterClause1227 (q : Nat → Bool) : valuationOf q 114 = true ∨ valuationOf q 1626 = true := by
  have hs : count1626 q = (countLit q [-114]) + (countLit q [-115]) := List.countP_append (p := literal q) (l₁ := [-114]) (l₂ := [-115])
  have hm := merge_left (literal (valuationOf q) (-114)) (literal (valuationOf q) (1626)) (countLit q [-114]) (countLit q [-115]) (count1626 q) 1 (meaningNeg114 q) (meaning1626 q) hs
  change (! (valuationOf q 114)) = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1227 (q : Snake 81) (h : Conditions q) : valuation q 114 = true ∨ valuation q 1626 = true := counterClause1227 (baseVal q)

theorem counterClause1228 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1628 = true := by
  have hs : count1628 q = (countLit q [-112, -113]) + (countLit q [-114, -115]) := List.countP_append (p := literal q) (l₁ := [-112, -113]) (l₂ := [-114, -115])
  have hm := merge_right (literal (valuationOf q) (1626)) (literal (valuationOf q) (1628)) (countLit q [-112, -113]) (countLit q [-114, -115]) (count1628 q) 1 (meaning1626 q) (meaning1628 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1628 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1228 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1628 = true := counterClause1228 (baseVal q)

theorem counterClause1229 (q : Nat → Bool) : valuationOf q 1624 = false ∨ valuationOf q 1628 = true := by
  have hs : count1628 q = (countLit q [-112, -113]) + (countLit q [-114, -115]) := List.countP_append (p := literal q) (l₁ := [-112, -113]) (l₂ := [-114, -115])
  have hm := merge_left (literal (valuationOf q) (1624)) (literal (valuationOf q) (1628)) (countLit q [-112, -113]) (countLit q [-114, -115]) (count1628 q) 1 (meaning1624 q) (meaning1628 q) hs
  change valuationOf q 1624 = false ∨ valuationOf q 1628 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1229 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1628 = true := counterClause1229 (baseVal q)

theorem counterClause1230 (q : Nat → Bool) : valuationOf q 1628 = false ∨ valuationOf q 1632 = true := by
  have hs : count1632 q = (countLit q [-101, -105, -107, -108]) + (countLit q [-112, -113, -114, -115]) := List.countP_append (p := literal q) (l₁ := [-101, -105, -107, -108]) (l₂ := [-112, -113, -114, -115])
  have hm := merge_right (literal (valuationOf q) (1628)) (literal (valuationOf q) (1632)) (countLit q [-101, -105, -107, -108]) (countLit q [-112, -113, -114, -115]) (count1632 q) 1 (meaning1628 q) (meaning1632 q) hs
  change valuationOf q 1628 = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1230 (q : Snake 81) (h : Conditions q) : valuation q 1628 = false ∨ valuation q 1632 = true := counterClause1230 (baseVal q)

theorem counterClause1231 (q : Nat → Bool) : valuationOf q 1620 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1633 = true := by
  have hs : count1632 q = (countLit q [-101, -105, -107, -108]) + (countLit q [-112, -113, -114, -115]) := List.countP_append (p := literal q) (l₁ := [-101, -105, -107, -108]) (l₂ := [-112, -113, -114, -115])
  have hm := merge_two (literal (valuationOf q) (1620)) (literal (valuationOf q) (1628)) (literal (valuationOf q) (1633)) (countLit q [-101, -105, -107, -108]) (countLit q [-112, -113, -114, -115]) (count1632 q) 1 1 (meaning1620 q) (meaning1628 q) (meaning1633 q) hs
  change valuationOf q 1620 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1633 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1231 (q : Snake 81) (h : Conditions q) : valuation q 1620 = false ∨ valuation q 1628 = false ∨ valuation q 1633 = true := counterClause1231 (baseVal q)

theorem counterClause1232 (q : Nat → Bool) : valuationOf q 1609 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1642 = true := by
  have hs : count1640 q = (countLit q [-90, -92, -93, -95, -98, -99, -100]) + (countLit q [-101, -105, -107, -108, -112, -113, -114, -115]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93, -95, -98, -99, -100]) (l₂ := [-101, -105, -107, -108, -112, -113, -114, -115])
  have hm := merge_two (literal (valuationOf q) (1609)) (literal (valuationOf q) (1633)) (literal (valuationOf q) (1642)) (countLit q [-90, -92, -93, -95, -98, -99, -100]) (countLit q [-101, -105, -107, -108, -112, -113, -114, -115]) (count1640 q) 1 2 (meaning1609 q) (meaning1633 q) (meaning1642 q) hs
  change valuationOf q 1609 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1232 (q : Snake 81) (h : Conditions q) : valuation q 1609 = false ∨ valuation q 1633 = false ∨ valuation q 1642 = true := counterClause1232 (baseVal q)

theorem counterClause1233 (q : Nat → Bool) : valuationOf q 1610 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1642 = true := by
  have hs : count1640 q = (countLit q [-90, -92, -93, -95, -98, -99, -100]) + (countLit q [-101, -105, -107, -108, -112, -113, -114, -115]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -93, -95, -98, -99, -100]) (l₂ := [-101, -105, -107, -108, -112, -113, -114, -115])
  have hm := merge_two (literal (valuationOf q) (1610)) (literal (valuationOf q) (1632)) (literal (valuationOf q) (1642)) (countLit q [-90, -92, -93, -95, -98, -99, -100]) (countLit q [-101, -105, -107, -108, -112, -113, -114, -115]) (count1640 q) 2 1 (meaning1610 q) (meaning1632 q) (meaning1642 q) hs
  change valuationOf q 1610 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1233 (q : Snake 81) (h : Conditions q) : valuation q 1610 = false ∨ valuation q 1632 = false ∨ valuation q 1642 = true := counterClause1233 (baseVal q)

theorem counterClause1234 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1659 = true := by
  have hs : count1655 q = (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -81, -82, -83, -87, -89]) + (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -66, -69, -71, -72, -74, -75, -79, -81, -82, -83, -87, -89]) (l₂ := [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115])
  have hm := merge_two (literal (valuationOf q) (1583)) (literal (valuationOf q) (1642)) (literal (valuationOf q) (1659)) (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -81, -82, -83, -87, -89]) (countLit q [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) (count1655 q) 2 3 (meaning1583 q) (meaning1642 q) (meaning1659 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1234 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1642 = false ∨ valuation q 1659 = true := counterClause1234 (baseVal q)

theorem counterClause1235 (q : Nat → Bool) : valuationOf q 1536 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1690 = true := by
  have hs : count1673 q = (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27, -30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) + (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -81, -82, -83, -87, -89, -90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27, -30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) (l₂ := [-62, -63, -66, -69, -71, -72, -74, -75, -79, -81, -82, -83, -87, -89, -90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115])
  have hm := merge_two (literal (valuationOf q) (1536)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1690)) (countLit q [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27, -30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]) (countLit q [-62, -63, -66, -69, -71, -72, -74, -75, -79, -81, -82, -83, -87, -89, -90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]) (count1673 q) 13 5 (meaning1536 q) (meaning1659 q) (meaning1690 q) hs
  change valuationOf q 1536 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1235 (q : Snake 81) (h : Conditions q) : valuation q 1536 = false ∨ valuation q 1659 = false ∨ valuation q 1690 = true := counterClause1235 (baseVal q)

theorem clause1236 (q : Snake 81) (h : Conditions q) : valuation q 1690 = false := by
  rw [value1690]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1673 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause1237 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 2 = false ∨ valuation q 45 = false ∨ valuation q 46 = false := by
  rw [value1, value2, value45, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (0 : Vertex) (1 : Vertex) (256 : Vertex) (257 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1238 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 4 = false ∨ valuation q 15 = false ∨ valuation q 20 = false := by
  rw [value1, value4, value15, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (0 : Vertex) (8 : Vertex) (128 : Vertex) (136 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1239 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 4 = false ∨ valuation q 45 = false ∨ valuation q 52 = false := by
  rw [value1, value4, value45, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (0 : Vertex) (8 : Vertex) (256 : Vertex) (264 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1240 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 15 = false ∨ valuation q 45 = false ∨ valuation q 86 = false := by
  rw [value1, value15, value45, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (0 : Vertex) (128 : Vertex) (256 : Vertex) (384 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1241 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 8 = false ∨ valuation q 46 = false ∨ valuation q 58 = false := by
  rw [value2, value8, value46, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (1 : Vertex) (17 : Vertex) (257 : Vertex) (273 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1242 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 18 = false ∨ valuation q 50 = false ∨ valuation q 88 = false := by
  rw [value3, value18, value50, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (6 : Vertex) (134 : Vertex) (262 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1243 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 7 = false ∨ valuation q 54 = false ∨ valuation q 57 = false := by
  rw [value5, value7, value54, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (11 : Vertex) (15 : Vertex) (267 : Vertex) (271 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1244 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 10 = false ∨ valuation q 58 = false ∨ valuation q 59 = false := by
  rw [value8, value10, value58, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (17 : Vertex) (19 : Vertex) (273 : Vertex) (275 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1245 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 19 = false ∨ valuation q 88 = false ∨ valuation q 89 = false := by
  rw [value18, value19, value88, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (134 : Vertex) (135 : Vertex) (390 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1246 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 22 = false ∨ valuation q 23 = false ∨ valuation q 24 = false := by
  rw [value20, value22, value23, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (136 : Vertex) (138 : Vertex) (140 : Vertex) (142 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1247 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 47 = false ∨ valuation q 48 = false ∨ valuation q 50 = false := by
  rw [value45, value47, value48, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (256 : Vertex) (258 : Vertex) (260 : Vertex) (262 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1248 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 47 = false ∨ valuation q 52 = false ∨ valuation q 53 = false := by
  rw [value45, value47, value52, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (256 : Vertex) (258 : Vertex) (264 : Vertex) (266 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block38 (q : Snake 81) (h : Conditions q) : B112E203.Block38 (valuation q) :=
  ⟨clause1217 q h, clause1218 q h, clause1219 q h, clause1220 q h, clause1221 q h, clause1222 q h, clause1223 q h, clause1224 q h, clause1225 q h, clause1226 q h, clause1227 q h, clause1228 q h, clause1229 q h, clause1230 q h, clause1231 q h, clause1232 q h, clause1233 q h, clause1234 q h, clause1235 q h, clause1236 q h, clause1237 q h, clause1238 q h, clause1239 q h, clause1240 q h, clause1241 q h, clause1242 q h, clause1243 q h, clause1244 q h, clause1245 q h, clause1246 q h, clause1247 q h, clause1248 q h⟩

end
end Snake9.Regrowth.E112203
