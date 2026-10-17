import E112097Semantics
import B112E097Inputs
namespace Snake9.Regrowth.E112097
noncomputable section
local instance blockDec48 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1537 (q : Nat → Bool) : valuationOf q 1709 = false ∨ valuationOf q 1734 = false ∨ valuationOf q 1745 = true := by
  have hs : count1739 q = (countLit q [-92, -93, -96, -98, -99, -102, -103, -104]) + (countLit q [-107, -110, -112, -116, -117, -119, -120, -123]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -96, -98, -99, -102, -103, -104]) (l₂ := [-107, -110, -112, -116, -117, -119, -120, -123])
  have hm := merge_two (literal (valuationOf q) (1709)) (literal (valuationOf q) (1734)) (literal (valuationOf q) (1745)) (countLit q [-92, -93, -96, -98, -99, -102, -103, -104]) (countLit q [-107, -110, -112, -116, -117, -119, -120, -123]) (count1739 q) 3 4 (meaning1709 q) (meaning1734 q) (meaning1745 q) hs
  change valuationOf q 1709 = false ∨ valuationOf q 1734 = false ∨ valuationOf q 1745 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1537 (q : Snake 81) (h : Conditions q) : valuation q 1709 = false ∨ valuation q 1734 = false ∨ valuation q 1745 = true := counterClause1537 (baseVal q)

theorem counterClause1538 (q : Nat → Bool) : valuationOf q 1709 = false ∨ valuationOf q 1735 = false ∨ valuationOf q 1746 = true := by
  have hs : count1739 q = (countLit q [-92, -93, -96, -98, -99, -102, -103, -104]) + (countLit q [-107, -110, -112, -116, -117, -119, -120, -123]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -96, -98, -99, -102, -103, -104]) (l₂ := [-107, -110, -112, -116, -117, -119, -120, -123])
  have hm := merge_two (literal (valuationOf q) (1709)) (literal (valuationOf q) (1735)) (literal (valuationOf q) (1746)) (countLit q [-92, -93, -96, -98, -99, -102, -103, -104]) (countLit q [-107, -110, -112, -116, -117, -119, -120, -123]) (count1739 q) 3 5 (meaning1709 q) (meaning1735 q) (meaning1746 q) hs
  change valuationOf q 1709 = false ∨ valuationOf q 1735 = false ∨ valuationOf q 1746 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1538 (q : Snake 81) (h : Conditions q) : valuation q 1709 = false ∨ valuation q 1735 = false ∨ valuation q 1746 = true := counterClause1538 (baseVal q)

theorem counterClause1539 (q : Nat → Bool) : valuationOf q 1710 = false ∨ valuationOf q 1734 = false ∨ valuationOf q 1746 = true := by
  have hs : count1739 q = (countLit q [-92, -93, -96, -98, -99, -102, -103, -104]) + (countLit q [-107, -110, -112, -116, -117, -119, -120, -123]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -96, -98, -99, -102, -103, -104]) (l₂ := [-107, -110, -112, -116, -117, -119, -120, -123])
  have hm := merge_two (literal (valuationOf q) (1710)) (literal (valuationOf q) (1734)) (literal (valuationOf q) (1746)) (countLit q [-92, -93, -96, -98, -99, -102, -103, -104]) (countLit q [-107, -110, -112, -116, -117, -119, -120, -123]) (count1739 q) 4 4 (meaning1710 q) (meaning1734 q) (meaning1746 q) hs
  change valuationOf q 1710 = false ∨ valuationOf q 1734 = false ∨ valuationOf q 1746 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1539 (q : Snake 81) (h : Conditions q) : valuation q 1710 = false ∨ valuation q 1734 = false ∨ valuation q 1746 = true := counterClause1539 (baseVal q)

theorem counterClause1540 (q : Nat → Bool) : valuationOf q 1678 = false ∨ valuationOf q 1746 = false ∨ valuationOf q 1765 = true := by
  have hs : count1755 q = (countLit q [-63, -66, -67, -68, -71, -73, -75, -77, -78, -80, -83, -84, -85, -88, -90]) + (countLit q [-92, -93, -96, -98, -99, -102, -103, -104, -107, -110, -112, -116, -117, -119, -120, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -67, -68, -71, -73, -75, -77, -78, -80, -83, -84, -85, -88, -90]) (l₂ := [-92, -93, -96, -98, -99, -102, -103, -104, -107, -110, -112, -116, -117, -119, -120, -123])
  have hm := merge_two (literal (valuationOf q) (1678)) (literal (valuationOf q) (1746)) (literal (valuationOf q) (1765)) (countLit q [-63, -66, -67, -68, -71, -73, -75, -77, -78, -80, -83, -84, -85, -88, -90]) (countLit q [-92, -93, -96, -98, -99, -102, -103, -104, -107, -110, -112, -116, -117, -119, -120, -123]) (count1755 q) 3 8 (meaning1678 q) (meaning1746 q) (meaning1765 q) hs
  change valuationOf q 1678 = false ∨ valuationOf q 1746 = false ∨ valuationOf q 1765 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1540 (q : Snake 81) (h : Conditions q) : valuation q 1678 = false ∨ valuation q 1746 = false ∨ valuation q 1765 = true := counterClause1540 (baseVal q)

theorem counterClause1541 (q : Nat → Bool) : valuationOf q 1679 = false ∨ valuationOf q 1745 = false ∨ valuationOf q 1765 = true := by
  have hs : count1755 q = (countLit q [-63, -66, -67, -68, -71, -73, -75, -77, -78, -80, -83, -84, -85, -88, -90]) + (countLit q [-92, -93, -96, -98, -99, -102, -103, -104, -107, -110, -112, -116, -117, -119, -120, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -67, -68, -71, -73, -75, -77, -78, -80, -83, -84, -85, -88, -90]) (l₂ := [-92, -93, -96, -98, -99, -102, -103, -104, -107, -110, -112, -116, -117, -119, -120, -123])
  have hm := merge_two (literal (valuationOf q) (1679)) (literal (valuationOf q) (1745)) (literal (valuationOf q) (1765)) (countLit q [-63, -66, -67, -68, -71, -73, -75, -77, -78, -80, -83, -84, -85, -88, -90]) (countLit q [-92, -93, -96, -98, -99, -102, -103, -104, -107, -110, -112, -116, -117, -119, -120, -123]) (count1755 q) 4 7 (meaning1679 q) (meaning1745 q) (meaning1765 q) hs
  change valuationOf q 1679 = false ∨ valuationOf q 1745 = false ∨ valuationOf q 1765 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1541 (q : Snake 81) (h : Conditions q) : valuation q 1679 = false ∨ valuation q 1745 = false ∨ valuation q 1765 = true := counterClause1541 (baseVal q)

theorem counterClause1542 (q : Nat → Bool) : valuationOf q 1620 = false ∨ valuationOf q 1765 = false ∨ valuationOf q 1798 = true := by
  have hs : count1777 q = (countLit q [-2, -5, -9, -11, -12, -14, -15, -16, -17, -19, -23, -24, -26, -27, -30, -31, -32, -35, -37, -39, -41, -42, -45, -48, -49, -51, -52, -56, -58, -60, -62]) + (countLit q [-63, -66, -67, -68, -71, -73, -75, -77, -78, -80, -83, -84, -85, -88, -90, -92, -93, -96, -98, -99, -102, -103, -104, -107, -110, -112, -116, -117, -119, -120, -123]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -9, -11, -12, -14, -15, -16, -17, -19, -23, -24, -26, -27, -30, -31, -32, -35, -37, -39, -41, -42, -45, -48, -49, -51, -52, -56, -58, -60, -62]) (l₂ := [-63, -66, -67, -68, -71, -73, -75, -77, -78, -80, -83, -84, -85, -88, -90, -92, -93, -96, -98, -99, -102, -103, -104, -107, -110, -112, -116, -117, -119, -120, -123])
  have hm := merge_two (literal (valuationOf q) (1620)) (literal (valuationOf q) (1765)) (literal (valuationOf q) (1798)) (countLit q [-2, -5, -9, -11, -12, -14, -15, -16, -17, -19, -23, -24, -26, -27, -30, -31, -32, -35, -37, -39, -41, -42, -45, -48, -49, -51, -52, -56, -58, -60, -62]) (countLit q [-63, -66, -67, -68, -71, -73, -75, -77, -78, -80, -83, -84, -85, -88, -90, -92, -93, -96, -98, -99, -102, -103, -104, -107, -110, -112, -116, -117, -119, -120, -123]) (count1777 q) 11 11 (meaning1620 q) (meaning1765 q) (meaning1798 q) hs
  change valuationOf q 1620 = false ∨ valuationOf q 1765 = false ∨ valuationOf q 1798 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1542 (q : Snake 81) (h : Conditions q) : valuation q 1620 = false ∨ valuation q 1765 = false ∨ valuation q 1798 = true := counterClause1542 (baseVal q)

theorem clause1543 (q : Snake 81) (h : Conditions q) : valuation q 1798 = false := by
  rw [value1798]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1777 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause1544 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 19 = false ∨ valuation q 27 = false ∨ valuation q 28 = false := by
  rw [value18, value19, value27, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (170 : Vertex) (171 : Vertex) (186 : Vertex) (187 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1545 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 23 = false ∨ valuation q 24 = false ∨ valuation q 25 = false := by
  rw [value22, value23, value24, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (180 : Vertex) (181 : Vertex) (182 : Vertex) (183 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1546 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 30 = false ∨ valuation q 31 = false ∨ valuation q 33 = false := by
  rw [value29, value30, value31, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (225 : Vertex) (227 : Vertex) (229 : Vertex) (231 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1547 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 31 = false ∨ valuation q 102 = false ∨ valuation q 105 = false := by
  rw [value29, value31, value102, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (225 : Vertex) (229 : Vertex) (481 : Vertex) (485 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1548 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 35 = false ∨ valuation q 102 = false ∨ valuation q 108 = false := by
  rw [value29, value35, value102, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (225 : Vertex) (233 : Vertex) (481 : Vertex) (489 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1549 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 33 = false ∨ valuation q 36 = false ∨ valuation q 37 = false := by
  rw [value32, value33, value36, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (230 : Vertex) (231 : Vertex) (238 : Vertex) (239 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1550 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 36 = false ∨ valuation q 106 = false ∨ valuation q 112 = false := by
  rw [value32, value36, value106, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (230 : Vertex) (238 : Vertex) (486 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1551 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 35 = false ∨ valuation q 107 = false ∨ valuation q 108 = false := by
  rw [value34, value35, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (232 : Vertex) (233 : Vertex) (488 : Vertex) (489 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1552 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 37 = false ∨ valuation q 112 = false ∨ valuation q 113 = false := by
  rw [value36, value37, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (238 : Vertex) (239 : Vertex) (494 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1553 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 46 = false ∨ valuation q 113 = false ∨ valuation q 123 = false := by
  rw [value37, value46, value113, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (239 : Vertex) (255 : Vertex) (495 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1554 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 39 = false ∨ valuation q 42 = false ∨ valuation q 43 = false := by
  rw [value38, value39, value42, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (240 : Vertex) (242 : Vertex) (248 : Vertex) (250 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1555 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 41 = false ∨ valuation q 42 = false ∨ valuation q 44 = false := by
  rw [value38, value41, value42, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (240 : Vertex) (244 : Vertex) (248 : Vertex) (252 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1556 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 46 = false ∨ valuation q 122 = false ∨ valuation q 123 = false := by
  rw [value45, value46, value122, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (253 : Vertex) (255 : Vertex) (509 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1557 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 48 = false ∨ valuation q 49 = false ∨ valuation q 50 = false := by
  rw [value47, value48, value49, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (288 : Vertex) (290 : Vertex) (292 : Vertex) (294 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1558 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 49 = false ∨ valuation q 52 = false ∨ valuation q 55 = false := by
  rw [value47, value49, value52, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (288 : Vertex) (292 : Vertex) (296 : Vertex) (300 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1559 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 50 = false ∨ valuation q 54 = false ∨ valuation q 56 = false := by
  rw [value48, value50, value54, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (290 : Vertex) (294 : Vertex) (298 : Vertex) (302 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1560 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 50 = false ∨ valuation q 55 = false ∨ valuation q 56 = false := by
  rw [value49, value50, value55, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (292 : Vertex) (294 : Vertex) (300 : Vertex) (302 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1561 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 56 = false ∨ valuation q 68 = false ∨ valuation q 72 = false := by
  rw [value50, value56, value68, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (294 : Vertex) (302 : Vertex) (358 : Vertex) (366 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1562 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 56 = false ∨ valuation q 85 = false ∨ valuation q 89 = false := by
  rw [value50, value56, value85, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (294 : Vertex) (302 : Vertex) (422 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1563 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 53 = false ∨ valuation q 70 = false ∨ valuation q 71 = false := by
  rw [value52, value53, value70, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (296 : Vertex) (297 : Vertex) (360 : Vertex) (361 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1564 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 70 = false ∨ valuation q 86 = false ∨ valuation q 107 = false := by
  rw [value52, value70, value86, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (296 : Vertex) (360 : Vertex) (424 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1565 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 72 = false ∨ valuation q 89 = false ∨ valuation q 112 = false := by
  rw [value56, value72, value89, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (302 : Vertex) (366 : Vertex) (430 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1566 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 58 = false ∨ valuation q 60 = false ∨ valuation q 61 = false := by
  rw [value57, value58, value60, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (305 : Vertex) (307 : Vertex) (309 : Vertex) (311 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1567 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 58 = false ∨ valuation q 62 = false ∨ valuation q 64 = false := by
  rw [value57, value58, value62, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (305 : Vertex) (307 : Vertex) (313 : Vertex) (315 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1568 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 66 = false ∨ valuation q 67 = false ∨ valuation q 69 = false := by
  rw [value65, value66, value67, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (353 : Vertex) (355 : Vertex) (357 : Vertex) (359 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block48 (q : Snake 81) (h : Conditions q) : B112E097.Block48 (valuation q) :=
  ⟨clause1537 q h, clause1538 q h, clause1539 q h, clause1540 q h, clause1541 q h, clause1542 q h, clause1543 q h, clause1544 q h, clause1545 q h, clause1546 q h, clause1547 q h, clause1548 q h, clause1549 q h, clause1550 q h, clause1551 q h, clause1552 q h, clause1553 q h, clause1554 q h, clause1555 q h, clause1556 q h, clause1557 q h, clause1558 q h, clause1559 q h, clause1560 q h, clause1561 q h, clause1562 q h, clause1563 q h, clause1564 q h, clause1565 q h, clause1566 q h, clause1567 q h, clause1568 q h⟩

end
end Snake9.Regrowth.E112097
