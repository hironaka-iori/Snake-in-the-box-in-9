import E112008Semantics
import B112E008Inputs
namespace Snake9.Regrowth.E112008
noncomputable section
local instance blockDec49 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1569 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 39 = false ∨ valuation q 52 = false ∨ valuation q 57 = false := by
  rw [value34, value39, value52, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (162 : Vertex) (170 : Vertex) (226 : Vertex) (234 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1570 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 37 = false ∨ valuation q 41 = false ∨ valuation q 42 = false := by
  rw [value35, value37, value41, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (164 : Vertex) (166 : Vertex) (172 : Vertex) (174 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1571 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 39 = false ∨ valuation q 41 = false ∨ valuation q 42 = false := by
  rw [value38, value39, value41, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (168 : Vertex) (170 : Vertex) (172 : Vertex) (174 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1572 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 47 = false ∨ valuation q 92 = false ∨ valuation q 103 = false := by
  rw [value38, value47, value92, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (168 : Vertex) (184 : Vertex) (424 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1573 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 40 = false ∨ valuation q 57 = false ∨ valuation q 58 = false := by
  rw [value39, value40, value57, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (170 : Vertex) (171 : Vertex) (234 : Vertex) (235 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1574 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 49 = false ∨ valuation q 93 = false ∨ valuation q 105 = false := by
  rw [value40, value49, value93, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (171 : Vertex) (187 : Vertex) (427 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1575 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 42 = false ∨ valuation q 94 = false ∨ valuation q 96 = false := by
  rw [value41, value42, value94, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (172 : Vertex) (174 : Vertex) (428 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1576 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 46 = false ∨ valuation q 50 = false ∨ valuation q 51 = false := by
  rw [value44, value46, value50, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (181 : Vertex) (183 : Vertex) (189 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1577 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 49 = false ∨ valuation q 50 = false ∨ valuation q 51 = false := by
  rw [value48, value49, value50, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (185 : Vertex) (187 : Vertex) (189 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1578 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 53 = false ∨ valuation q 63 = false ∨ valuation q 64 = false := by
  rw [value52, value53, value63, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (226 : Vertex) (227 : Vertex) (242 : Vertex) (243 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1579 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 55 = false ∨ valuation q 58 = false ∨ valuation q 60 = false := by
  rw [value53, value55, value58, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (227 : Vertex) (231 : Vertex) (235 : Vertex) (239 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1580 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 55 = false ∨ valuation q 59 = false ∨ valuation q 60 = false := by
  rw [value54, value55, value59, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (229 : Vertex) (231 : Vertex) (237 : Vertex) (239 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1581 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 58 = false ∨ valuation q 59 = false ∨ valuation q 60 = false := by
  rw [value56, value58, value59, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (233 : Vertex) (235 : Vertex) (237 : Vertex) (239 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1582 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 62 = false ∨ valuation q 63 = false ∨ valuation q 64 = false := by
  rw [value61, value62, value63, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (240 : Vertex) (241 : Vertex) (242 : Vertex) (243 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1583 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 65 = false ∨ valuation q 66 = false ∨ valuation q 67 = false := by
  rw [value61, value65, value66, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (240 : Vertex) (244 : Vertex) (248 : Vertex) (252 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1584 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 71 = false ∨ valuation q 74 = false ∨ valuation q 75 = false := by
  rw [value70, value71, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (288 : Vertex) (289 : Vertex) (296 : Vertex) (297 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1585 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 71 = false ∨ valuation q 86 = false ∨ valuation q 87 = false := by
  rw [value70, value71, value86, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (288 : Vertex) (289 : Vertex) (416 : Vertex) (417 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1586 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 77 = false ∨ valuation q 94 = false ∨ valuation q 96 = false := by
  rw [value76, value77, value94, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (300 : Vertex) (302 : Vertex) (428 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1587 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 83 = false ∨ valuation q 100 = false ∨ valuation q 104 = false := by
  rw [value78, value83, value100, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (306 : Vertex) (314 : Vertex) (434 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1588 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 87 = false ∨ valuation q 88 = false ∨ valuation q 89 = false := by
  rw [value86, value87, value88, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (416 : Vertex) (417 : Vertex) (418 : Vertex) (419 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1589 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 87 = false ∨ valuation q 98 = false ∨ valuation q 99 = false := by
  rw [value86, value87, value98, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (416 : Vertex) (417 : Vertex) (432 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1590 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 87 = false ∨ valuation q 109 = false ∨ valuation q 110 = false := by
  rw [value86, value87, value109, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (416 : Vertex) (417 : Vertex) (480 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1591 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 89 = false ∨ valuation q 90 = false ∨ valuation q 91 = false := by
  rw [value87, value89, value90, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (417 : Vertex) (419 : Vertex) (421 : Vertex) (423 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1592 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 89 = false ∨ valuation q 99 = false ∨ valuation q 101 = false := by
  rw [value87, value89, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (417 : Vertex) (419 : Vertex) (433 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1593 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 89 = false ∨ valuation q 100 = false ∨ valuation q 101 = false := by
  rw [value88, value89, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (418 : Vertex) (419 : Vertex) (434 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1594 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 91 = false ∨ valuation q 93 = false ∨ valuation q 97 = false := by
  rw [value89, value91, value93, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (419 : Vertex) (423 : Vertex) (427 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1595 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 93 = false ∨ valuation q 101 = false ∨ valuation q 105 = false := by
  rw [value89, value93, value101, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (419 : Vertex) (427 : Vertex) (435 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1596 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 91 = false ∨ valuation q 95 = false ∨ valuation q 97 = false := by
  rw [value90, value91, value95, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (421 : Vertex) (423 : Vertex) (429 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1597 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 94 = false ∨ valuation q 103 = false ∨ valuation q 106 = false := by
  rw [value92, value94, value103, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (424 : Vertex) (428 : Vertex) (440 : Vertex) (444 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1598 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 97 = false ∨ valuation q 105 = false ∨ valuation q 108 = false := by
  rw [value93, value97, value105, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (427 : Vertex) (431 : Vertex) (443 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1599 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 95 = false ∨ valuation q 96 = false ∨ valuation q 97 = false := by
  rw [value94, value95, value96, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (428 : Vertex) (429 : Vertex) (430 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1600 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 96 = false ∨ valuation q 106 = false ∨ valuation q 107 = false := by
  rw [value94, value96, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (428 : Vertex) (430 : Vertex) (444 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block49 (q : Snake 81) (h : Conditions q) : B112E008.Block49 (valuation q) :=
  ⟨clause1569 q h, clause1570 q h, clause1571 q h, clause1572 q h, clause1573 q h, clause1574 q h, clause1575 q h, clause1576 q h, clause1577 q h, clause1578 q h, clause1579 q h, clause1580 q h, clause1581 q h, clause1582 q h, clause1583 q h, clause1584 q h, clause1585 q h, clause1586 q h, clause1587 q h, clause1588 q h, clause1589 q h, clause1590 q h, clause1591 q h, clause1592 q h, clause1593 q h, clause1594 q h, clause1595 q h, clause1596 q h, clause1597 q h, clause1598 q h, clause1599 q h, clause1600 q h⟩

end
end Snake9.Regrowth.E112008
