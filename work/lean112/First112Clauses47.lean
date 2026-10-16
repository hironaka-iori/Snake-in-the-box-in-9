import First112Semantics
import Dfs112FirstBooleanInputs
namespace Snake9.Regrowth.First112
noncomputable section
local instance blockDec47 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1505 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 4 = false ∨ valuation q 10 = false ∨ valuation q 11 = false := by
  rw [value3, value4, value10, value11]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (36 : Vertex) (37 : Vertex) (52 : Vertex) (53 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1506 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 6 = false ∨ valuation q 8 = false ∨ valuation q 9 = false := by
  rw [value5, value6, value8, value9]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (40 : Vertex) (42 : Vertex) (44 : Vertex) (46 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1507 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 24 = false ∨ valuation q 60 = false ∨ valuation q 87 = false := by
  rw [value5, value24, value60, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (40 : Vertex) (168 : Vertex) (296 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1508 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 26 = false ∨ valuation q 61 = false ∨ valuation q 89 = false := by
  rw [value7, value26, value61, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (43 : Vertex) (171 : Vertex) (299 : Vertex) (427 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1509 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 19 = false ∨ valuation q 73 = false ∨ valuation q 75 = false := by
  rw [value17, value19, value73, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (99 : Vertex) (103 : Vertex) (355 : Vertex) (359 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1510 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 39 = false ∨ valuation q 73 = false ∨ valuation q 106 = false := by
  rw [value17, value39, value73, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (99 : Vertex) (227 : Vertex) (355 : Vertex) (483 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1511 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 24 = false ∨ valuation q 80 = false ∨ valuation q 87 = false := by
  rw [value20, value24, value80, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (160 : Vertex) (168 : Vertex) (416 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1512 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 23 = false ∨ valuation q 85 = false ∨ valuation q 86 = false := by
  rw [value22, value23, value85, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (166 : Vertex) (167 : Vertex) (422 : Vertex) (423 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1513 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 42 = false ∨ valuation q 85 = false ∨ valuation q 108 = false := by
  rw [value22, value42, value85, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (166 : Vertex) (230 : Vertex) (422 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1514 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 44 = false ∨ valuation q 89 = false ∨ valuation q 110 = false := by
  rw [value26, value44, value89, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (171 : Vertex) (235 : Vertex) (427 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1515 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 31 = false ∨ valuation q 93 = false ∨ valuation q 94 = false := by
  rw [value29, value31, value93, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (177 : Vertex) (179 : Vertex) (433 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1516 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 33 = false ∨ valuation q 35 = false ∨ valuation q 37 = false := by
  rw [value32, value33, value35, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (180 : Vertex) (182 : Vertex) (188 : Vertex) (190 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1517 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 42 = false ∨ valuation q 43 = false ∨ valuation q 46 = false := by
  rw [value38, value42, value43, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (226 : Vertex) (230 : Vertex) (234 : Vertex) (238 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1518 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 44 = false ∨ valuation q 106 = false ∨ valuation q 110 = false := by
  rw [value39, value44, value106, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (227 : Vertex) (235 : Vertex) (483 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1519 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 42 = false ∨ valuation q 45 = false ∨ valuation q 46 = false := by
  rw [value40, value42, value45, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (228 : Vertex) (230 : Vertex) (236 : Vertex) (238 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1520 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 52 = false ∨ valuation q 53 = false := by
  rw [value50, value51, value52, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (248 : Vertex) (249 : Vertex) (250 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1521 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 56 = false ∨ valuation q 64 = false ∨ valuation q 65 = false := by
  rw [value55, value56, value64, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (288 : Vertex) (289 : Vertex) (304 : Vertex) (305 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1522 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 56 = false ∨ valuation q 80 = false ∨ valuation q 81 = false := by
  rw [value55, value56, value80, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (288 : Vertex) (289 : Vertex) (416 : Vertex) (417 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1523 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 60 = false ∨ valuation q 80 = false ∨ valuation q 87 = false := by
  rw [value55, value60, value80, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (288 : Vertex) (296 : Vertex) (416 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1524 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 63 = false ∨ valuation q 89 = false ∨ valuation q 92 = false := by
  rw [value61, value63, value89, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (299 : Vertex) (303 : Vertex) (427 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1525 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 65 = false ∨ valuation q 66 = false ∨ valuation q 67 = false := by
  rw [value64, value65, value66, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (304 : Vertex) (305 : Vertex) (306 : Vertex) (307 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1526 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 67 = false ∨ valuation q 93 = false ∨ valuation q 94 = false := by
  rw [value65, value67, value93, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (305 : Vertex) (307 : Vertex) (433 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1527 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 83 = false ∨ valuation q 87 = false ∨ valuation q 90 = false := by
  rw [value80, value83, value87, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (416 : Vertex) (420 : Vertex) (424 : Vertex) (428 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1528 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 87 = false ∨ valuation q 103 = false ∨ valuation q 109 = false := by
  rw [value80, value87, value103, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (416 : Vertex) (424 : Vertex) (480 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1529 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 93 = false ∨ valuation q 104 = false ∨ valuation q 114 = false := by
  rw [value81, value93, value104, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (417 : Vertex) (433 : Vertex) (481 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1530 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 85 = false ∨ valuation q 88 = false ∨ valuation q 91 = false := by
  rw [value82, value85, value88, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (418 : Vertex) (422 : Vertex) (426 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1531 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 85 = false ∨ valuation q 90 = false ∨ valuation q 91 = false := by
  rw [value83, value85, value90, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (420 : Vertex) (422 : Vertex) (428 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1532 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 86 = false ∨ valuation q 96 = false ∨ valuation q 97 = false := by
  rw [value84, value86, value96, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (421 : Vertex) (423 : Vertex) (437 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1533 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 92 = false ∨ valuation q 97 = false ∨ valuation q 102 = false := by
  rw [value86, value92, value97, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (423 : Vertex) (431 : Vertex) (439 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1534 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 88 = false ∨ valuation q 90 = false ∨ valuation q 91 = false := by
  rw [value87, value88, value90, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (424 : Vertex) (426 : Vertex) (428 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1535 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 88 = false ∨ valuation q 98 = false ∨ valuation q 100 = false := by
  rw [value87, value88, value98, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (424 : Vertex) (426 : Vertex) (440 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1536 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 98 = false ∨ valuation q 109 = false ∨ valuation q 118 = false := by
  rw [value87, value98, value109, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (424 : Vertex) (440 : Vertex) (488 : Vertex) (504 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block47 (q : Snake 81) (h : Conditions q) : Dfs112FirstBoolean.Block47 (valuation q) :=
  ⟨clause1505 q h, clause1506 q h, clause1507 q h, clause1508 q h, clause1509 q h, clause1510 q h, clause1511 q h, clause1512 q h, clause1513 q h, clause1514 q h, clause1515 q h, clause1516 q h, clause1517 q h, clause1518 q h, clause1519 q h, clause1520 q h, clause1521 q h, clause1522 q h, clause1523 q h, clause1524 q h, clause1525 q h, clause1526 q h, clause1527 q h, clause1528 q h, clause1529 q h, clause1530 q h, clause1531 q h, clause1532 q h, clause1533 q h, clause1534 q h, clause1535 q h, clause1536 q h⟩

end
end Snake9.Regrowth.First112
