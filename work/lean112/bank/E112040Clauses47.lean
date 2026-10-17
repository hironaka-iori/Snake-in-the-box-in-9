import E112040Semantics
import B112E040Inputs
namespace Snake9.Regrowth.E112040
noncomputable section
local instance blockDec47 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1505 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 36 = false ∨ valuation q 67 = false ∨ valuation q 71 = false := by
  rw [value30, value36, value67, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (112 : Vertex) (120 : Vertex) (240 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1506 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 36 = false ∨ valuation q 102 = false ∨ valuation q 106 = false := by
  rw [value30, value36, value102, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (112 : Vertex) (120 : Vertex) (368 : Vertex) (376 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1507 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 32 = false ∨ valuation q 34 = false ∨ valuation q 35 = false := by
  rw [value31, value32, value34, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (114 : Vertex) (115 : Vertex) (118 : Vertex) (119 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1508 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 34 = false ∨ valuation q 39 = false ∨ valuation q 41 = false := by
  rw [value33, value34, value39, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (116 : Vertex) (118 : Vertex) (124 : Vertex) (126 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1509 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 38 = false ∨ valuation q 106 = false ∨ valuation q 108 = false := by
  rw [value36, value38, value106, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (120 : Vertex) (122 : Vertex) (376 : Vertex) (378 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1510 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 41 = false ∨ valuation q 108 = false ∨ valuation q 111 = false := by
  rw [value38, value41, value108, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (122 : Vertex) (126 : Vertex) (378 : Vertex) (382 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1511 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 47 = false ∨ valuation q 50 = false ∨ valuation q 55 = false := by
  rw [value43, value47, value50, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (160 : Vertex) (168 : Vertex) (176 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1512 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 55 = false ∨ valuation q 112 = false ∨ valuation q 115 = false := by
  rw [value47, value55, value112, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (168 : Vertex) (184 : Vertex) (424 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1513 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 53 = false ∨ valuation q 54 = false := by
  rw [value50, value51, value53, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (176 : Vertex) (178 : Vertex) (180 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1514 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 55 = false ∨ valuation q 67 = false ∨ valuation q 71 = false := by
  rw [value50, value55, value67, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (176 : Vertex) (184 : Vertex) (240 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1515 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 76 = false ∨ valuation q 77 = false ∨ valuation q 78 = false := by
  rw [value75, value76, value77, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (288 : Vertex) (289 : Vertex) (290 : Vertex) (291 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1516 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 85 = false ∨ valuation q 88 = false ∨ valuation q 89 = false := by
  rw [value84, value85, value88, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (306 : Vertex) (307 : Vertex) (314 : Vertex) (315 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1517 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 97 = false ∨ valuation q 102 = false ∨ valuation q 106 = false := by
  rw [value92, value97, value102, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (352 : Vertex) (360 : Vertex) (368 : Vertex) (376 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1518 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 96 = false ∨ valuation q 104 = false ∨ valuation q 105 = false := by
  rw [value94, value96, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (357 : Vertex) (359 : Vertex) (373 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1519 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 98 = false ∨ valuation q 99 = false ∨ valuation q 100 = false := by
  rw [value97, value98, value99, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (360 : Vertex) (361 : Vertex) (362 : Vertex) (363 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1520 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 98 = false ∨ valuation q 106 = false ∨ valuation q 107 = false := by
  rw [value97, value98, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (360 : Vertex) (361 : Vertex) (376 : Vertex) (377 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1521 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 100 = false ∨ valuation q 107 = false ∨ valuation q 109 = false := by
  rw [value98, value100, value107, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (361 : Vertex) (363 : Vertex) (377 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1522 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 100 = false ∨ valuation q 108 = false ∨ valuation q 109 = false := by
  rw [value99, value100, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (362 : Vertex) (363 : Vertex) (378 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1523 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 101 = false ∨ valuation q 108 = false ∨ valuation q 111 = false := by
  rw [value99, value101, value108, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (362 : Vertex) (366 : Vertex) (378 : Vertex) (382 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1524 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 107 = false ∨ valuation q 108 = false ∨ valuation q 109 = false := by
  rw [value106, value107, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (376 : Vertex) (377 : Vertex) (378 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block47 (q : Snake 81) (h : Conditions q) : B112E040.Block47 (valuation q) :=
  ⟨clause1505 q h, clause1506 q h, clause1507 q h, clause1508 q h, clause1509 q h, clause1510 q h, clause1511 q h, clause1512 q h, clause1513 q h, clause1514 q h, clause1515 q h, clause1516 q h, clause1517 q h, clause1518 q h, clause1519 q h, clause1520 q h, clause1521 q h, clause1522 q h, clause1523 q h, clause1524 q h⟩

end
end Snake9.Regrowth.E112040
