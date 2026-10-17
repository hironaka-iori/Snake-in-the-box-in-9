import E112004Semantics
import B112E004Inputs
namespace Snake9.Regrowth.E112004
noncomputable section
local instance blockDec53 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1697 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 40 = false ∨ valuation q 61 = false ∨ valuation q 63 = false := by
  rw [value39, value40, value61, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (169 : Vertex) (171 : Vertex) (233 : Vertex) (235 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1698 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 40 = false ∨ valuation q 90 = false ∨ valuation q 92 = false := by
  rw [value39, value40, value90, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (169 : Vertex) (171 : Vertex) (425 : Vertex) (427 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1699 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 42 = false ∨ valuation q 51 = false ∨ valuation q 54 = false := by
  rw [value39, value42, value51, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (169 : Vertex) (173 : Vertex) (185 : Vertex) (189 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1700 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 51 = false ∨ valuation q 61 = false ∨ valuation q 72 = false := by
  rw [value39, value51, value61, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (169 : Vertex) (185 : Vertex) (233 : Vertex) (249 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1701 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 51 = false ∨ valuation q 90 = false ∨ valuation q 99 = false := by
  rw [value39, value51, value90, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (169 : Vertex) (185 : Vertex) (425 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1702 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 42 = false ∨ valuation q 53 = false ∨ valuation q 54 = false := by
  rw [value41, value42, value53, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (172 : Vertex) (173 : Vertex) (188 : Vertex) (189 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1703 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 43 = false ∨ valuation q 54 = false ∨ valuation q 56 = false := by
  rw [value42, value43, value54, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (173 : Vertex) (175 : Vertex) (189 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1704 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 45 = false ∨ valuation q 47 = false ∨ valuation q 48 = false := by
  rw [value44, value45, value47, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (176 : Vertex) (178 : Vertex) (180 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1705 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 45 = false ∨ valuation q 50 = false ∨ valuation q 52 = false := by
  rw [value44, value45, value50, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (176 : Vertex) (178 : Vertex) (184 : Vertex) (186 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1706 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 47 = false ∨ valuation q 50 = false ∨ valuation q 53 = false := by
  rw [value44, value47, value50, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (176 : Vertex) (180 : Vertex) (184 : Vertex) (188 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1707 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 50 = false ∨ valuation q 66 = false ∨ valuation q 71 = false := by
  rw [value44, value50, value66, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (176 : Vertex) (184 : Vertex) (240 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1708 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 50 = false ∨ valuation q 94 = false ∨ valuation q 98 = false := by
  rw [value44, value50, value94, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (176 : Vertex) (184 : Vertex) (432 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1709 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 48 = false ∨ valuation q 52 = false ∨ valuation q 55 = false := by
  rw [value45, value48, value52, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (178 : Vertex) (182 : Vertex) (186 : Vertex) (190 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1710 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 48 = false ∨ valuation q 53 = false ∨ valuation q 55 = false := by
  rw [value47, value48, value53, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (180 : Vertex) (182 : Vertex) (188 : Vertex) (190 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1711 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 53 = false ∨ valuation q 54 = false := by
  rw [value50, value51, value53, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (184 : Vertex) (185 : Vertex) (188 : Vertex) (189 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1712 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 71 = false ∨ valuation q 72 = false := by
  rw [value50, value51, value71, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (184 : Vertex) (185 : Vertex) (248 : Vertex) (249 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1713 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 98 = false ∨ valuation q 99 = false := by
  rw [value50, value51, value98, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (184 : Vertex) (185 : Vertex) (440 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1714 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 52 = false ∨ valuation q 53 = false ∨ valuation q 55 = false := by
  rw [value50, value52, value53, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (184 : Vertex) (186 : Vertex) (188 : Vertex) (190 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1715 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 54 = false ∨ valuation q 99 = false ∨ valuation q 102 = false := by
  rw [value51, value54, value99, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (185 : Vertex) (189 : Vertex) (441 : Vertex) (445 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1716 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 55 = false ∨ valuation q 100 = false ∨ valuation q 103 = false := by
  rw [value52, value55, value100, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (186 : Vertex) (190 : Vertex) (442 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1717 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 54 = false ∨ valuation q 55 = false ∨ valuation q 56 = false := by
  rw [value53, value54, value55, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (188 : Vertex) (189 : Vertex) (190 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1718 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 56 = false ∨ valuation q 73 = false ∨ valuation q 74 = false := by
  rw [value55, value56, value73, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (190 : Vertex) (191 : Vertex) (254 : Vertex) (255 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1719 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 60 = false ∨ valuation q 62 = false ∨ valuation q 65 = false := by
  rw [value57, value60, value62, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (226 : Vertex) (230 : Vertex) (234 : Vertex) (238 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1720 (q : Snake 81) (h : Conditions q) : valuation q 66 = false ∨ valuation q 67 = false ∨ valuation q 71 = false ∨ valuation q 72 = false := by
  rw [value66, value67, value71, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (240 : Vertex) (241 : Vertex) (248 : Vertex) (249 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1721 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 68 = false ∨ valuation q 69 = false ∨ valuation q 70 = false := by
  rw [value67, value68, value69, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (241 : Vertex) (243 : Vertex) (245 : Vertex) (247 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1722 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 83 = false ∨ valuation q 101 = false ∨ valuation q 118 = false := by
  rw [value77, value83, value101, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (315 : Vertex) (379 : Vertex) (443 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1723 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 89 = false ∨ valuation q 94 = false ∨ valuation q 98 = false := by
  rw [value84, value89, value94, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (416 : Vertex) (424 : Vertex) (432 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1724 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 89 = false ∨ valuation q 104 = false ∨ valuation q 109 = false := by
  rw [value84, value89, value104, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (416 : Vertex) (424 : Vertex) (480 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1725 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 86 = false ∨ valuation q 87 = false ∨ valuation q 88 = false := by
  rw [value85, value86, value87, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (420 : Vertex) (421 : Vertex) (422 : Vertex) (423 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1726 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 88 = false ∨ valuation q 96 = false ∨ valuation q 97 = false := by
  rw [value86, value88, value96, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (421 : Vertex) (423 : Vertex) (437 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1727 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 91 = false ∨ valuation q 98 = false ∨ valuation q 100 = false := by
  rw [value89, value91, value98, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (424 : Vertex) (426 : Vertex) (440 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1728 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 92 = false ∨ valuation q 100 = false ∨ valuation q 101 = false := by
  rw [value91, value92, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (426 : Vertex) (427 : Vertex) (442 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block53 (q : Snake 81) (h : Conditions q) : B112E004.Block53 (valuation q) :=
  ⟨clause1697 q h, clause1698 q h, clause1699 q h, clause1700 q h, clause1701 q h, clause1702 q h, clause1703 q h, clause1704 q h, clause1705 q h, clause1706 q h, clause1707 q h, clause1708 q h, clause1709 q h, clause1710 q h, clause1711 q h, clause1712 q h, clause1713 q h, clause1714 q h, clause1715 q h, clause1716 q h, clause1717 q h, clause1718 q h, clause1719 q h, clause1720 q h, clause1721 q h, clause1722 q h, clause1723 q h, clause1724 q h, clause1725 q h, clause1726 q h, clause1727 q h, clause1728 q h⟩

end
end Snake9.Regrowth.E112004
