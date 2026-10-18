import E112110Semantics
import B112E110Inputs
namespace Snake9.Regrowth.E112110
noncomputable section
local instance blockDec39 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1249 (q : Nat → Bool) : valuationOf q 1536 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1708 = true := by
  have hs : count1689 q = (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29, -30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) + (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86, -88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29, -30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) (l₂ := [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86, -88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1536)) (literal (valuationOf q) (1682)) (literal (valuationOf q) (1708)) (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29, -30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86, -88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) (count1689 q) 6 14 (meaning1536 q) (meaning1682 q) (meaning1708 q) hs
  change valuationOf q 1536 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1249 (q : Snake 81) (h : Conditions q) : valuation q 1536 = false ∨ valuation q 1682 = false ∨ valuation q 1708 = true := counterClause1249 (baseVal q)

theorem counterClause1250 (q : Nat → Bool) : valuationOf q 1537 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1708 = true := by
  have hs : count1689 q = (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29, -30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) + (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86, -88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29, -30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) (l₂ := [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86, -88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1537)) (literal (valuationOf q) (1681)) (literal (valuationOf q) (1708)) (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29, -30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86, -88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) (count1689 q) 7 13 (meaning1537 q) (meaning1681 q) (meaning1708 q) hs
  change valuationOf q 1537 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1250 (q : Snake 81) (h : Conditions q) : valuation q 1537 = false ∨ valuation q 1681 = false ∨ valuation q 1708 = true := counterClause1250 (baseVal q)

theorem counterClause1251 (q : Nat → Bool) : valuationOf q 1538 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1708 = true := by
  have hs : count1689 q = (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29, -30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) + (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86, -88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29, -30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) (l₂ := [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86, -88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1538)) (literal (valuationOf q) (1680)) (literal (valuationOf q) (1708)) (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29, -30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86, -88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) (count1689 q) 8 12 (meaning1538 q) (meaning1680 q) (meaning1708 q) hs
  change valuationOf q 1538 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1251 (q : Snake 81) (h : Conditions q) : valuation q 1538 = false ∨ valuation q 1680 = false ∨ valuation q 1708 = true := counterClause1251 (baseVal q)

theorem counterClause1252 (q : Nat → Bool) : valuationOf q 1539 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1708 = true := by
  have hs : count1689 q = (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29, -30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) + (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86, -88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29, -30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) (l₂ := [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86, -88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1539)) (literal (valuationOf q) (1679)) (literal (valuationOf q) (1708)) (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29, -30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86, -88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) (count1689 q) 9 11 (meaning1539 q) (meaning1679 q) (meaning1708 q) hs
  change valuationOf q 1539 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1252 (q : Snake 81) (h : Conditions q) : valuation q 1539 = false ∨ valuation q 1679 = false ∨ valuation q 1708 = true := counterClause1252 (baseVal q)

theorem counterClause1253 (q : Nat → Bool) : valuationOf q 1540 = false ∨ valuationOf q 1678 = false ∨ valuationOf q 1708 = true := by
  have hs : count1689 q = (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29, -30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) + (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86, -88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29, -30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) (l₂ := [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86, -88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1540)) (literal (valuationOf q) (1678)) (literal (valuationOf q) (1708)) (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29, -30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86, -88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) (count1689 q) 10 10 (meaning1540 q) (meaning1678 q) (meaning1708 q) hs
  change valuationOf q 1540 = false ∨ valuationOf q 1678 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1253 (q : Snake 81) (h : Conditions q) : valuation q 1540 = false ∨ valuation q 1678 = false ∨ valuation q 1708 = true := counterClause1253 (baseVal q)

theorem counterClause1254 (q : Nat → Bool) : valuationOf q 1541 = false ∨ valuationOf q 1677 = false ∨ valuationOf q 1708 = true := by
  have hs : count1689 q = (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29, -30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) + (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86, -88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29, -30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) (l₂ := [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86, -88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1541)) (literal (valuationOf q) (1677)) (literal (valuationOf q) (1708)) (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29, -30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86, -88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) (count1689 q) 11 9 (meaning1541 q) (meaning1677 q) (meaning1708 q) hs
  change valuationOf q 1541 = false ∨ valuationOf q 1677 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1254 (q : Snake 81) (h : Conditions q) : valuation q 1541 = false ∨ valuation q 1677 = false ∨ valuation q 1708 = true := counterClause1254 (baseVal q)

theorem counterClause1255 (q : Nat → Bool) : valuationOf q 1542 = false ∨ valuationOf q 1676 = false ∨ valuationOf q 1708 = true := by
  have hs : count1689 q = (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29, -30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) + (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86, -88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29, -30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) (l₂ := [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86, -88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1542)) (literal (valuationOf q) (1676)) (literal (valuationOf q) (1708)) (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29, -30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86, -88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) (count1689 q) 12 8 (meaning1542 q) (meaning1676 q) (meaning1708 q) hs
  change valuationOf q 1542 = false ∨ valuationOf q 1676 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1255 (q : Snake 81) (h : Conditions q) : valuation q 1542 = false ∨ valuation q 1676 = false ∨ valuation q 1708 = true := counterClause1255 (baseVal q)

theorem clause1256 (q : Snake 81) (h : Conditions q) : valuation q 1708 = false := by
  rw [value1708]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1689 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause1257 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 22 = false ∨ valuation q 52 = false ∨ valuation q 83 = false := by
  rw [value1, value22, value52, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (10 : Vertex) (138 : Vertex) (266 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1258 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 40 = false ∨ valuation q 64 = false ∨ valuation q 103 = false := by
  rw [value7, value40, value64, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (75 : Vertex) (203 : Vertex) (331 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1259 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 19 = false ∨ valuation q 22 = false ∨ valuation q 23 = false := by
  rw [value18, value19, value22, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (130 : Vertex) (131 : Vertex) (138 : Vertex) (139 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1260 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 21 = false ∨ valuation q 23 = false ∨ valuation q 25 = false := by
  rw [value19, value21, value23, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (131 : Vertex) (135 : Vertex) (139 : Vertex) (143 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1261 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 21 = false ∨ valuation q 24 = false ∨ valuation q 25 = false := by
  rw [value20, value21, value24, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (133 : Vertex) (135 : Vertex) (141 : Vertex) (143 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1262 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 40 = false ∨ valuation q 84 = false ∨ valuation q 103 = false := by
  rw [value23, value40, value84, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (139 : Vertex) (203 : Vertex) (395 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1263 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 29 = false ∨ valuation q 30 = false ∨ valuation q 31 = false := by
  rw [value26, value29, value30, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (144 : Vertex) (148 : Vertex) (152 : Vertex) (156 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1264 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 35 = false ∨ valuation q 38 = false ∨ valuation q 39 = false := by
  rw [value34, value35, value38, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (192 : Vertex) (193 : Vertex) (200 : Vertex) (201 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1265 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 35 = false ∨ valuation q 96 = false ∨ valuation q 97 = false := by
  rw [value34, value35, value96, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (192 : Vertex) (193 : Vertex) (448 : Vertex) (449 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1266 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 38 = false ∨ valuation q 96 = false ∨ valuation q 102 = false := by
  rw [value34, value38, value96, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (192 : Vertex) (200 : Vertex) (448 : Vertex) (456 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1267 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 37 = false ∨ valuation q 46 = false ∨ valuation q 47 = false := by
  rw [value36, value37, value46, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (198 : Vertex) (199 : Vertex) (214 : Vertex) (215 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1268 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 50 = false ∨ valuation q 103 = false ∨ valuation q 115 = false := by
  rw [value40, value50, value103, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (203 : Vertex) (219 : Vertex) (459 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1269 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 42 = false ∨ valuation q 104 = false ∨ valuation q 106 = false := by
  rw [value41, value42, value104, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (204 : Vertex) (206 : Vertex) (460 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1270 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 49 = false ∨ valuation q 110 = false ∨ valuation q 114 = false := by
  rw [value43, value49, value110, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (210 : Vertex) (218 : Vertex) (466 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1271 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 45 = false ∨ valuation q 46 = false ∨ valuation q 47 = false := by
  rw [value44, value45, value46, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (212 : Vertex) (213 : Vertex) (214 : Vertex) (215 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1272 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 50 = false ∨ valuation q 114 = false ∨ valuation q 115 = false := by
  rw [value49, value50, value114, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (218 : Vertex) (219 : Vertex) (474 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1273 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 60 = false ∨ valuation q 96 = false ∨ valuation q 97 = false := by
  rw [value59, value60, value96, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (320 : Vertex) (321 : Vertex) (448 : Vertex) (449 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1274 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 62 = false ∨ valuation q 65 = false ∨ valuation q 66 = false := by
  rw [value61, value62, value65, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (324 : Vertex) (326 : Vertex) (332 : Vertex) (334 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1275 (q : Snake 81) (h : Conditions q) : valuation q 64 = false ∨ valuation q 74 = false ∨ valuation q 103 = false ∨ valuation q 115 = false := by
  rw [value64, value74, value103, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (331 : Vertex) (347 : Vertex) (459 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1276 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 66 = false ∨ valuation q 104 = false ∨ valuation q 106 = false := by
  rw [value65, value66, value104, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (332 : Vertex) (334 : Vertex) (460 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1277 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 72 = false ∨ valuation q 73 = false ∨ valuation q 74 = false := by
  rw [value71, value72, value73, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (344 : Vertex) (345 : Vertex) (346 : Vertex) (347 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1278 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 77 = false ∨ valuation q 79 = false ∨ valuation q 80 = false := by
  rw [value76, value77, value79, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (384 : Vertex) (385 : Vertex) (388 : Vertex) (389 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1279 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 77 = false ∨ valuation q 96 = false ∨ valuation q 97 = false := by
  rw [value76, value77, value96, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (384 : Vertex) (385 : Vertex) (448 : Vertex) (449 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1280 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 78 = false ∨ valuation q 82 = false ∨ valuation q 83 = false := by
  rw [value76, value78, value82, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (384 : Vertex) (386 : Vertex) (392 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block39 (q : Snake 81) (h : Conditions q) : B112E110.Block39 (valuation q) :=
  ⟨clause1249 q h, clause1250 q h, clause1251 q h, clause1252 q h, clause1253 q h, clause1254 q h, clause1255 q h, clause1256 q h, clause1257 q h, clause1258 q h, clause1259 q h, clause1260 q h, clause1261 q h, clause1262 q h, clause1263 q h, clause1264 q h, clause1265 q h, clause1266 q h, clause1267 q h, clause1268 q h, clause1269 q h, clause1270 q h, clause1271 q h, clause1272 q h, clause1273 q h, clause1274 q h, clause1275 q h, clause1276 q h, clause1277 q h, clause1278 q h, clause1279 q h, clause1280 q h⟩

end
end Snake9.Regrowth.E112110
