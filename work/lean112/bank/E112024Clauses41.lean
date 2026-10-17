import E112024Semantics
import B112E024Inputs
namespace Snake9.Regrowth.E112024
noncomputable section
local instance blockDec41 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1313 (q : Nat → Bool) : valuationOf q 1578 = false ∨ valuationOf q 1726 = false ∨ valuationOf q 1762 = true := by
  have hs : count1740 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26, -28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) + (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89, -91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26, -28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (l₂ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89, -91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1578)) (literal (valuationOf q) (1726)) (literal (valuationOf q) (1762)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26, -28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89, -91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1740 q) 13 10 (meaning1578 q) (meaning1726 q) (meaning1762 q) hs
  change valuationOf q 1578 = false ∨ valuationOf q 1726 = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1313 (q : Snake 81) (h : Conditions q) : valuation q 1578 = false ∨ valuation q 1726 = false ∨ valuation q 1762 = true := counterClause1313 (baseVal q)

theorem counterClause1314 (q : Nat → Bool) : valuationOf q 1579 = false ∨ valuationOf q 1725 = false ∨ valuationOf q 1762 = true := by
  have hs : count1740 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26, -28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) + (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89, -91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26, -28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (l₂ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89, -91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1579)) (literal (valuationOf q) (1725)) (literal (valuationOf q) (1762)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26, -28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89, -91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1740 q) 14 9 (meaning1579 q) (meaning1725 q) (meaning1762 q) hs
  change valuationOf q 1579 = false ∨ valuationOf q 1725 = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1314 (q : Snake 81) (h : Conditions q) : valuation q 1579 = false ∨ valuation q 1725 = false ∨ valuation q 1762 = true := counterClause1314 (baseVal q)

theorem counterClause1315 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1724 = false ∨ valuationOf q 1762 = true := by
  have hs : count1740 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26, -28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) + (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89, -91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26, -28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (l₂ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89, -91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1580)) (literal (valuationOf q) (1724)) (literal (valuationOf q) (1762)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26, -28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89, -91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1740 q) 15 8 (meaning1580 q) (meaning1724 q) (meaning1762 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1724 = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1315 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1724 = false ∨ valuation q 1762 = true := counterClause1315 (baseVal q)

theorem counterClause1316 (q : Nat → Bool) : valuationOf q 1581 = false ∨ valuationOf q 1723 = false ∨ valuationOf q 1762 = true := by
  have hs : count1740 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26, -28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) + (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89, -91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26, -28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (l₂ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89, -91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1581)) (literal (valuationOf q) (1723)) (literal (valuationOf q) (1762)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26, -28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89, -91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1740 q) 16 7 (meaning1581 q) (meaning1723 q) (meaning1762 q) hs
  change valuationOf q 1581 = false ∨ valuationOf q 1723 = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1316 (q : Snake 81) (h : Conditions q) : valuation q 1581 = false ∨ valuation q 1723 = false ∨ valuation q 1762 = true := counterClause1316 (baseVal q)

theorem clause1317 (q : Snake 81) (h : Conditions q) : valuation q 1762 = false := by
  rw [value1762]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1740 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause1318 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 4 = false ∨ valuation q 9 = false ∨ valuation q 11 = false := by
  rw [value1, value4, value9, value11]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (35 : Vertex) (39 : Vertex) (99 : Vertex) (103 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1319 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 9 = false ∨ valuation q 15 = false ∨ valuation q 33 = false := by
  rw [value1, value9, value15, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (35 : Vertex) (99 : Vertex) (163 : Vertex) (227 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1320 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 14 = false ∨ valuation q 15 = false := by
  rw [value12, value13, value14, value15]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (160 : Vertex) (161 : Vertex) (162 : Vertex) (163 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1321 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 22 = false ∨ valuation q 23 = false := by
  rw [value12, value13, value22, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (160 : Vertex) (161 : Vertex) (176 : Vertex) (177 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1322 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 81 = false ∨ valuation q 82 = false := by
  rw [value12, value13, value81, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (160 : Vertex) (161 : Vertex) (416 : Vertex) (417 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1323 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 18 = false ∨ valuation q 22 = false ∨ valuation q 27 = false := by
  rw [value12, value18, value22, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (160 : Vertex) (168 : Vertex) (176 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1324 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 18 = false ∨ valuation q 81 = false ∨ valuation q 88 = false := by
  rw [value12, value18, value81, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (160 : Vertex) (168 : Vertex) (416 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1325 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 15 = false ∨ valuation q 23 = false ∨ valuation q 25 = false := by
  rw [value13, value15, value23, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (161 : Vertex) (163 : Vertex) (177 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1326 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 16 = false ∨ valuation q 82 = false ∨ valuation q 85 = false := by
  rw [value13, value16, value82, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (161 : Vertex) (165 : Vertex) (417 : Vertex) (421 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1327 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 23 = false ∨ valuation q 82 = false ∨ valuation q 94 = false := by
  rw [value13, value23, value82, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (161 : Vertex) (177 : Vertex) (417 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1328 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 15 = false ∨ valuation q 32 = false ∨ valuation q 33 = false := by
  rw [value14, value15, value32, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (162 : Vertex) (163 : Vertex) (226 : Vertex) (227 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1329 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 17 = false ∨ valuation q 24 = false ∨ valuation q 26 = false := by
  rw [value14, value17, value24, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (162 : Vertex) (166 : Vertex) (178 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1330 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 19 = false ∨ valuation q 33 = false ∨ valuation q 38 = false := by
  rw [value15, value19, value33, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (163 : Vertex) (171 : Vertex) (227 : Vertex) (235 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1331 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 27 = false ∨ valuation q 88 = false ∨ valuation q 99 = false := by
  rw [value18, value27, value88, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (168 : Vertex) (184 : Vertex) (424 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1332 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 21 = false ∨ valuation q 90 = false ∨ valuation q 93 = false := by
  rw [value19, value21, value90, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (171 : Vertex) (175 : Vertex) (427 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1333 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 38 = false ∨ valuation q 90 = false ∨ valuation q 110 = false := by
  rw [value19, value38, value90, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (171 : Vertex) (235 : Vertex) (427 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1334 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 21 = false ∨ valuation q 29 = false ∨ valuation q 31 = false := by
  rw [value20, value21, value29, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (173 : Vertex) (175 : Vertex) (189 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1335 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 23 = false ∨ valuation q 24 = false ∨ valuation q 25 = false := by
  rw [value22, value23, value24, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (176 : Vertex) (177 : Vertex) (178 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1336 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 25 = false ∨ valuation q 94 = false ∨ valuation q 95 = false := by
  rw [value23, value25, value94, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (177 : Vertex) (179 : Vertex) (433 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1337 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 29 = false ∨ valuation q 30 = false ∨ valuation q 31 = false := by
  rw [value28, value29, value30, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (188 : Vertex) (189 : Vertex) (190 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1338 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 36 = false ∨ valuation q 37 = false ∨ valuation q 40 = false := by
  rw [value32, value36, value37, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (226 : Vertex) (230 : Vertex) (234 : Vertex) (238 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1339 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 35 = false ∨ valuation q 41 = false ∨ valuation q 42 = false := by
  rw [value34, value35, value41, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (228 : Vertex) (229 : Vertex) (244 : Vertex) (245 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1340 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 36 = false ∨ valuation q 39 = false ∨ valuation q 40 = false := by
  rw [value34, value36, value39, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (228 : Vertex) (230 : Vertex) (236 : Vertex) (238 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1341 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 45 = false ∨ valuation q 46 = false ∨ valuation q 47 = false := by
  rw [value44, value45, value46, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (248 : Vertex) (249 : Vertex) (250 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1342 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 50 = false ∨ valuation q 58 = false ∨ valuation q 59 = false := by
  rw [value49, value50, value58, value59]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (288 : Vertex) (289 : Vertex) (304 : Vertex) (305 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1343 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 54 = false ∨ valuation q 81 = false ∨ valuation q 88 = false := by
  rw [value49, value54, value81, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (288 : Vertex) (296 : Vertex) (416 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1344 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 53 = false ∨ valuation q 56 = false ∨ valuation q 57 = false := by
  rw [value51, value53, value56, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (293 : Vertex) (295 : Vertex) (301 : Vertex) (303 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block41 (q : Snake 81) (h : Conditions q) : B112E024.Block41 (valuation q) :=
  ⟨clause1313 q h, clause1314 q h, clause1315 q h, clause1316 q h, clause1317 q h, clause1318 q h, clause1319 q h, clause1320 q h, clause1321 q h, clause1322 q h, clause1323 q h, clause1324 q h, clause1325 q h, clause1326 q h, clause1327 q h, clause1328 q h, clause1329 q h, clause1330 q h, clause1331 q h, clause1332 q h, clause1333 q h, clause1334 q h, clause1335 q h, clause1336 q h, clause1337 q h, clause1338 q h, clause1339 q h, clause1340 q h, clause1341 q h, clause1342 q h, clause1343 q h, clause1344 q h⟩

end
end Snake9.Regrowth.E112024
