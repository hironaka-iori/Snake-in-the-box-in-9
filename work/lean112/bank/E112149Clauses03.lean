import E112149Semantics
import B112E149Inputs
namespace Snake9.Regrowth.E112149
noncomputable section
local instance blockDec3 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause97 (q : Snake 81) (h : Conditions q) : valuation q 139 = false := by
  rw [value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (243 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause98 (q : Snake 81) (h : Conditions q) : valuation q 159 = false := by
  rw [value159]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (354 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause99 (q : Snake 81) (h : Conditions q) : valuation q 162 = false := by
  rw [value162]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (368 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause100 (q : Snake 81) (h : Conditions q) : valuation q 164 = false := by
  rw [value164]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (371 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause101 (q : Snake 81) (h : Conditions q) : valuation q 166 = false := by
  rw [value166]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (380 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem counterClause102 (q : Nat → Bool) : valuationOf q 101 = false ∨ valuationOf q 199 = true := by
  have hs : count199 q = (countLit q [101]) + (countLit q [102]) := List.countP_append (p := literal q) (l₁ := [101]) (l₂ := [102])
  have hm := merge_left (literal (valuationOf q) (101)) (literal (valuationOf q) (199)) (countLit q [101]) (countLit q [102]) (count199 q) 1 (meaning101 q) (meaning199 q) hs
  change valuationOf q 101 = false ∨ valuationOf q 199 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause102 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 199 = true := counterClause102 (baseVal q)

theorem counterClause103 (q : Nat → Bool) : valuationOf q 199 = false ∨ valuationOf q 201 = true := by
  have hs : count201 q = (countLit q [100]) + (countLit q [101, 102]) := List.countP_append (p := literal q) (l₁ := [100]) (l₂ := [101, 102])
  have hm := merge_right (literal (valuationOf q) (199)) (literal (valuationOf q) (201)) (countLit q [100]) (countLit q [101, 102]) (count201 q) 1 (meaning199 q) (meaning201 q) hs
  change valuationOf q 199 = false ∨ valuationOf q 201 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause103 (q : Snake 81) (h : Conditions q) : valuation q 199 = false ∨ valuation q 201 = true := counterClause103 (baseVal q)

theorem counterClause104 (q : Nat → Bool) : valuationOf q 105 = false ∨ valuationOf q 203 = true := by
  have hs : count203 q = (countLit q [104]) + (countLit q [105]) := List.countP_append (p := literal q) (l₁ := [104]) (l₂ := [105])
  have hm := merge_right (literal (valuationOf q) (105)) (literal (valuationOf q) (203)) (countLit q [104]) (countLit q [105]) (count203 q) 1 (meaning105 q) (meaning203 q) hs
  change valuationOf q 105 = false ∨ valuationOf q 203 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause104 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 203 = true := counterClause104 (baseVal q)

theorem counterClause105 (q : Nat → Bool) : valuationOf q 203 = false ∨ valuationOf q 205 = true := by
  have hs : count205 q = (countLit q [103]) + (countLit q [104, 105]) := List.countP_append (p := literal q) (l₁ := [103]) (l₂ := [104, 105])
  have hm := merge_right (literal (valuationOf q) (203)) (literal (valuationOf q) (205)) (countLit q [103]) (countLit q [104, 105]) (count205 q) 1 (meaning203 q) (meaning205 q) hs
  change valuationOf q 203 = false ∨ valuationOf q 205 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause105 (q : Snake 81) (h : Conditions q) : valuation q 203 = false ∨ valuation q 205 = true := counterClause105 (baseVal q)

theorem counterClause106 (q : Nat → Bool) : valuationOf q 201 = false ∨ valuationOf q 205 = false ∨ valuationOf q 208 = true := by
  have hs : count207 q = (countLit q [100, 101, 102]) + (countLit q [103, 104, 105]) := List.countP_append (p := literal q) (l₁ := [100, 101, 102]) (l₂ := [103, 104, 105])
  have hm := merge_two (literal (valuationOf q) (201)) (literal (valuationOf q) (205)) (literal (valuationOf q) (208)) (countLit q [100, 101, 102]) (countLit q [103, 104, 105]) (count207 q) 1 1 (meaning201 q) (meaning205 q) (meaning208 q) hs
  change valuationOf q 201 = false ∨ valuationOf q 205 = false ∨ valuationOf q 208 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause106 (q : Snake 81) (h : Conditions q) : valuation q 201 = false ∨ valuation q 205 = false ∨ valuation q 208 = true := counterClause106 (baseVal q)

theorem counterClause107 (q : Nat → Bool) : valuationOf q 107 = false ∨ valuationOf q 209 = true := by
  have hs : count209 q = (countLit q [107]) + (countLit q [108]) := List.countP_append (p := literal q) (l₁ := [107]) (l₂ := [108])
  have hm := merge_left (literal (valuationOf q) (107)) (literal (valuationOf q) (209)) (countLit q [107]) (countLit q [108]) (count209 q) 1 (meaning107 q) (meaning209 q) hs
  change valuationOf q 107 = false ∨ valuationOf q 209 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause107 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 209 = true := counterClause107 (baseVal q)

theorem counterClause108 (q : Nat → Bool) : valuationOf q 209 = false ∨ valuationOf q 211 = true := by
  have hs : count211 q = (countLit q [106]) + (countLit q [107, 108]) := List.countP_append (p := literal q) (l₁ := [106]) (l₂ := [107, 108])
  have hm := merge_right (literal (valuationOf q) (209)) (literal (valuationOf q) (211)) (countLit q [106]) (countLit q [107, 108]) (count211 q) 1 (meaning209 q) (meaning211 q) hs
  change valuationOf q 209 = false ∨ valuationOf q 211 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause108 (q : Snake 81) (h : Conditions q) : valuation q 209 = false ∨ valuation q 211 = true := counterClause108 (baseVal q)

theorem counterClause109 (q : Nat → Bool) : valuationOf q 109 = false ∨ valuationOf q 215 = true := by
  have hs : count215 q = (countLit q [109]) + (countLit q [110, 111]) := List.countP_append (p := literal q) (l₁ := [109]) (l₂ := [110, 111])
  have hm := merge_left (literal (valuationOf q) (109)) (literal (valuationOf q) (215)) (countLit q [109]) (countLit q [110, 111]) (count215 q) 1 (meaning109 q) (meaning215 q) hs
  change valuationOf q 109 = false ∨ valuationOf q 215 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause109 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 215 = true := counterClause109 (baseVal q)

theorem counterClause110 (q : Nat → Bool) : valuationOf q 211 = false ∨ valuationOf q 215 = false ∨ valuationOf q 218 = true := by
  have hs : count217 q = (countLit q [106, 107, 108]) + (countLit q [109, 110, 111]) := List.countP_append (p := literal q) (l₁ := [106, 107, 108]) (l₂ := [109, 110, 111])
  have hm := merge_two (literal (valuationOf q) (211)) (literal (valuationOf q) (215)) (literal (valuationOf q) (218)) (countLit q [106, 107, 108]) (countLit q [109, 110, 111]) (count217 q) 1 1 (meaning211 q) (meaning215 q) (meaning218 q) hs
  change valuationOf q 211 = false ∨ valuationOf q 215 = false ∨ valuationOf q 218 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause110 (q : Snake 81) (h : Conditions q) : valuation q 211 = false ∨ valuation q 215 = false ∨ valuation q 218 = true := counterClause110 (baseVal q)

theorem counterClause111 (q : Nat → Bool) : valuationOf q 218 = false ∨ valuationOf q 220 = true := by
  have hs : count219 q = (countLit q [100, 101, 102, 103, 104, 105]) + (countLit q [106, 107, 108, 109, 110, 111]) := List.countP_append (p := literal q) (l₁ := [100, 101, 102, 103, 104, 105]) (l₂ := [106, 107, 108, 109, 110, 111])
  have hm := merge_right (literal (valuationOf q) (218)) (literal (valuationOf q) (220)) (countLit q [100, 101, 102, 103, 104, 105]) (countLit q [106, 107, 108, 109, 110, 111]) (count219 q) 2 (meaning218 q) (meaning220 q) hs
  change valuationOf q 218 = false ∨ valuationOf q 220 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause111 (q : Snake 81) (h : Conditions q) : valuation q 218 = false ∨ valuation q 220 = true := counterClause111 (baseVal q)

theorem counterClause112 (q : Nat → Bool) : valuationOf q 208 = false ∨ valuationOf q 220 = true := by
  have hs : count219 q = (countLit q [100, 101, 102, 103, 104, 105]) + (countLit q [106, 107, 108, 109, 110, 111]) := List.countP_append (p := literal q) (l₁ := [100, 101, 102, 103, 104, 105]) (l₂ := [106, 107, 108, 109, 110, 111])
  have hm := merge_left (literal (valuationOf q) (208)) (literal (valuationOf q) (220)) (countLit q [100, 101, 102, 103, 104, 105]) (countLit q [106, 107, 108, 109, 110, 111]) (count219 q) 2 (meaning208 q) (meaning220 q) hs
  change valuationOf q 208 = false ∨ valuationOf q 220 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause112 (q : Snake 81) (h : Conditions q) : valuation q 208 = false ∨ valuation q 220 = true := counterClause112 (baseVal q)

theorem counterClause113 (q : Nat → Bool) : valuationOf q 113 = false ∨ valuationOf q 221 = true := by
  have hs : count221 q = (countLit q [113]) + (countLit q [114]) := List.countP_append (p := literal q) (l₁ := [113]) (l₂ := [114])
  have hm := merge_left (literal (valuationOf q) (113)) (literal (valuationOf q) (221)) (countLit q [113]) (countLit q [114]) (count221 q) 1 (meaning113 q) (meaning221 q) hs
  change valuationOf q 113 = false ∨ valuationOf q 221 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause113 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 221 = true := counterClause113 (baseVal q)

theorem counterClause114 (q : Nat → Bool) : valuationOf q 221 = false ∨ valuationOf q 223 = true := by
  have hs : count223 q = (countLit q [112]) + (countLit q [113, 114]) := List.countP_append (p := literal q) (l₁ := [112]) (l₂ := [113, 114])
  have hm := merge_right (literal (valuationOf q) (221)) (literal (valuationOf q) (223)) (countLit q [112]) (countLit q [113, 114]) (count223 q) 1 (meaning221 q) (meaning223 q) hs
  change valuationOf q 221 = false ∨ valuationOf q 223 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause114 (q : Snake 81) (h : Conditions q) : valuation q 221 = false ∨ valuation q 223 = true := counterClause114 (baseVal q)

theorem counterClause115 (q : Nat → Bool) : valuationOf q 117 = false ∨ valuationOf q 225 = true := by
  have hs : count225 q = (countLit q [116]) + (countLit q [117]) := List.countP_append (p := literal q) (l₁ := [116]) (l₂ := [117])
  have hm := merge_right (literal (valuationOf q) (117)) (literal (valuationOf q) (225)) (countLit q [116]) (countLit q [117]) (count225 q) 1 (meaning117 q) (meaning225 q) hs
  change valuationOf q 117 = false ∨ valuationOf q 225 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause115 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 225 = true := counterClause115 (baseVal q)

theorem counterClause116 (q : Nat → Bool) : valuationOf q 225 = false ∨ valuationOf q 227 = true := by
  have hs : count227 q = (countLit q [115]) + (countLit q [116, 117]) := List.countP_append (p := literal q) (l₁ := [115]) (l₂ := [116, 117])
  have hm := merge_right (literal (valuationOf q) (225)) (literal (valuationOf q) (227)) (countLit q [115]) (countLit q [116, 117]) (count227 q) 1 (meaning225 q) (meaning227 q) hs
  change valuationOf q 225 = false ∨ valuationOf q 227 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause116 (q : Snake 81) (h : Conditions q) : valuation q 225 = false ∨ valuation q 227 = true := counterClause116 (baseVal q)

theorem counterClause117 (q : Nat → Bool) : valuationOf q 227 = false ∨ valuationOf q 229 = true := by
  have hs : count229 q = (countLit q [112, 113, 114]) + (countLit q [115, 116, 117]) := List.countP_append (p := literal q) (l₁ := [112, 113, 114]) (l₂ := [115, 116, 117])
  have hm := merge_right (literal (valuationOf q) (227)) (literal (valuationOf q) (229)) (countLit q [112, 113, 114]) (countLit q [115, 116, 117]) (count229 q) 1 (meaning227 q) (meaning229 q) hs
  change valuationOf q 227 = false ∨ valuationOf q 229 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause117 (q : Snake 81) (h : Conditions q) : valuation q 227 = false ∨ valuation q 229 = true := counterClause117 (baseVal q)

theorem counterClause118 (q : Nat → Bool) : valuationOf q 223 = false ∨ valuationOf q 229 = true := by
  have hs : count229 q = (countLit q [112, 113, 114]) + (countLit q [115, 116, 117]) := List.countP_append (p := literal q) (l₁ := [112, 113, 114]) (l₂ := [115, 116, 117])
  have hm := merge_left (literal (valuationOf q) (223)) (literal (valuationOf q) (229)) (countLit q [112, 113, 114]) (countLit q [115, 116, 117]) (count229 q) 1 (meaning223 q) (meaning229 q) hs
  change valuationOf q 223 = false ∨ valuationOf q 229 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause118 (q : Snake 81) (h : Conditions q) : valuation q 223 = false ∨ valuation q 229 = true := counterClause118 (baseVal q)

theorem counterClause119 (q : Nat → Bool) : valuationOf q 119 = false ∨ valuationOf q 231 = true := by
  have hs : count231 q = (countLit q [119]) + (countLit q [120]) := List.countP_append (p := literal q) (l₁ := [119]) (l₂ := [120])
  have hm := merge_left (literal (valuationOf q) (119)) (literal (valuationOf q) (231)) (countLit q [119]) (countLit q [120]) (count231 q) 1 (meaning119 q) (meaning231 q) hs
  change valuationOf q 119 = false ∨ valuationOf q 231 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause119 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 231 = true := counterClause119 (baseVal q)

theorem counterClause120 (q : Nat → Bool) : valuationOf q 231 = false ∨ valuationOf q 233 = true := by
  have hs : count233 q = (countLit q [118]) + (countLit q [119, 120]) := List.countP_append (p := literal q) (l₁ := [118]) (l₂ := [119, 120])
  have hm := merge_right (literal (valuationOf q) (231)) (literal (valuationOf q) (233)) (countLit q [118]) (countLit q [119, 120]) (count233 q) 1 (meaning231 q) (meaning233 q) hs
  change valuationOf q 231 = false ∨ valuationOf q 233 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause120 (q : Snake 81) (h : Conditions q) : valuation q 231 = false ∨ valuation q 233 = true := counterClause120 (baseVal q)

theorem counterClause121 (q : Nat → Bool) : valuationOf q 123 = false ∨ valuationOf q 235 = true := by
  have hs : count235 q = (countLit q [122]) + (countLit q [123]) := List.countP_append (p := literal q) (l₁ := [122]) (l₂ := [123])
  have hm := merge_right (literal (valuationOf q) (123)) (literal (valuationOf q) (235)) (countLit q [122]) (countLit q [123]) (count235 q) 1 (meaning123 q) (meaning235 q) hs
  change valuationOf q 123 = false ∨ valuationOf q 235 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause121 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 235 = true := counterClause121 (baseVal q)

theorem counterClause122 (q : Nat → Bool) : valuationOf q 122 = false ∨ valuationOf q 235 = true := by
  have hs : count235 q = (countLit q [122]) + (countLit q [123]) := List.countP_append (p := literal q) (l₁ := [122]) (l₂ := [123])
  have hm := merge_left (literal (valuationOf q) (122)) (literal (valuationOf q) (235)) (countLit q [122]) (countLit q [123]) (count235 q) 1 (meaning122 q) (meaning235 q) hs
  change valuationOf q 122 = false ∨ valuationOf q 235 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause122 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 235 = true := counterClause122 (baseVal q)

theorem counterClause123 (q : Nat → Bool) : valuationOf q 235 = false ∨ valuationOf q 237 = true := by
  have hs : count237 q = (countLit q [121]) + (countLit q [122, 123]) := List.countP_append (p := literal q) (l₁ := [121]) (l₂ := [122, 123])
  have hm := merge_right (literal (valuationOf q) (235)) (literal (valuationOf q) (237)) (countLit q [121]) (countLit q [122, 123]) (count237 q) 1 (meaning235 q) (meaning237 q) hs
  change valuationOf q 235 = false ∨ valuationOf q 237 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause123 (q : Snake 81) (h : Conditions q) : valuation q 235 = false ∨ valuation q 237 = true := counterClause123 (baseVal q)

theorem counterClause124 (q : Nat → Bool) : valuationOf q 121 = false ∨ valuationOf q 237 = true := by
  have hs : count237 q = (countLit q [121]) + (countLit q [122, 123]) := List.countP_append (p := literal q) (l₁ := [121]) (l₂ := [122, 123])
  have hm := merge_left (literal (valuationOf q) (121)) (literal (valuationOf q) (237)) (countLit q [121]) (countLit q [122, 123]) (count237 q) 1 (meaning121 q) (meaning237 q) hs
  change valuationOf q 121 = false ∨ valuationOf q 237 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause124 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 237 = true := counterClause124 (baseVal q)

theorem counterClause125 (q : Nat → Bool) : valuationOf q 121 = false ∨ valuationOf q 235 = false ∨ valuationOf q 238 = true := by
  have hs : count237 q = (countLit q [121]) + (countLit q [122, 123]) := List.countP_append (p := literal q) (l₁ := [121]) (l₂ := [122, 123])
  have hm := merge_two (literal (valuationOf q) (121)) (literal (valuationOf q) (235)) (literal (valuationOf q) (238)) (countLit q [121]) (countLit q [122, 123]) (count237 q) 1 1 (meaning121 q) (meaning235 q) (meaning238 q) hs
  change valuationOf q 121 = false ∨ valuationOf q 235 = false ∨ valuationOf q 238 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause125 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 235 = false ∨ valuation q 238 = true := counterClause125 (baseVal q)

theorem counterClause126 (q : Nat → Bool) : valuationOf q 237 = false ∨ valuationOf q 239 = true := by
  have hs : count239 q = (countLit q [118, 119, 120]) + (countLit q [121, 122, 123]) := List.countP_append (p := literal q) (l₁ := [118, 119, 120]) (l₂ := [121, 122, 123])
  have hm := merge_right (literal (valuationOf q) (237)) (literal (valuationOf q) (239)) (countLit q [118, 119, 120]) (countLit q [121, 122, 123]) (count239 q) 1 (meaning237 q) (meaning239 q) hs
  change valuationOf q 237 = false ∨ valuationOf q 239 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause126 (q : Snake 81) (h : Conditions q) : valuation q 237 = false ∨ valuation q 239 = true := counterClause126 (baseVal q)

theorem counterClause127 (q : Nat → Bool) : valuationOf q 238 = false ∨ valuationOf q 240 = true := by
  have hs : count239 q = (countLit q [118, 119, 120]) + (countLit q [121, 122, 123]) := List.countP_append (p := literal q) (l₁ := [118, 119, 120]) (l₂ := [121, 122, 123])
  have hm := merge_right (literal (valuationOf q) (238)) (literal (valuationOf q) (240)) (countLit q [118, 119, 120]) (countLit q [121, 122, 123]) (count239 q) 2 (meaning238 q) (meaning240 q) hs
  change valuationOf q 238 = false ∨ valuationOf q 240 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause127 (q : Snake 81) (h : Conditions q) : valuation q 238 = false ∨ valuation q 240 = true := counterClause127 (baseVal q)

theorem counterClause128 (q : Nat → Bool) : valuationOf q 233 = false ∨ valuationOf q 239 = true := by
  have hs : count239 q = (countLit q [118, 119, 120]) + (countLit q [121, 122, 123]) := List.countP_append (p := literal q) (l₁ := [118, 119, 120]) (l₂ := [121, 122, 123])
  have hm := merge_left (literal (valuationOf q) (233)) (literal (valuationOf q) (239)) (countLit q [118, 119, 120]) (countLit q [121, 122, 123]) (count239 q) 1 (meaning233 q) (meaning239 q) hs
  change valuationOf q 233 = false ∨ valuationOf q 239 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause128 (q : Snake 81) (h : Conditions q) : valuation q 233 = false ∨ valuation q 239 = true := counterClause128 (baseVal q)

theorem block3 (q : Snake 81) (h : Conditions q) : B112E149.Block3 (valuation q) :=
  ⟨clause97 q h, clause98 q h, clause99 q h, clause100 q h, clause101 q h, clause102 q h, clause103 q h, clause104 q h, clause105 q h, clause106 q h, clause107 q h, clause108 q h, clause109 q h, clause110 q h, clause111 q h, clause112 q h, clause113 q h, clause114 q h, clause115 q h, clause116 q h, clause117 q h, clause118 q h, clause119 q h, clause120 q h, clause121 q h, clause122 q h, clause123 q h, clause124 q h, clause125 q h, clause126 q h, clause127 q h, clause128 q h⟩

end
end Snake9.Regrowth.E112149
