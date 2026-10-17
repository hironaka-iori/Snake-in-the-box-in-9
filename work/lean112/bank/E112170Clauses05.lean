import E112170Semantics
import B112E170Inputs
namespace Snake9.Regrowth.E112170
noncomputable section
local instance blockDec5 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause161 (q : Nat → Bool) : valuationOf q 105 = false ∨ valuationOf q 203 = true := by
  have hs : count203 q = (countLit q [104]) + (countLit q [105]) := List.countP_append (p := literal q) (l₁ := [104]) (l₂ := [105])
  have hm := merge_right (literal (valuationOf q) (105)) (literal (valuationOf q) (203)) (countLit q [104]) (countLit q [105]) (count203 q) 1 (meaning105 q) (meaning203 q) hs
  change valuationOf q 105 = false ∨ valuationOf q 203 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause161 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 203 = true := counterClause161 (baseVal q)

theorem counterClause162 (q : Nat → Bool) : valuationOf q 203 = false ∨ valuationOf q 205 = true := by
  have hs : count205 q = (countLit q [103]) + (countLit q [104, 105]) := List.countP_append (p := literal q) (l₁ := [103]) (l₂ := [104, 105])
  have hm := merge_right (literal (valuationOf q) (203)) (literal (valuationOf q) (205)) (countLit q [103]) (countLit q [104, 105]) (count205 q) 1 (meaning203 q) (meaning205 q) hs
  change valuationOf q 203 = false ∨ valuationOf q 205 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause162 (q : Snake 81) (h : Conditions q) : valuation q 203 = false ∨ valuation q 205 = true := counterClause162 (baseVal q)

theorem counterClause163 (q : Nat → Bool) : valuationOf q 103 = false ∨ valuationOf q 205 = true := by
  have hs : count205 q = (countLit q [103]) + (countLit q [104, 105]) := List.countP_append (p := literal q) (l₁ := [103]) (l₂ := [104, 105])
  have hm := merge_left (literal (valuationOf q) (103)) (literal (valuationOf q) (205)) (countLit q [103]) (countLit q [104, 105]) (count205 q) 1 (meaning103 q) (meaning205 q) hs
  change valuationOf q 103 = false ∨ valuationOf q 205 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause163 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 205 = true := counterClause163 (baseVal q)

theorem counterClause164 (q : Nat → Bool) : valuationOf q 205 = false ∨ valuationOf q 207 = true := by
  have hs : count207 q = (countLit q [100, 101, 102]) + (countLit q [103, 104, 105]) := List.countP_append (p := literal q) (l₁ := [100, 101, 102]) (l₂ := [103, 104, 105])
  have hm := merge_right (literal (valuationOf q) (205)) (literal (valuationOf q) (207)) (countLit q [100, 101, 102]) (countLit q [103, 104, 105]) (count207 q) 1 (meaning205 q) (meaning207 q) hs
  change valuationOf q 205 = false ∨ valuationOf q 207 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause164 (q : Snake 81) (h : Conditions q) : valuation q 205 = false ∨ valuation q 207 = true := counterClause164 (baseVal q)

theorem counterClause165 (q : Nat → Bool) : valuationOf q 201 = false ∨ valuationOf q 207 = true := by
  have hs : count207 q = (countLit q [100, 101, 102]) + (countLit q [103, 104, 105]) := List.countP_append (p := literal q) (l₁ := [100, 101, 102]) (l₂ := [103, 104, 105])
  have hm := merge_left (literal (valuationOf q) (201)) (literal (valuationOf q) (207)) (countLit q [100, 101, 102]) (countLit q [103, 104, 105]) (count207 q) 1 (meaning201 q) (meaning207 q) hs
  change valuationOf q 201 = false ∨ valuationOf q 207 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause165 (q : Snake 81) (h : Conditions q) : valuation q 201 = false ∨ valuation q 207 = true := counterClause165 (baseVal q)

theorem counterClause166 (q : Nat → Bool) : valuationOf q 201 = false ∨ valuationOf q 205 = false ∨ valuationOf q 208 = true := by
  have hs : count207 q = (countLit q [100, 101, 102]) + (countLit q [103, 104, 105]) := List.countP_append (p := literal q) (l₁ := [100, 101, 102]) (l₂ := [103, 104, 105])
  have hm := merge_two (literal (valuationOf q) (201)) (literal (valuationOf q) (205)) (literal (valuationOf q) (208)) (countLit q [100, 101, 102]) (countLit q [103, 104, 105]) (count207 q) 1 1 (meaning201 q) (meaning205 q) (meaning208 q) hs
  change valuationOf q 201 = false ∨ valuationOf q 205 = false ∨ valuationOf q 208 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause166 (q : Snake 81) (h : Conditions q) : valuation q 201 = false ∨ valuation q 205 = false ∨ valuation q 208 = true := counterClause166 (baseVal q)

theorem counterClause167 (q : Nat → Bool) : valuationOf q 108 = false ∨ valuationOf q 209 = true := by
  have hs : count209 q = (countLit q [107]) + (countLit q [108]) := List.countP_append (p := literal q) (l₁ := [107]) (l₂ := [108])
  have hm := merge_right (literal (valuationOf q) (108)) (literal (valuationOf q) (209)) (countLit q [107]) (countLit q [108]) (count209 q) 1 (meaning108 q) (meaning209 q) hs
  change valuationOf q 108 = false ∨ valuationOf q 209 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause167 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 209 = true := counterClause167 (baseVal q)

theorem counterClause168 (q : Nat → Bool) : valuationOf q 209 = false ∨ valuationOf q 211 = true := by
  have hs : count211 q = (countLit q [106]) + (countLit q [107, 108]) := List.countP_append (p := literal q) (l₁ := [106]) (l₂ := [107, 108])
  have hm := merge_right (literal (valuationOf q) (209)) (literal (valuationOf q) (211)) (countLit q [106]) (countLit q [107, 108]) (count211 q) 1 (meaning209 q) (meaning211 q) hs
  change valuationOf q 209 = false ∨ valuationOf q 211 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause168 (q : Snake 81) (h : Conditions q) : valuation q 209 = false ∨ valuation q 211 = true := counterClause168 (baseVal q)

theorem counterClause169 (q : Nat → Bool) : valuationOf q 106 = false ∨ valuationOf q 211 = true := by
  have hs : count211 q = (countLit q [106]) + (countLit q [107, 108]) := List.countP_append (p := literal q) (l₁ := [106]) (l₂ := [107, 108])
  have hm := merge_left (literal (valuationOf q) (106)) (literal (valuationOf q) (211)) (countLit q [106]) (countLit q [107, 108]) (count211 q) 1 (meaning106 q) (meaning211 q) hs
  change valuationOf q 106 = false ∨ valuationOf q 211 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause169 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 211 = true := counterClause169 (baseVal q)

theorem counterClause170 (q : Nat → Bool) : valuationOf q 111 = false ∨ valuationOf q 213 = true := by
  have hs : count213 q = (countLit q [110]) + (countLit q [111]) := List.countP_append (p := literal q) (l₁ := [110]) (l₂ := [111])
  have hm := merge_right (literal (valuationOf q) (111)) (literal (valuationOf q) (213)) (countLit q [110]) (countLit q [111]) (count213 q) 1 (meaning111 q) (meaning213 q) hs
  change valuationOf q 111 = false ∨ valuationOf q 213 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause170 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 213 = true := counterClause170 (baseVal q)

theorem counterClause171 (q : Nat → Bool) : valuationOf q 213 = false ∨ valuationOf q 215 = true := by
  have hs : count215 q = (countLit q [109]) + (countLit q [110, 111]) := List.countP_append (p := literal q) (l₁ := [109]) (l₂ := [110, 111])
  have hm := merge_right (literal (valuationOf q) (213)) (literal (valuationOf q) (215)) (countLit q [109]) (countLit q [110, 111]) (count215 q) 1 (meaning213 q) (meaning215 q) hs
  change valuationOf q 213 = false ∨ valuationOf q 215 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause171 (q : Snake 81) (h : Conditions q) : valuation q 213 = false ∨ valuation q 215 = true := counterClause171 (baseVal q)

theorem counterClause172 (q : Nat → Bool) : valuationOf q 215 = false ∨ valuationOf q 217 = true := by
  have hs : count217 q = (countLit q [106, 107, 108]) + (countLit q [109, 110, 111]) := List.countP_append (p := literal q) (l₁ := [106, 107, 108]) (l₂ := [109, 110, 111])
  have hm := merge_right (literal (valuationOf q) (215)) (literal (valuationOf q) (217)) (countLit q [106, 107, 108]) (countLit q [109, 110, 111]) (count217 q) 1 (meaning215 q) (meaning217 q) hs
  change valuationOf q 215 = false ∨ valuationOf q 217 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause172 (q : Snake 81) (h : Conditions q) : valuation q 215 = false ∨ valuation q 217 = true := counterClause172 (baseVal q)

theorem counterClause173 (q : Nat → Bool) : valuationOf q 211 = false ∨ valuationOf q 217 = true := by
  have hs : count217 q = (countLit q [106, 107, 108]) + (countLit q [109, 110, 111]) := List.countP_append (p := literal q) (l₁ := [106, 107, 108]) (l₂ := [109, 110, 111])
  have hm := merge_left (literal (valuationOf q) (211)) (literal (valuationOf q) (217)) (countLit q [106, 107, 108]) (countLit q [109, 110, 111]) (count217 q) 1 (meaning211 q) (meaning217 q) hs
  change valuationOf q 211 = false ∨ valuationOf q 217 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause173 (q : Snake 81) (h : Conditions q) : valuation q 211 = false ∨ valuation q 217 = true := counterClause173 (baseVal q)

theorem counterClause174 (q : Nat → Bool) : valuationOf q 217 = false ∨ valuationOf q 219 = true := by
  have hs : count219 q = (countLit q [100, 101, 102, 103, 104, 105]) + (countLit q [106, 107, 108, 109, 110, 111]) := List.countP_append (p := literal q) (l₁ := [100, 101, 102, 103, 104, 105]) (l₂ := [106, 107, 108, 109, 110, 111])
  have hm := merge_right (literal (valuationOf q) (217)) (literal (valuationOf q) (219)) (countLit q [100, 101, 102, 103, 104, 105]) (countLit q [106, 107, 108, 109, 110, 111]) (count219 q) 1 (meaning217 q) (meaning219 q) hs
  change valuationOf q 217 = false ∨ valuationOf q 219 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause174 (q : Snake 81) (h : Conditions q) : valuation q 217 = false ∨ valuation q 219 = true := counterClause174 (baseVal q)

theorem counterClause175 (q : Nat → Bool) : valuationOf q 207 = false ∨ valuationOf q 219 = true := by
  have hs : count219 q = (countLit q [100, 101, 102, 103, 104, 105]) + (countLit q [106, 107, 108, 109, 110, 111]) := List.countP_append (p := literal q) (l₁ := [100, 101, 102, 103, 104, 105]) (l₂ := [106, 107, 108, 109, 110, 111])
  have hm := merge_left (literal (valuationOf q) (207)) (literal (valuationOf q) (219)) (countLit q [100, 101, 102, 103, 104, 105]) (countLit q [106, 107, 108, 109, 110, 111]) (count219 q) 1 (meaning207 q) (meaning219 q) hs
  change valuationOf q 207 = false ∨ valuationOf q 219 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause175 (q : Snake 81) (h : Conditions q) : valuation q 207 = false ∨ valuation q 219 = true := counterClause175 (baseVal q)

theorem counterClause176 (q : Nat → Bool) : valuationOf q 207 = false ∨ valuationOf q 217 = false ∨ valuationOf q 220 = true := by
  have hs : count219 q = (countLit q [100, 101, 102, 103, 104, 105]) + (countLit q [106, 107, 108, 109, 110, 111]) := List.countP_append (p := literal q) (l₁ := [100, 101, 102, 103, 104, 105]) (l₂ := [106, 107, 108, 109, 110, 111])
  have hm := merge_two (literal (valuationOf q) (207)) (literal (valuationOf q) (217)) (literal (valuationOf q) (220)) (countLit q [100, 101, 102, 103, 104, 105]) (countLit q [106, 107, 108, 109, 110, 111]) (count219 q) 1 1 (meaning207 q) (meaning217 q) (meaning220 q) hs
  change valuationOf q 207 = false ∨ valuationOf q 217 = false ∨ valuationOf q 220 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause176 (q : Snake 81) (h : Conditions q) : valuation q 207 = false ∨ valuation q 217 = false ∨ valuation q 220 = true := counterClause176 (baseVal q)

theorem counterClause177 (q : Nat → Bool) : valuationOf q 208 = false ∨ valuationOf q 220 = true := by
  have hs : count219 q = (countLit q [100, 101, 102, 103, 104, 105]) + (countLit q [106, 107, 108, 109, 110, 111]) := List.countP_append (p := literal q) (l₁ := [100, 101, 102, 103, 104, 105]) (l₂ := [106, 107, 108, 109, 110, 111])
  have hm := merge_left (literal (valuationOf q) (208)) (literal (valuationOf q) (220)) (countLit q [100, 101, 102, 103, 104, 105]) (countLit q [106, 107, 108, 109, 110, 111]) (count219 q) 2 (meaning208 q) (meaning220 q) hs
  change valuationOf q 208 = false ∨ valuationOf q 220 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause177 (q : Snake 81) (h : Conditions q) : valuation q 208 = false ∨ valuation q 220 = true := counterClause177 (baseVal q)

theorem counterClause178 (q : Nat → Bool) : valuationOf q 219 = false ∨ valuationOf q 243 = true := by
  have hs : count243 q = (countLit q [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111]) + (countLit q [112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) := List.countP_append (p := literal q) (l₁ := [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111]) (l₂ := [112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123])
  have hm := merge_left (literal (valuationOf q) (219)) (literal (valuationOf q) (243)) (countLit q [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111]) (countLit q [112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) (count243 q) 1 (meaning219 q) (meaning243 q) hs
  change valuationOf q 219 = false ∨ valuationOf q 243 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause178 (q : Snake 81) (h : Conditions q) : valuation q 219 = false ∨ valuation q 243 = true := counterClause178 (baseVal q)

theorem counterClause179 (q : Nat → Bool) : valuationOf q 220 = false ∨ valuationOf q 244 = true := by
  have hs : count243 q = (countLit q [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111]) + (countLit q [112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) := List.countP_append (p := literal q) (l₁ := [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111]) (l₂ := [112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123])
  have hm := merge_left (literal (valuationOf q) (220)) (literal (valuationOf q) (244)) (countLit q [100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111]) (countLit q [112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]) (count243 q) 2 (meaning220 q) (meaning244 q) hs
  change valuationOf q 220 = false ∨ valuationOf q 244 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause179 (q : Snake 81) (h : Conditions q) : valuation q 220 = false ∨ valuation q 244 = true := counterClause179 (baseVal q)

theorem counterClause180 (q : Nat → Bool) : valuationOf q 129 = false ∨ valuationOf q 249 = true := by
  have hs : count249 q = (countLit q [128]) + (countLit q [129]) := List.countP_append (p := literal q) (l₁ := [128]) (l₂ := [129])
  have hm := merge_right (literal (valuationOf q) (129)) (literal (valuationOf q) (249)) (countLit q [128]) (countLit q [129]) (count249 q) 1 (meaning129 q) (meaning249 q) hs
  change valuationOf q 129 = false ∨ valuationOf q 249 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause180 (q : Snake 81) (h : Conditions q) : valuation q 129 = false ∨ valuation q 249 = true := counterClause180 (baseVal q)

theorem counterClause181 (q : Nat → Bool) : valuationOf q 249 = false ∨ valuationOf q 251 = true := by
  have hs : count251 q = (countLit q [127]) + (countLit q [128, 129]) := List.countP_append (p := literal q) (l₁ := [127]) (l₂ := [128, 129])
  have hm := merge_right (literal (valuationOf q) (249)) (literal (valuationOf q) (251)) (countLit q [127]) (countLit q [128, 129]) (count251 q) 1 (meaning249 q) (meaning251 q) hs
  change valuationOf q 249 = false ∨ valuationOf q 251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause181 (q : Snake 81) (h : Conditions q) : valuation q 249 = false ∨ valuation q 251 = true := counterClause181 (baseVal q)

theorem counterClause182 (q : Nat → Bool) : valuationOf q 127 = false ∨ valuationOf q 251 = true := by
  have hs : count251 q = (countLit q [127]) + (countLit q [128, 129]) := List.countP_append (p := literal q) (l₁ := [127]) (l₂ := [128, 129])
  have hm := merge_left (literal (valuationOf q) (127)) (literal (valuationOf q) (251)) (countLit q [127]) (countLit q [128, 129]) (count251 q) 1 (meaning127 q) (meaning251 q) hs
  change valuationOf q 127 = false ∨ valuationOf q 251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause182 (q : Snake 81) (h : Conditions q) : valuation q 127 = false ∨ valuation q 251 = true := counterClause182 (baseVal q)

theorem counterClause183 (q : Nat → Bool) : valuationOf q 251 = false ∨ valuationOf q 253 = true := by
  have hs : count253 q = (countLit q [124, 125, 126]) + (countLit q [127, 128, 129]) := List.countP_append (p := literal q) (l₁ := [124, 125, 126]) (l₂ := [127, 128, 129])
  have hm := merge_right (literal (valuationOf q) (251)) (literal (valuationOf q) (253)) (countLit q [124, 125, 126]) (countLit q [127, 128, 129]) (count253 q) 1 (meaning251 q) (meaning253 q) hs
  change valuationOf q 251 = false ∨ valuationOf q 253 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause183 (q : Snake 81) (h : Conditions q) : valuation q 251 = false ∨ valuation q 253 = true := counterClause183 (baseVal q)

theorem counterClause184 (q : Nat → Bool) : valuationOf q 253 = false ∨ valuationOf q 265 = true := by
  have hs : count265 q = (countLit q [124, 125, 126, 127, 128, 129]) + (countLit q [130, 131, 132, 133, 134, 135]) := List.countP_append (p := literal q) (l₁ := [124, 125, 126, 127, 128, 129]) (l₂ := [130, 131, 132, 133, 134, 135])
  have hm := merge_left (literal (valuationOf q) (253)) (literal (valuationOf q) (265)) (countLit q [124, 125, 126, 127, 128, 129]) (countLit q [130, 131, 132, 133, 134, 135]) (count265 q) 1 (meaning253 q) (meaning265 q) hs
  change valuationOf q 253 = false ∨ valuationOf q 265 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause184 (q : Snake 81) (h : Conditions q) : valuation q 253 = false ∨ valuation q 265 = true := counterClause184 (baseVal q)

theorem counterClause185 (q : Nat → Bool) : valuationOf q 138 = false ∨ valuationOf q 267 = true := by
  have hs : count267 q = (countLit q [137]) + (countLit q [138]) := List.countP_append (p := literal q) (l₁ := [137]) (l₂ := [138])
  have hm := merge_right (literal (valuationOf q) (138)) (literal (valuationOf q) (267)) (countLit q [137]) (countLit q [138]) (count267 q) 1 (meaning138 q) (meaning267 q) hs
  change valuationOf q 138 = false ∨ valuationOf q 267 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause185 (q : Snake 81) (h : Conditions q) : valuation q 138 = false ∨ valuation q 267 = true := counterClause185 (baseVal q)

theorem counterClause186 (q : Nat → Bool) : valuationOf q 267 = false ∨ valuationOf q 269 = true := by
  have hs : count269 q = (countLit q [136]) + (countLit q [137, 138]) := List.countP_append (p := literal q) (l₁ := [136]) (l₂ := [137, 138])
  have hm := merge_right (literal (valuationOf q) (267)) (literal (valuationOf q) (269)) (countLit q [136]) (countLit q [137, 138]) (count269 q) 1 (meaning267 q) (meaning269 q) hs
  change valuationOf q 267 = false ∨ valuationOf q 269 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause186 (q : Snake 81) (h : Conditions q) : valuation q 267 = false ∨ valuation q 269 = true := counterClause186 (baseVal q)

theorem counterClause187 (q : Nat → Bool) : valuationOf q 141 = false ∨ valuationOf q 271 = true := by
  have hs : count271 q = (countLit q [140]) + (countLit q [141]) := List.countP_append (p := literal q) (l₁ := [140]) (l₂ := [141])
  have hm := merge_right (literal (valuationOf q) (141)) (literal (valuationOf q) (271)) (countLit q [140]) (countLit q [141]) (count271 q) 1 (meaning141 q) (meaning271 q) hs
  change valuationOf q 141 = false ∨ valuationOf q 271 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause187 (q : Snake 81) (h : Conditions q) : valuation q 141 = false ∨ valuation q 271 = true := counterClause187 (baseVal q)

theorem counterClause188 (q : Nat → Bool) : valuationOf q 271 = false ∨ valuationOf q 273 = true := by
  have hs : count273 q = (countLit q [139]) + (countLit q [140, 141]) := List.countP_append (p := literal q) (l₁ := [139]) (l₂ := [140, 141])
  have hm := merge_right (literal (valuationOf q) (271)) (literal (valuationOf q) (273)) (countLit q [139]) (countLit q [140, 141]) (count273 q) 1 (meaning271 q) (meaning273 q) hs
  change valuationOf q 271 = false ∨ valuationOf q 273 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause188 (q : Snake 81) (h : Conditions q) : valuation q 271 = false ∨ valuation q 273 = true := counterClause188 (baseVal q)

theorem counterClause189 (q : Nat → Bool) : valuationOf q 273 = false ∨ valuationOf q 275 = true := by
  have hs : count275 q = (countLit q [136, 137, 138]) + (countLit q [139, 140, 141]) := List.countP_append (p := literal q) (l₁ := [136, 137, 138]) (l₂ := [139, 140, 141])
  have hm := merge_right (literal (valuationOf q) (273)) (literal (valuationOf q) (275)) (countLit q [136, 137, 138]) (countLit q [139, 140, 141]) (count275 q) 1 (meaning273 q) (meaning275 q) hs
  change valuationOf q 273 = false ∨ valuationOf q 275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause189 (q : Snake 81) (h : Conditions q) : valuation q 273 = false ∨ valuation q 275 = true := counterClause189 (baseVal q)

theorem counterClause190 (q : Nat → Bool) : valuationOf q 269 = false ∨ valuationOf q 275 = true := by
  have hs : count275 q = (countLit q [136, 137, 138]) + (countLit q [139, 140, 141]) := List.countP_append (p := literal q) (l₁ := [136, 137, 138]) (l₂ := [139, 140, 141])
  have hm := merge_left (literal (valuationOf q) (269)) (literal (valuationOf q) (275)) (countLit q [136, 137, 138]) (countLit q [139, 140, 141]) (count275 q) 1 (meaning269 q) (meaning275 q) hs
  change valuationOf q 269 = false ∨ valuationOf q 275 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause190 (q : Snake 81) (h : Conditions q) : valuation q 269 = false ∨ valuation q 275 = true := counterClause190 (baseVal q)

theorem counterClause191 (q : Nat → Bool) : valuationOf q 145 = false ∨ valuationOf q 281 = true := by
  have hs : count281 q = (countLit q [145]) + (countLit q [146]) := List.countP_append (p := literal q) (l₁ := [145]) (l₂ := [146])
  have hm := merge_left (literal (valuationOf q) (145)) (literal (valuationOf q) (281)) (countLit q [145]) (countLit q [146]) (count281 q) 1 (meaning145 q) (meaning281 q) hs
  change valuationOf q 145 = false ∨ valuationOf q 281 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause191 (q : Snake 81) (h : Conditions q) : valuation q 145 = false ∨ valuation q 281 = true := counterClause191 (baseVal q)

theorem counterClause192 (q : Nat → Bool) : valuationOf q 281 = false ∨ valuationOf q 285 = true := by
  have hs : count285 q = (countLit q [145, 146]) + (countLit q [147, 148]) := List.countP_append (p := literal q) (l₁ := [145, 146]) (l₂ := [147, 148])
  have hm := merge_left (literal (valuationOf q) (281)) (literal (valuationOf q) (285)) (countLit q [145, 146]) (countLit q [147, 148]) (count285 q) 1 (meaning281 q) (meaning285 q) hs
  change valuationOf q 281 = false ∨ valuationOf q 285 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause192 (q : Snake 81) (h : Conditions q) : valuation q 281 = false ∨ valuation q 285 = true := counterClause192 (baseVal q)

theorem block5 (q : Snake 81) (h : Conditions q) : B112E170.Block5 (valuation q) :=
  ⟨clause161 q h, clause162 q h, clause163 q h, clause164 q h, clause165 q h, clause166 q h, clause167 q h, clause168 q h, clause169 q h, clause170 q h, clause171 q h, clause172 q h, clause173 q h, clause174 q h, clause175 q h, clause176 q h, clause177 q h, clause178 q h, clause179 q h, clause180 q h, clause181 q h, clause182 q h, clause183 q h, clause184 q h, clause185 q h, clause186 q h, clause187 q h, clause188 q h, clause189 q h, clause190 q h, clause191 q h, clause192 q h⟩

end
end Snake9.Regrowth.E112170
