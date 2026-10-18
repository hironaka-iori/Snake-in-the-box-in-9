import E112179Semantics
import B112E179Inputs
namespace Snake9.Regrowth.E112179
noncomputable section
local instance blockDec12 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause385 (q : Nat → Bool) : valuationOf q 308 = false ∨ valuationOf q 412 = true := by
  have hs : count411 q = (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) + (countLit q [156, 157, 158, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (l₂ := [156, 157, 158, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208])
  have hm := merge_left (literal (valuationOf q) (308)) (literal (valuationOf q) (412)) (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]) (countLit q [156, 157, 158, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (count411 q) 2 (meaning308 q) (meaning412 q) hs
  change valuationOf q 308 = false ∨ valuationOf q 412 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause385 (q : Snake 81) (h : Conditions q) : valuation q 308 = false ∨ valuation q 412 = true := counterClause385 (baseVal q)

theorem clause386 (q : Snake 81) (h : Conditions q) : valuation q 412 = false := by
  rw [value412]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count411 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem clause387 (q : Snake 81) (h : Conditions q) : valuation q 105 = true ∨ valuation q 106 = true ∨ valuation q 107 = true ∨ valuation q 108 = true ∨ valuation q 109 = true ∨ valuation q 110 = true ∨ valuation q 111 = true ∨ valuation q 112 = true ∨ valuation q 113 = true ∨ valuation q 114 = true ∨ valuation q 115 = true ∨ valuation q 116 = true ∨ valuation q 117 = true ∨ valuation q 118 = true ∨ valuation q 119 = true ∨ valuation q 120 = true ∨ valuation q 121 = true ∨ valuation q 122 = true ∨ valuation q 123 = true ∨ valuation q 124 = true ∨ valuation q 125 = true ∨ valuation q 126 = true ∨ valuation q 127 = true ∨ valuation q 128 = true ∨ valuation q 129 = true ∨ valuation q 130 = true ∨ valuation q 131 = true ∨ valuation q 132 = true ∨ valuation q 133 = true ∨ valuation q 134 = true ∨ valuation q 135 = true ∨ valuation q 136 = true ∨ valuation q 137 = true ∨ valuation q 138 = true ∨ valuation q 139 = true ∨ valuation q 140 = true ∨ valuation q 141 = true ∨ valuation q 142 = true ∨ valuation q 143 = true ∨ valuation q 144 = true ∨ valuation q 145 = true ∨ valuation q 146 = true ∨ valuation q 147 = true ∨ valuation q 148 = true ∨ valuation q 149 = true ∨ valuation q 150 = true ∨ valuation q 151 = true ∨ valuation q 152 = true ∨ valuation q 153 = true ∨ valuation q 154 = true ∨ valuation q 155 = true ∨ valuation q 156 = true ∨ valuation q 157 = true ∨ valuation q 158 = true ∨ valuation q 160 = true ∨ valuation q 161 = true ∨ valuation q 162 = true ∨ valuation q 163 = true ∨ valuation q 164 = true ∨ valuation q 165 = true ∨ valuation q 166 = true ∨ valuation q 167 = true ∨ valuation q 168 = true ∨ valuation q 169 = true ∨ valuation q 170 = true ∨ valuation q 171 = true ∨ valuation q 172 = true ∨ valuation q 173 = true ∨ valuation q 174 = true ∨ valuation q 175 = true ∨ valuation q 176 = true ∨ valuation q 177 = true ∨ valuation q 178 = true ∨ valuation q 179 = true ∨ valuation q 180 = true ∨ valuation q 181 = true ∨ valuation q 182 = true ∨ valuation q 183 = true ∨ valuation q 184 = true ∨ valuation q 185 = true ∨ valuation q 186 = true ∨ valuation q 187 = true ∨ valuation q 188 = true ∨ valuation q 189 = true ∨ valuation q 190 = true ∨ valuation q 191 = true ∨ valuation q 192 = true ∨ valuation q 193 = true ∨ valuation q 194 = true ∨ valuation q 195 = true ∨ valuation q 196 = true ∨ valuation q 197 = true ∨ valuation q 198 = true ∨ valuation q 199 = true ∨ valuation q 200 = true ∨ valuation q 201 = true ∨ valuation q 202 = true ∨ valuation q 203 = true ∨ valuation q 204 = true ∨ valuation q 205 = true ∨ valuation q 206 = true ∨ valuation q 207 = true ∨ valuation q 208 = true := by
  rw [value105, value106, value107, value108, value109, value110, value111, value112, value113, value114, value115, value116, value117, value118, value119, value120, value121, value122, value123, value124, value125, value126, value127, value128, value129, value130, value131, value132, value133, value134, value135, value136, value137, value138, value139, value140, value141, value142, value143, value144, value145, value146, value147, value148, value149, value150, value151, value152, value153, value154, value155, value156, value157, value158, value160, value161, value162, value163, value164, value165, value166, value167, value168, value169, value170, value171, value172, value173, value174, value175, value176, value177, value178, value179, value180, value181, value182, value183, value184, value185, value186, value187, value188, value189, value190, value191, value192, value193, value194, value195, value196, value197, value198, value199, value200, value201, value202, value203, value204, value205, value206, value207, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hg := other_endpoint q others (fun v hv hn => others_mem v (h.covered v hv) (by simpa only [h.head_fixed] using hn))
  simpa only [others, List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem counterClause388 (q : Nat → Bool) : valuationOf q 7 = true ∨ valuationOf q 1241 = true := by
  have hs : count1241 q = (countLit q [-6]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-7])
  have hm := merge_right (literal (valuationOf q) (-7)) (literal (valuationOf q) (1241)) (countLit q [-6]) (countLit q [-7]) (count1241 q) 1 (meaningNeg7 q) (meaning1241 q) hs
  change (! (valuationOf q 7)) = false ∨ valuationOf q 1241 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause388 (q : Snake 81) (h : Conditions q) : valuation q 7 = true ∨ valuation q 1241 = true := counterClause388 (baseVal q)

theorem counterClause389 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 1241 = true := by
  have hs : count1241 q = (countLit q [-6]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-7])
  have hm := merge_left (literal (valuationOf q) (-6)) (literal (valuationOf q) (1241)) (countLit q [-6]) (countLit q [-7]) (count1241 q) 1 (meaningNeg6 q) (meaning1241 q) hs
  change (! (valuationOf q 6)) = false ∨ valuationOf q 1241 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause389 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 1241 = true := counterClause389 (baseVal q)

theorem counterClause390 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 7 = true ∨ valuationOf q 1242 = true := by
  have hs : count1241 q = (countLit q [-6]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-7])
  have hm := merge_two (literal (valuationOf q) (-6)) (literal (valuationOf q) (-7)) (literal (valuationOf q) (1242)) (countLit q [-6]) (countLit q [-7]) (count1241 q) 1 1 (meaningNeg6 q) (meaningNeg7 q) (meaning1242 q) hs
  change (! (valuationOf q 6)) = false ∨ (! (valuationOf q 7)) = false ∨ valuationOf q 1242 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause390 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 7 = true ∨ valuation q 1242 = true := counterClause390 (baseVal q)

theorem counterClause391 (q : Nat → Bool) : valuationOf q 1241 = false ∨ valuationOf q 1243 = true := by
  have hs : count1243 q = (countLit q [-2]) + (countLit q [-6, -7]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-6, -7])
  have hm := merge_right (literal (valuationOf q) (1241)) (literal (valuationOf q) (1243)) (countLit q [-2]) (countLit q [-6, -7]) (count1243 q) 1 (meaning1241 q) (meaning1243 q) hs
  change valuationOf q 1241 = false ∨ valuationOf q 1243 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause391 (q : Snake 81) (h : Conditions q) : valuation q 1241 = false ∨ valuation q 1243 = true := counterClause391 (baseVal q)

theorem counterClause392 (q : Nat → Bool) : valuationOf q 1242 = false ∨ valuationOf q 1244 = true := by
  have hs : count1243 q = (countLit q [-2]) + (countLit q [-6, -7]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-6, -7])
  have hm := merge_right (literal (valuationOf q) (1242)) (literal (valuationOf q) (1244)) (countLit q [-2]) (countLit q [-6, -7]) (count1243 q) 2 (meaning1242 q) (meaning1244 q) hs
  change valuationOf q 1242 = false ∨ valuationOf q 1244 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause392 (q : Snake 81) (h : Conditions q) : valuation q 1242 = false ∨ valuation q 1244 = true := counterClause392 (baseVal q)

theorem counterClause393 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1243 = true := by
  have hs : count1243 q = (countLit q [-2]) + (countLit q [-6, -7]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-6, -7])
  have hm := merge_left (literal (valuationOf q) (-2)) (literal (valuationOf q) (1243)) (countLit q [-2]) (countLit q [-6, -7]) (count1243 q) 1 (meaningNeg2 q) (meaning1243 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1243 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause393 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1243 = true := counterClause393 (baseVal q)

theorem counterClause394 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1241 = false ∨ valuationOf q 1244 = true := by
  have hs : count1243 q = (countLit q [-2]) + (countLit q [-6, -7]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-6, -7])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (1241)) (literal (valuationOf q) (1244)) (countLit q [-2]) (countLit q [-6, -7]) (count1243 q) 1 1 (meaningNeg2 q) (meaning1241 q) (meaning1244 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1241 = false ∨ valuationOf q 1244 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause394 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1241 = false ∨ valuation q 1244 = true := counterClause394 (baseVal q)

theorem counterClause395 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1242 = false ∨ valuationOf q 1245 = true := by
  have hs : count1243 q = (countLit q [-2]) + (countLit q [-6, -7]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-6, -7])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (1242)) (literal (valuationOf q) (1245)) (countLit q [-2]) (countLit q [-6, -7]) (count1243 q) 1 2 (meaningNeg2 q) (meaning1242 q) (meaning1245 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1242 = false ∨ valuationOf q 1245 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause395 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1242 = false ∨ valuation q 1245 = true := counterClause395 (baseVal q)

theorem counterClause396 (q : Nat → Bool) : valuationOf q 12 = true ∨ valuationOf q 1246 = true := by
  have hs : count1246 q = (countLit q [-10]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-12])
  have hm := merge_right (literal (valuationOf q) (-12)) (literal (valuationOf q) (1246)) (countLit q [-10]) (countLit q [-12]) (count1246 q) 1 (meaningNeg12 q) (meaning1246 q) hs
  change (! (valuationOf q 12)) = false ∨ valuationOf q 1246 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause396 (q : Snake 81) (h : Conditions q) : valuation q 12 = true ∨ valuation q 1246 = true := counterClause396 (baseVal q)

theorem counterClause397 (q : Nat → Bool) : valuationOf q 10 = true ∨ valuationOf q 1246 = true := by
  have hs : count1246 q = (countLit q [-10]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-12])
  have hm := merge_left (literal (valuationOf q) (-10)) (literal (valuationOf q) (1246)) (countLit q [-10]) (countLit q [-12]) (count1246 q) 1 (meaningNeg10 q) (meaning1246 q) hs
  change (! (valuationOf q 10)) = false ∨ valuationOf q 1246 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause397 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 1246 = true := counterClause397 (baseVal q)

theorem counterClause398 (q : Nat → Bool) : valuationOf q 10 = true ∨ valuationOf q 12 = true ∨ valuationOf q 1247 = true := by
  have hs : count1246 q = (countLit q [-10]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-12])
  have hm := merge_two (literal (valuationOf q) (-10)) (literal (valuationOf q) (-12)) (literal (valuationOf q) (1247)) (countLit q [-10]) (countLit q [-12]) (count1246 q) 1 1 (meaningNeg10 q) (meaningNeg12 q) (meaning1247 q) hs
  change (! (valuationOf q 10)) = false ∨ (! (valuationOf q 12)) = false ∨ valuationOf q 1247 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause398 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 12 = true ∨ valuation q 1247 = true := counterClause398 (baseVal q)

theorem counterClause399 (q : Nat → Bool) : valuationOf q 1246 = false ∨ valuationOf q 1248 = true := by
  have hs : count1248 q = (countLit q [-8]) + (countLit q [-10, -12]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-10, -12])
  have hm := merge_right (literal (valuationOf q) (1246)) (literal (valuationOf q) (1248)) (countLit q [-8]) (countLit q [-10, -12]) (count1248 q) 1 (meaning1246 q) (meaning1248 q) hs
  change valuationOf q 1246 = false ∨ valuationOf q 1248 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause399 (q : Snake 81) (h : Conditions q) : valuation q 1246 = false ∨ valuation q 1248 = true := counterClause399 (baseVal q)

theorem counterClause400 (q : Nat → Bool) : valuationOf q 1247 = false ∨ valuationOf q 1249 = true := by
  have hs : count1248 q = (countLit q [-8]) + (countLit q [-10, -12]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-10, -12])
  have hm := merge_right (literal (valuationOf q) (1247)) (literal (valuationOf q) (1249)) (countLit q [-8]) (countLit q [-10, -12]) (count1248 q) 2 (meaning1247 q) (meaning1249 q) hs
  change valuationOf q 1247 = false ∨ valuationOf q 1249 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause400 (q : Snake 81) (h : Conditions q) : valuation q 1247 = false ∨ valuation q 1249 = true := counterClause400 (baseVal q)

theorem counterClause401 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 1248 = true := by
  have hs : count1248 q = (countLit q [-8]) + (countLit q [-10, -12]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-10, -12])
  have hm := merge_left (literal (valuationOf q) (-8)) (literal (valuationOf q) (1248)) (countLit q [-8]) (countLit q [-10, -12]) (count1248 q) 1 (meaningNeg8 q) (meaning1248 q) hs
  change (! (valuationOf q 8)) = false ∨ valuationOf q 1248 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause401 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 1248 = true := counterClause401 (baseVal q)

theorem counterClause402 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 1246 = false ∨ valuationOf q 1249 = true := by
  have hs : count1248 q = (countLit q [-8]) + (countLit q [-10, -12]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-10, -12])
  have hm := merge_two (literal (valuationOf q) (-8)) (literal (valuationOf q) (1246)) (literal (valuationOf q) (1249)) (countLit q [-8]) (countLit q [-10, -12]) (count1248 q) 1 1 (meaningNeg8 q) (meaning1246 q) (meaning1249 q) hs
  change (! (valuationOf q 8)) = false ∨ valuationOf q 1246 = false ∨ valuationOf q 1249 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause402 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 1246 = false ∨ valuation q 1249 = true := counterClause402 (baseVal q)

theorem counterClause403 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 1247 = false ∨ valuationOf q 1250 = true := by
  have hs : count1248 q = (countLit q [-8]) + (countLit q [-10, -12]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-10, -12])
  have hm := merge_two (literal (valuationOf q) (-8)) (literal (valuationOf q) (1247)) (literal (valuationOf q) (1250)) (countLit q [-8]) (countLit q [-10, -12]) (count1248 q) 1 2 (meaningNeg8 q) (meaning1247 q) (meaning1250 q) hs
  change (! (valuationOf q 8)) = false ∨ valuationOf q 1247 = false ∨ valuationOf q 1250 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause403 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 1247 = false ∨ valuation q 1250 = true := counterClause403 (baseVal q)

theorem counterClause404 (q : Nat → Bool) : valuationOf q 1248 = false ∨ valuationOf q 1251 = true := by
  have hs : count1251 q = (countLit q [-2, -6, -7]) + (countLit q [-8, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7]) (l₂ := [-8, -10, -12])
  have hm := merge_right (literal (valuationOf q) (1248)) (literal (valuationOf q) (1251)) (countLit q [-2, -6, -7]) (countLit q [-8, -10, -12]) (count1251 q) 1 (meaning1248 q) (meaning1251 q) hs
  change valuationOf q 1248 = false ∨ valuationOf q 1251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause404 (q : Snake 81) (h : Conditions q) : valuation q 1248 = false ∨ valuation q 1251 = true := counterClause404 (baseVal q)

theorem counterClause405 (q : Nat → Bool) : valuationOf q 1249 = false ∨ valuationOf q 1252 = true := by
  have hs : count1251 q = (countLit q [-2, -6, -7]) + (countLit q [-8, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7]) (l₂ := [-8, -10, -12])
  have hm := merge_right (literal (valuationOf q) (1249)) (literal (valuationOf q) (1252)) (countLit q [-2, -6, -7]) (countLit q [-8, -10, -12]) (count1251 q) 2 (meaning1249 q) (meaning1252 q) hs
  change valuationOf q 1249 = false ∨ valuationOf q 1252 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause405 (q : Snake 81) (h : Conditions q) : valuation q 1249 = false ∨ valuation q 1252 = true := counterClause405 (baseVal q)

theorem counterClause406 (q : Nat → Bool) : valuationOf q 1250 = false ∨ valuationOf q 1253 = true := by
  have hs : count1251 q = (countLit q [-2, -6, -7]) + (countLit q [-8, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7]) (l₂ := [-8, -10, -12])
  have hm := merge_right (literal (valuationOf q) (1250)) (literal (valuationOf q) (1253)) (countLit q [-2, -6, -7]) (countLit q [-8, -10, -12]) (count1251 q) 3 (meaning1250 q) (meaning1253 q) hs
  change valuationOf q 1250 = false ∨ valuationOf q 1253 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause406 (q : Snake 81) (h : Conditions q) : valuation q 1250 = false ∨ valuation q 1253 = true := counterClause406 (baseVal q)

theorem counterClause407 (q : Nat → Bool) : valuationOf q 1243 = false ∨ valuationOf q 1251 = true := by
  have hs : count1251 q = (countLit q [-2, -6, -7]) + (countLit q [-8, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7]) (l₂ := [-8, -10, -12])
  have hm := merge_left (literal (valuationOf q) (1243)) (literal (valuationOf q) (1251)) (countLit q [-2, -6, -7]) (countLit q [-8, -10, -12]) (count1251 q) 1 (meaning1243 q) (meaning1251 q) hs
  change valuationOf q 1243 = false ∨ valuationOf q 1251 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause407 (q : Snake 81) (h : Conditions q) : valuation q 1243 = false ∨ valuation q 1251 = true := counterClause407 (baseVal q)

theorem counterClause408 (q : Nat → Bool) : valuationOf q 1243 = false ∨ valuationOf q 1248 = false ∨ valuationOf q 1252 = true := by
  have hs : count1251 q = (countLit q [-2, -6, -7]) + (countLit q [-8, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7]) (l₂ := [-8, -10, -12])
  have hm := merge_two (literal (valuationOf q) (1243)) (literal (valuationOf q) (1248)) (literal (valuationOf q) (1252)) (countLit q [-2, -6, -7]) (countLit q [-8, -10, -12]) (count1251 q) 1 1 (meaning1243 q) (meaning1248 q) (meaning1252 q) hs
  change valuationOf q 1243 = false ∨ valuationOf q 1248 = false ∨ valuationOf q 1252 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause408 (q : Snake 81) (h : Conditions q) : valuation q 1243 = false ∨ valuation q 1248 = false ∨ valuation q 1252 = true := counterClause408 (baseVal q)

theorem counterClause409 (q : Nat → Bool) : valuationOf q 1243 = false ∨ valuationOf q 1249 = false ∨ valuationOf q 1253 = true := by
  have hs : count1251 q = (countLit q [-2, -6, -7]) + (countLit q [-8, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7]) (l₂ := [-8, -10, -12])
  have hm := merge_two (literal (valuationOf q) (1243)) (literal (valuationOf q) (1249)) (literal (valuationOf q) (1253)) (countLit q [-2, -6, -7]) (countLit q [-8, -10, -12]) (count1251 q) 1 2 (meaning1243 q) (meaning1249 q) (meaning1253 q) hs
  change valuationOf q 1243 = false ∨ valuationOf q 1249 = false ∨ valuationOf q 1253 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause409 (q : Snake 81) (h : Conditions q) : valuation q 1243 = false ∨ valuation q 1249 = false ∨ valuation q 1253 = true := counterClause409 (baseVal q)

theorem counterClause410 (q : Nat → Bool) : valuationOf q 1244 = false ∨ valuationOf q 1252 = true := by
  have hs : count1251 q = (countLit q [-2, -6, -7]) + (countLit q [-8, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7]) (l₂ := [-8, -10, -12])
  have hm := merge_left (literal (valuationOf q) (1244)) (literal (valuationOf q) (1252)) (countLit q [-2, -6, -7]) (countLit q [-8, -10, -12]) (count1251 q) 2 (meaning1244 q) (meaning1252 q) hs
  change valuationOf q 1244 = false ∨ valuationOf q 1252 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause410 (q : Snake 81) (h : Conditions q) : valuation q 1244 = false ∨ valuation q 1252 = true := counterClause410 (baseVal q)

theorem counterClause411 (q : Nat → Bool) : valuationOf q 1244 = false ∨ valuationOf q 1248 = false ∨ valuationOf q 1253 = true := by
  have hs : count1251 q = (countLit q [-2, -6, -7]) + (countLit q [-8, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7]) (l₂ := [-8, -10, -12])
  have hm := merge_two (literal (valuationOf q) (1244)) (literal (valuationOf q) (1248)) (literal (valuationOf q) (1253)) (countLit q [-2, -6, -7]) (countLit q [-8, -10, -12]) (count1251 q) 2 1 (meaning1244 q) (meaning1248 q) (meaning1253 q) hs
  change valuationOf q 1244 = false ∨ valuationOf q 1248 = false ∨ valuationOf q 1253 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause411 (q : Snake 81) (h : Conditions q) : valuation q 1244 = false ∨ valuation q 1248 = false ∨ valuation q 1253 = true := counterClause411 (baseVal q)

theorem counterClause412 (q : Nat → Bool) : valuationOf q 1244 = false ∨ valuationOf q 1249 = false ∨ valuationOf q 1254 = true := by
  have hs : count1251 q = (countLit q [-2, -6, -7]) + (countLit q [-8, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7]) (l₂ := [-8, -10, -12])
  have hm := merge_two (literal (valuationOf q) (1244)) (literal (valuationOf q) (1249)) (literal (valuationOf q) (1254)) (countLit q [-2, -6, -7]) (countLit q [-8, -10, -12]) (count1251 q) 2 2 (meaning1244 q) (meaning1249 q) (meaning1254 q) hs
  change valuationOf q 1244 = false ∨ valuationOf q 1249 = false ∨ valuationOf q 1254 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause412 (q : Snake 81) (h : Conditions q) : valuation q 1244 = false ∨ valuation q 1249 = false ∨ valuation q 1254 = true := counterClause412 (baseVal q)

theorem counterClause413 (q : Nat → Bool) : valuationOf q 1245 = false ∨ valuationOf q 1253 = true := by
  have hs : count1251 q = (countLit q [-2, -6, -7]) + (countLit q [-8, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7]) (l₂ := [-8, -10, -12])
  have hm := merge_left (literal (valuationOf q) (1245)) (literal (valuationOf q) (1253)) (countLit q [-2, -6, -7]) (countLit q [-8, -10, -12]) (count1251 q) 3 (meaning1245 q) (meaning1253 q) hs
  change valuationOf q 1245 = false ∨ valuationOf q 1253 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause413 (q : Snake 81) (h : Conditions q) : valuation q 1245 = false ∨ valuation q 1253 = true := counterClause413 (baseVal q)

theorem counterClause414 (q : Nat → Bool) : valuationOf q 1245 = false ∨ valuationOf q 1248 = false ∨ valuationOf q 1254 = true := by
  have hs : count1251 q = (countLit q [-2, -6, -7]) + (countLit q [-8, -10, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7]) (l₂ := [-8, -10, -12])
  have hm := merge_two (literal (valuationOf q) (1245)) (literal (valuationOf q) (1248)) (literal (valuationOf q) (1254)) (countLit q [-2, -6, -7]) (countLit q [-8, -10, -12]) (count1251 q) 3 1 (meaning1245 q) (meaning1248 q) (meaning1254 q) hs
  change valuationOf q 1245 = false ∨ valuationOf q 1248 = false ∨ valuationOf q 1254 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause414 (q : Snake 81) (h : Conditions q) : valuation q 1245 = false ∨ valuation q 1248 = false ∨ valuation q 1254 = true := counterClause414 (baseVal q)

theorem counterClause415 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 1257 = true := by
  have hs : count1257 q = (countLit q [-17]) + (countLit q [-20]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-20])
  have hm := merge_right (literal (valuationOf q) (-20)) (literal (valuationOf q) (1257)) (countLit q [-17]) (countLit q [-20]) (count1257 q) 1 (meaningNeg20 q) (meaning1257 q) hs
  change (! (valuationOf q 20)) = false ∨ valuationOf q 1257 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause415 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 1257 = true := counterClause415 (baseVal q)

theorem counterClause416 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 1257 = true := by
  have hs : count1257 q = (countLit q [-17]) + (countLit q [-20]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-20])
  have hm := merge_left (literal (valuationOf q) (-17)) (literal (valuationOf q) (1257)) (countLit q [-17]) (countLit q [-20]) (count1257 q) 1 (meaningNeg17 q) (meaning1257 q) hs
  change (! (valuationOf q 17)) = false ∨ valuationOf q 1257 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause416 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 1257 = true := counterClause416 (baseVal q)

theorem block12 (q : Snake 81) (h : Conditions q) : B112E179.Block12 (valuation q) :=
  ⟨clause385 q h, clause386 q h, clause387 q h, clause388 q h, clause389 q h, clause390 q h, clause391 q h, clause392 q h, clause393 q h, clause394 q h, clause395 q h, clause396 q h, clause397 q h, clause398 q h, clause399 q h, clause400 q h, clause401 q h, clause402 q h, clause403 q h, clause404 q h, clause405 q h, clause406 q h, clause407 q h, clause408 q h, clause409 q h, clause410 q h, clause411 q h, clause412 q h, clause413 q h, clause414 q h, clause415 q h, clause416 q h⟩

end
end Snake9.Regrowth.E112179
