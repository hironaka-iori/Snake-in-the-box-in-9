import E112168Semantics
import B112E168Inputs
namespace Snake9.Regrowth.E112168
noncomputable section
local instance blockDec21 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause673 (q : Nat → Bool) : valuationOf q 392 = false ∨ valuationOf q 450 = true := by
  have hs : count449 q = (countLit q [171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199]) + (countLit q [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) := List.countP_append (p := literal q) (l₁ := [171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199]) (l₂ := [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228])
  have hm := merge_left (literal (valuationOf q) (392)) (literal (valuationOf q) (450)) (countLit q [171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199]) (countLit q [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) (count449 q) 2 (meaning392 q) (meaning450 q) hs
  change valuationOf q 392 = false ∨ valuationOf q 450 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause673 (q : Snake 81) (h : Conditions q) : valuation q 392 = false ∨ valuation q 450 = true := counterClause673 (baseVal q)

theorem counterClause674 (q : Nat → Bool) : valuationOf q 450 = false ∨ valuationOf q 452 = true := by
  have hs : count451 q = (countLit q [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) + (countLit q [171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) := List.countP_append (p := literal q) (l₁ := [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) (l₂ := [171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228])
  have hm := merge_right (literal (valuationOf q) (450)) (literal (valuationOf q) (452)) (countLit q [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) (countLit q [171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) (count451 q) 2 (meaning450 q) (meaning452 q) hs
  change valuationOf q 450 = false ∨ valuationOf q 452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause674 (q : Snake 81) (h : Conditions q) : valuation q 450 = false ∨ valuation q 452 = true := counterClause674 (baseVal q)

theorem counterClause675 (q : Nat → Bool) : valuationOf q 337 = false ∨ valuationOf q 449 = false ∨ valuationOf q 452 = true := by
  have hs : count451 q = (countLit q [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) + (countLit q [171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) := List.countP_append (p := literal q) (l₁ := [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) (l₂ := [171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228])
  have hm := merge_two (literal (valuationOf q) (337)) (literal (valuationOf q) (449)) (literal (valuationOf q) (452)) (countLit q [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) (countLit q [171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) (count451 q) 1 1 (meaning337 q) (meaning449 q) (meaning452 q) hs
  change valuationOf q 337 = false ∨ valuationOf q 449 = false ∨ valuationOf q 452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause675 (q : Snake 81) (h : Conditions q) : valuation q 337 = false ∨ valuation q 449 = false ∨ valuation q 452 = true := counterClause675 (baseVal q)

theorem counterClause676 (q : Nat → Bool) : valuationOf q 338 = false ∨ valuationOf q 452 = true := by
  have hs : count451 q = (countLit q [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) + (countLit q [171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) := List.countP_append (p := literal q) (l₁ := [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) (l₂ := [171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228])
  have hm := merge_left (literal (valuationOf q) (338)) (literal (valuationOf q) (452)) (countLit q [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) (countLit q [171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) (count451 q) 2 (meaning338 q) (meaning452 q) hs
  change valuationOf q 338 = false ∨ valuationOf q 452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause676 (q : Snake 81) (h : Conditions q) : valuation q 338 = false ∨ valuation q 452 = true := counterClause676 (baseVal q)

theorem clause677 (q : Snake 81) (h : Conditions q) : valuation q 452 = false := by
  rw [value452]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count451 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem clause678 (q : Snake 81) (h : Conditions q) : valuation q 115 = true ∨ valuation q 116 = true ∨ valuation q 117 = true ∨ valuation q 118 = true ∨ valuation q 119 = true ∨ valuation q 120 = true ∨ valuation q 121 = true ∨ valuation q 122 = true ∨ valuation q 123 = true ∨ valuation q 124 = true ∨ valuation q 125 = true ∨ valuation q 126 = true ∨ valuation q 127 = true ∨ valuation q 128 = true ∨ valuation q 129 = true ∨ valuation q 130 = true ∨ valuation q 131 = true ∨ valuation q 132 = true ∨ valuation q 133 = true ∨ valuation q 134 = true ∨ valuation q 135 = true ∨ valuation q 136 = true ∨ valuation q 137 = true ∨ valuation q 138 = true ∨ valuation q 139 = true ∨ valuation q 140 = true ∨ valuation q 141 = true ∨ valuation q 142 = true ∨ valuation q 143 = true ∨ valuation q 144 = true ∨ valuation q 145 = true ∨ valuation q 146 = true ∨ valuation q 147 = true ∨ valuation q 148 = true ∨ valuation q 149 = true ∨ valuation q 150 = true ∨ valuation q 151 = true ∨ valuation q 152 = true ∨ valuation q 153 = true ∨ valuation q 154 = true ∨ valuation q 155 = true ∨ valuation q 156 = true ∨ valuation q 157 = true ∨ valuation q 158 = true ∨ valuation q 159 = true ∨ valuation q 160 = true ∨ valuation q 161 = true ∨ valuation q 162 = true ∨ valuation q 163 = true ∨ valuation q 164 = true ∨ valuation q 165 = true ∨ valuation q 166 = true ∨ valuation q 167 = true ∨ valuation q 168 = true ∨ valuation q 169 = true ∨ valuation q 170 = true ∨ valuation q 171 = true ∨ valuation q 172 = true ∨ valuation q 173 = true ∨ valuation q 174 = true ∨ valuation q 175 = true ∨ valuation q 176 = true ∨ valuation q 177 = true ∨ valuation q 178 = true ∨ valuation q 179 = true ∨ valuation q 180 = true ∨ valuation q 181 = true ∨ valuation q 182 = true ∨ valuation q 184 = true ∨ valuation q 185 = true ∨ valuation q 186 = true ∨ valuation q 187 = true ∨ valuation q 188 = true ∨ valuation q 189 = true ∨ valuation q 190 = true ∨ valuation q 191 = true ∨ valuation q 192 = true ∨ valuation q 193 = true ∨ valuation q 194 = true ∨ valuation q 195 = true ∨ valuation q 196 = true ∨ valuation q 197 = true ∨ valuation q 198 = true ∨ valuation q 199 = true ∨ valuation q 200 = true ∨ valuation q 201 = true ∨ valuation q 202 = true ∨ valuation q 203 = true ∨ valuation q 204 = true ∨ valuation q 205 = true ∨ valuation q 206 = true ∨ valuation q 207 = true ∨ valuation q 208 = true ∨ valuation q 209 = true ∨ valuation q 210 = true ∨ valuation q 211 = true ∨ valuation q 212 = true ∨ valuation q 213 = true ∨ valuation q 214 = true ∨ valuation q 215 = true ∨ valuation q 216 = true ∨ valuation q 217 = true ∨ valuation q 218 = true ∨ valuation q 219 = true ∨ valuation q 220 = true ∨ valuation q 221 = true ∨ valuation q 222 = true ∨ valuation q 223 = true ∨ valuation q 224 = true ∨ valuation q 225 = true ∨ valuation q 226 = true ∨ valuation q 227 = true ∨ valuation q 228 = true := by
  rw [value115, value116, value117, value118, value119, value120, value121, value122, value123, value124, value125, value126, value127, value128, value129, value130, value131, value132, value133, value134, value135, value136, value137, value138, value139, value140, value141, value142, value143, value144, value145, value146, value147, value148, value149, value150, value151, value152, value153, value154, value155, value156, value157, value158, value159, value160, value161, value162, value163, value164, value165, value166, value167, value168, value169, value170, value171, value172, value173, value174, value175, value176, value177, value178, value179, value180, value181, value182, value184, value185, value186, value187, value188, value189, value190, value191, value192, value193, value194, value195, value196, value197, value198, value199, value200, value201, value202, value203, value204, value205, value206, value207, value208, value209, value210, value211, value212, value213, value214, value215, value216, value217, value218, value219, value220, value221, value222, value223, value224, value225, value226, value227, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hg := other_endpoint q others (fun v hv hn => others_mem v (h.covered v hv) (by simpa only [h.head_fixed] using hn))
  simpa only [others, List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem counterClause679 (q : Nat → Bool) : valuationOf q 5 = true ∨ valuationOf q 1373 = true := by
  have hs : count1373 q = (countLit q [-3]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-5])
  have hm := merge_right (literal (valuationOf q) (-5)) (literal (valuationOf q) (1373)) (countLit q [-3]) (countLit q [-5]) (count1373 q) 1 (meaningNeg5 q) (meaning1373 q) hs
  change (! (valuationOf q 5)) = false ∨ valuationOf q 1373 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause679 (q : Snake 81) (h : Conditions q) : valuation q 5 = true ∨ valuation q 1373 = true := counterClause679 (baseVal q)

theorem counterClause680 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 1373 = true := by
  have hs : count1373 q = (countLit q [-3]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-5])
  have hm := merge_left (literal (valuationOf q) (-3)) (literal (valuationOf q) (1373)) (countLit q [-3]) (countLit q [-5]) (count1373 q) 1 (meaningNeg3 q) (meaning1373 q) hs
  change (! (valuationOf q 3)) = false ∨ valuationOf q 1373 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause680 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 1373 = true := counterClause680 (baseVal q)

theorem counterClause681 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 5 = true ∨ valuationOf q 1374 = true := by
  have hs : count1373 q = (countLit q [-3]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-5])
  have hm := merge_two (literal (valuationOf q) (-3)) (literal (valuationOf q) (-5)) (literal (valuationOf q) (1374)) (countLit q [-3]) (countLit q [-5]) (count1373 q) 1 1 (meaningNeg3 q) (meaningNeg5 q) (meaning1374 q) hs
  change (! (valuationOf q 3)) = false ∨ (! (valuationOf q 5)) = false ∨ valuationOf q 1374 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause681 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 5 = true ∨ valuation q 1374 = true := counterClause681 (baseVal q)

theorem counterClause682 (q : Nat → Bool) : valuationOf q 1374 = false ∨ valuationOf q 1376 = true := by
  have hs : count1375 q = (countLit q [-2]) + (countLit q [-3, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3, -5])
  have hm := merge_right (literal (valuationOf q) (1374)) (literal (valuationOf q) (1376)) (countLit q [-2]) (countLit q [-3, -5]) (count1375 q) 2 (meaning1374 q) (meaning1376 q) hs
  change valuationOf q 1374 = false ∨ valuationOf q 1376 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause682 (q : Snake 81) (h : Conditions q) : valuation q 1374 = false ∨ valuation q 1376 = true := counterClause682 (baseVal q)

theorem counterClause683 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1375 = true := by
  have hs : count1375 q = (countLit q [-2]) + (countLit q [-3, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3, -5])
  have hm := merge_left (literal (valuationOf q) (-2)) (literal (valuationOf q) (1375)) (countLit q [-2]) (countLit q [-3, -5]) (count1375 q) 1 (meaningNeg2 q) (meaning1375 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1375 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause683 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1375 = true := counterClause683 (baseVal q)

theorem counterClause684 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1373 = false ∨ valuationOf q 1376 = true := by
  have hs : count1375 q = (countLit q [-2]) + (countLit q [-3, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3, -5])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (1373)) (literal (valuationOf q) (1376)) (countLit q [-2]) (countLit q [-3, -5]) (count1375 q) 1 1 (meaningNeg2 q) (meaning1373 q) (meaning1376 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1373 = false ∨ valuationOf q 1376 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause684 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1373 = false ∨ valuation q 1376 = true := counterClause684 (baseVal q)

theorem counterClause685 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1374 = false ∨ valuationOf q 1377 = true := by
  have hs : count1375 q = (countLit q [-2]) + (countLit q [-3, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3, -5])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (1374)) (literal (valuationOf q) (1377)) (countLit q [-2]) (countLit q [-3, -5]) (count1375 q) 1 2 (meaningNeg2 q) (meaning1374 q) (meaning1377 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1374 = false ∨ valuationOf q 1377 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause685 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1374 = false ∨ valuation q 1377 = true := counterClause685 (baseVal q)

theorem counterClause686 (q : Nat → Bool) : valuationOf q 10 = true ∨ valuationOf q 1378 = true := by
  have hs : count1378 q = (countLit q [-8]) + (countLit q [-10]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-10])
  have hm := merge_right (literal (valuationOf q) (-10)) (literal (valuationOf q) (1378)) (countLit q [-8]) (countLit q [-10]) (count1378 q) 1 (meaningNeg10 q) (meaning1378 q) hs
  change (! (valuationOf q 10)) = false ∨ valuationOf q 1378 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause686 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 1378 = true := counterClause686 (baseVal q)

theorem counterClause687 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 1378 = true := by
  have hs : count1378 q = (countLit q [-8]) + (countLit q [-10]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-10])
  have hm := merge_left (literal (valuationOf q) (-8)) (literal (valuationOf q) (1378)) (countLit q [-8]) (countLit q [-10]) (count1378 q) 1 (meaningNeg8 q) (meaning1378 q) hs
  change (! (valuationOf q 8)) = false ∨ valuationOf q 1378 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause687 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 1378 = true := counterClause687 (baseVal q)

theorem counterClause688 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 10 = true ∨ valuationOf q 1379 = true := by
  have hs : count1378 q = (countLit q [-8]) + (countLit q [-10]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-10])
  have hm := merge_two (literal (valuationOf q) (-8)) (literal (valuationOf q) (-10)) (literal (valuationOf q) (1379)) (countLit q [-8]) (countLit q [-10]) (count1378 q) 1 1 (meaningNeg8 q) (meaningNeg10 q) (meaning1379 q) hs
  change (! (valuationOf q 8)) = false ∨ (! (valuationOf q 10)) = false ∨ valuationOf q 1379 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause688 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 10 = true ∨ valuation q 1379 = true := counterClause688 (baseVal q)

theorem counterClause689 (q : Nat → Bool) : valuationOf q 12 = true ∨ valuationOf q 1380 = true := by
  have hs : count1380 q = (countLit q [-11]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-12])
  have hm := merge_right (literal (valuationOf q) (-12)) (literal (valuationOf q) (1380)) (countLit q [-11]) (countLit q [-12]) (count1380 q) 1 (meaningNeg12 q) (meaning1380 q) hs
  change (! (valuationOf q 12)) = false ∨ valuationOf q 1380 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause689 (q : Snake 81) (h : Conditions q) : valuation q 12 = true ∨ valuation q 1380 = true := counterClause689 (baseVal q)

theorem counterClause690 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 1380 = true := by
  have hs : count1380 q = (countLit q [-11]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-12])
  have hm := merge_left (literal (valuationOf q) (-11)) (literal (valuationOf q) (1380)) (countLit q [-11]) (countLit q [-12]) (count1380 q) 1 (meaningNeg11 q) (meaning1380 q) hs
  change (! (valuationOf q 11)) = false ∨ valuationOf q 1380 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause690 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 1380 = true := counterClause690 (baseVal q)

theorem counterClause691 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 12 = true ∨ valuationOf q 1381 = true := by
  have hs : count1380 q = (countLit q [-11]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-12])
  have hm := merge_two (literal (valuationOf q) (-11)) (literal (valuationOf q) (-12)) (literal (valuationOf q) (1381)) (countLit q [-11]) (countLit q [-12]) (count1380 q) 1 1 (meaningNeg11 q) (meaningNeg12 q) (meaning1381 q) hs
  change (! (valuationOf q 11)) = false ∨ (! (valuationOf q 12)) = false ∨ valuationOf q 1381 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause691 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 12 = true ∨ valuation q 1381 = true := counterClause691 (baseVal q)

theorem counterClause692 (q : Nat → Bool) : valuationOf q 1380 = false ∨ valuationOf q 1382 = true := by
  have hs : count1382 q = (countLit q [-8, -10]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-8, -10]) (l₂ := [-11, -12])
  have hm := merge_right (literal (valuationOf q) (1380)) (literal (valuationOf q) (1382)) (countLit q [-8, -10]) (countLit q [-11, -12]) (count1382 q) 1 (meaning1380 q) (meaning1382 q) hs
  change valuationOf q 1380 = false ∨ valuationOf q 1382 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause692 (q : Snake 81) (h : Conditions q) : valuation q 1380 = false ∨ valuation q 1382 = true := counterClause692 (baseVal q)

theorem counterClause693 (q : Nat → Bool) : valuationOf q 1381 = false ∨ valuationOf q 1383 = true := by
  have hs : count1382 q = (countLit q [-8, -10]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-8, -10]) (l₂ := [-11, -12])
  have hm := merge_right (literal (valuationOf q) (1381)) (literal (valuationOf q) (1383)) (countLit q [-8, -10]) (countLit q [-11, -12]) (count1382 q) 2 (meaning1381 q) (meaning1383 q) hs
  change valuationOf q 1381 = false ∨ valuationOf q 1383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause693 (q : Snake 81) (h : Conditions q) : valuation q 1381 = false ∨ valuation q 1383 = true := counterClause693 (baseVal q)

theorem counterClause694 (q : Nat → Bool) : valuationOf q 1378 = false ∨ valuationOf q 1382 = true := by
  have hs : count1382 q = (countLit q [-8, -10]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-8, -10]) (l₂ := [-11, -12])
  have hm := merge_left (literal (valuationOf q) (1378)) (literal (valuationOf q) (1382)) (countLit q [-8, -10]) (countLit q [-11, -12]) (count1382 q) 1 (meaning1378 q) (meaning1382 q) hs
  change valuationOf q 1378 = false ∨ valuationOf q 1382 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause694 (q : Snake 81) (h : Conditions q) : valuation q 1378 = false ∨ valuation q 1382 = true := counterClause694 (baseVal q)

theorem counterClause695 (q : Nat → Bool) : valuationOf q 1378 = false ∨ valuationOf q 1380 = false ∨ valuationOf q 1383 = true := by
  have hs : count1382 q = (countLit q [-8, -10]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-8, -10]) (l₂ := [-11, -12])
  have hm := merge_two (literal (valuationOf q) (1378)) (literal (valuationOf q) (1380)) (literal (valuationOf q) (1383)) (countLit q [-8, -10]) (countLit q [-11, -12]) (count1382 q) 1 1 (meaning1378 q) (meaning1380 q) (meaning1383 q) hs
  change valuationOf q 1378 = false ∨ valuationOf q 1380 = false ∨ valuationOf q 1383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause695 (q : Snake 81) (h : Conditions q) : valuation q 1378 = false ∨ valuation q 1380 = false ∨ valuation q 1383 = true := counterClause695 (baseVal q)

theorem counterClause696 (q : Nat → Bool) : valuationOf q 1378 = false ∨ valuationOf q 1381 = false ∨ valuationOf q 1384 = true := by
  have hs : count1382 q = (countLit q [-8, -10]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-8, -10]) (l₂ := [-11, -12])
  have hm := merge_two (literal (valuationOf q) (1378)) (literal (valuationOf q) (1381)) (literal (valuationOf q) (1384)) (countLit q [-8, -10]) (countLit q [-11, -12]) (count1382 q) 1 2 (meaning1378 q) (meaning1381 q) (meaning1384 q) hs
  change valuationOf q 1378 = false ∨ valuationOf q 1381 = false ∨ valuationOf q 1384 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause696 (q : Snake 81) (h : Conditions q) : valuation q 1378 = false ∨ valuation q 1381 = false ∨ valuation q 1384 = true := counterClause696 (baseVal q)

theorem counterClause697 (q : Nat → Bool) : valuationOf q 1379 = false ∨ valuationOf q 1383 = true := by
  have hs : count1382 q = (countLit q [-8, -10]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-8, -10]) (l₂ := [-11, -12])
  have hm := merge_left (literal (valuationOf q) (1379)) (literal (valuationOf q) (1383)) (countLit q [-8, -10]) (countLit q [-11, -12]) (count1382 q) 2 (meaning1379 q) (meaning1383 q) hs
  change valuationOf q 1379 = false ∨ valuationOf q 1383 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause697 (q : Snake 81) (h : Conditions q) : valuation q 1379 = false ∨ valuation q 1383 = true := counterClause697 (baseVal q)

theorem counterClause698 (q : Nat → Bool) : valuationOf q 1379 = false ∨ valuationOf q 1380 = false ∨ valuationOf q 1384 = true := by
  have hs : count1382 q = (countLit q [-8, -10]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-8, -10]) (l₂ := [-11, -12])
  have hm := merge_two (literal (valuationOf q) (1379)) (literal (valuationOf q) (1380)) (literal (valuationOf q) (1384)) (countLit q [-8, -10]) (countLit q [-11, -12]) (count1382 q) 2 1 (meaning1379 q) (meaning1380 q) (meaning1384 q) hs
  change valuationOf q 1379 = false ∨ valuationOf q 1380 = false ∨ valuationOf q 1384 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause698 (q : Snake 81) (h : Conditions q) : valuation q 1379 = false ∨ valuation q 1380 = false ∨ valuation q 1384 = true := counterClause698 (baseVal q)

theorem counterClause699 (q : Nat → Bool) : valuationOf q 1379 = false ∨ valuationOf q 1381 = false ∨ valuationOf q 1385 = true := by
  have hs : count1382 q = (countLit q [-8, -10]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-8, -10]) (l₂ := [-11, -12])
  have hm := merge_two (literal (valuationOf q) (1379)) (literal (valuationOf q) (1381)) (literal (valuationOf q) (1385)) (countLit q [-8, -10]) (countLit q [-11, -12]) (count1382 q) 2 2 (meaning1379 q) (meaning1381 q) (meaning1385 q) hs
  change valuationOf q 1379 = false ∨ valuationOf q 1381 = false ∨ valuationOf q 1385 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause699 (q : Snake 81) (h : Conditions q) : valuation q 1379 = false ∨ valuation q 1381 = false ∨ valuation q 1385 = true := counterClause699 (baseVal q)

theorem counterClause700 (q : Nat → Bool) : valuationOf q 1375 = false ∨ valuationOf q 1386 = true := by
  have hs : count1386 q = (countLit q [-2, -3, -5]) + (countLit q [-8, -10, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-8, -10, -11, -12])
  have hm := merge_left (literal (valuationOf q) (1375)) (literal (valuationOf q) (1386)) (countLit q [-2, -3, -5]) (countLit q [-8, -10, -11, -12]) (count1386 q) 1 (meaning1375 q) (meaning1386 q) hs
  change valuationOf q 1375 = false ∨ valuationOf q 1386 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause700 (q : Snake 81) (h : Conditions q) : valuation q 1375 = false ∨ valuation q 1386 = true := counterClause700 (baseVal q)

theorem counterClause701 (q : Nat → Bool) : valuationOf q 1375 = false ∨ valuationOf q 1382 = false ∨ valuationOf q 1387 = true := by
  have hs : count1386 q = (countLit q [-2, -3, -5]) + (countLit q [-8, -10, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-8, -10, -11, -12])
  have hm := merge_two (literal (valuationOf q) (1375)) (literal (valuationOf q) (1382)) (literal (valuationOf q) (1387)) (countLit q [-2, -3, -5]) (countLit q [-8, -10, -11, -12]) (count1386 q) 1 1 (meaning1375 q) (meaning1382 q) (meaning1387 q) hs
  change valuationOf q 1375 = false ∨ valuationOf q 1382 = false ∨ valuationOf q 1387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause701 (q : Snake 81) (h : Conditions q) : valuation q 1375 = false ∨ valuation q 1382 = false ∨ valuation q 1387 = true := counterClause701 (baseVal q)

theorem counterClause702 (q : Nat → Bool) : valuationOf q 1375 = false ∨ valuationOf q 1383 = false ∨ valuationOf q 1388 = true := by
  have hs : count1386 q = (countLit q [-2, -3, -5]) + (countLit q [-8, -10, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-8, -10, -11, -12])
  have hm := merge_two (literal (valuationOf q) (1375)) (literal (valuationOf q) (1383)) (literal (valuationOf q) (1388)) (countLit q [-2, -3, -5]) (countLit q [-8, -10, -11, -12]) (count1386 q) 1 2 (meaning1375 q) (meaning1383 q) (meaning1388 q) hs
  change valuationOf q 1375 = false ∨ valuationOf q 1383 = false ∨ valuationOf q 1388 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause702 (q : Snake 81) (h : Conditions q) : valuation q 1375 = false ∨ valuation q 1383 = false ∨ valuation q 1388 = true := counterClause702 (baseVal q)

theorem counterClause703 (q : Nat → Bool) : valuationOf q 1375 = false ∨ valuationOf q 1384 = false ∨ valuationOf q 1389 = true := by
  have hs : count1386 q = (countLit q [-2, -3, -5]) + (countLit q [-8, -10, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-8, -10, -11, -12])
  have hm := merge_two (literal (valuationOf q) (1375)) (literal (valuationOf q) (1384)) (literal (valuationOf q) (1389)) (countLit q [-2, -3, -5]) (countLit q [-8, -10, -11, -12]) (count1386 q) 1 3 (meaning1375 q) (meaning1384 q) (meaning1389 q) hs
  change valuationOf q 1375 = false ∨ valuationOf q 1384 = false ∨ valuationOf q 1389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause703 (q : Snake 81) (h : Conditions q) : valuation q 1375 = false ∨ valuation q 1384 = false ∨ valuation q 1389 = true := counterClause703 (baseVal q)

theorem counterClause704 (q : Nat → Bool) : valuationOf q 1375 = false ∨ valuationOf q 1385 = false ∨ valuationOf q 1390 = true := by
  have hs : count1386 q = (countLit q [-2, -3, -5]) + (countLit q [-8, -10, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-8, -10, -11, -12])
  have hm := merge_two (literal (valuationOf q) (1375)) (literal (valuationOf q) (1385)) (literal (valuationOf q) (1390)) (countLit q [-2, -3, -5]) (countLit q [-8, -10, -11, -12]) (count1386 q) 1 4 (meaning1375 q) (meaning1385 q) (meaning1390 q) hs
  change valuationOf q 1375 = false ∨ valuationOf q 1385 = false ∨ valuationOf q 1390 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause704 (q : Snake 81) (h : Conditions q) : valuation q 1375 = false ∨ valuation q 1385 = false ∨ valuation q 1390 = true := counterClause704 (baseVal q)

theorem block21 (q : Snake 81) (h : Conditions q) : B112E168.Block21 (valuation q) :=
  ⟨clause673 q h, clause674 q h, clause675 q h, clause676 q h, clause677 q h, clause678 q h, clause679 q h, clause680 q h, clause681 q h, clause682 q h, clause683 q h, clause684 q h, clause685 q h, clause686 q h, clause687 q h, clause688 q h, clause689 q h, clause690 q h, clause691 q h, clause692 q h, clause693 q h, clause694 q h, clause695 q h, clause696 q h, clause697 q h, clause698 q h, clause699 q h, clause700 q h, clause701 q h, clause702 q h, clause703 q h, clause704 q h⟩

end
end Snake9.Regrowth.E112168
