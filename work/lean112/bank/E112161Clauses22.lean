import E112161Semantics
import B112E161Inputs
namespace Snake9.Regrowth.E112161
noncomputable section
local instance blockDec22 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause705 (q : Nat → Bool) : valuationOf q 329 = false ∨ valuationOf q 437 = false ∨ valuationOf q 440 = true := by
  have hs : count439 q = (countLit q [112, 113, 114, 115, 116, 117, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167]) + (countLit q [168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [112, 113, 114, 115, 116, 117, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167]) (l₂ := [168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222])
  have hm := merge_two (literal (valuationOf q) (329)) (literal (valuationOf q) (437)) (literal (valuationOf q) (440)) (countLit q [112, 113, 114, 115, 116, 117, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167]) (countLit q [168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (count439 q) 1 1 (meaning329 q) (meaning437 q) (meaning440 q) hs
  change valuationOf q 329 = false ∨ valuationOf q 437 = false ∨ valuationOf q 440 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause705 (q : Snake 81) (h : Conditions q) : valuation q 329 = false ∨ valuation q 437 = false ∨ valuation q 440 = true := counterClause705 (baseVal q)

theorem counterClause706 (q : Nat → Bool) : valuationOf q 330 = false ∨ valuationOf q 440 = true := by
  have hs : count439 q = (countLit q [112, 113, 114, 115, 116, 117, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167]) + (countLit q [168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) := List.countP_append (p := literal q) (l₁ := [112, 113, 114, 115, 116, 117, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167]) (l₂ := [168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222])
  have hm := merge_left (literal (valuationOf q) (330)) (literal (valuationOf q) (440)) (countLit q [112, 113, 114, 115, 116, 117, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167]) (countLit q [168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]) (count439 q) 2 (meaning330 q) (meaning440 q) hs
  change valuationOf q 330 = false ∨ valuationOf q 440 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause706 (q : Snake 81) (h : Conditions q) : valuation q 330 = false ∨ valuation q 440 = true := counterClause706 (baseVal q)

theorem clause707 (q : Snake 81) (h : Conditions q) : valuation q 440 = false := by
  rw [value440]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count439 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem clause708 (q : Snake 81) (h : Conditions q) : valuation q 112 = true ∨ valuation q 113 = true ∨ valuation q 114 = true ∨ valuation q 115 = true ∨ valuation q 116 = true ∨ valuation q 117 = true ∨ valuation q 119 = true ∨ valuation q 120 = true ∨ valuation q 121 = true ∨ valuation q 122 = true ∨ valuation q 123 = true ∨ valuation q 124 = true ∨ valuation q 125 = true ∨ valuation q 126 = true ∨ valuation q 127 = true ∨ valuation q 128 = true ∨ valuation q 129 = true ∨ valuation q 130 = true ∨ valuation q 131 = true ∨ valuation q 132 = true ∨ valuation q 133 = true ∨ valuation q 134 = true ∨ valuation q 135 = true ∨ valuation q 136 = true ∨ valuation q 137 = true ∨ valuation q 138 = true ∨ valuation q 139 = true ∨ valuation q 140 = true ∨ valuation q 141 = true ∨ valuation q 142 = true ∨ valuation q 143 = true ∨ valuation q 144 = true ∨ valuation q 145 = true ∨ valuation q 146 = true ∨ valuation q 147 = true ∨ valuation q 148 = true ∨ valuation q 149 = true ∨ valuation q 150 = true ∨ valuation q 151 = true ∨ valuation q 152 = true ∨ valuation q 153 = true ∨ valuation q 154 = true ∨ valuation q 155 = true ∨ valuation q 156 = true ∨ valuation q 157 = true ∨ valuation q 158 = true ∨ valuation q 159 = true ∨ valuation q 160 = true ∨ valuation q 161 = true ∨ valuation q 162 = true ∨ valuation q 163 = true ∨ valuation q 164 = true ∨ valuation q 165 = true ∨ valuation q 166 = true ∨ valuation q 167 = true ∨ valuation q 168 = true ∨ valuation q 169 = true ∨ valuation q 170 = true ∨ valuation q 171 = true ∨ valuation q 172 = true ∨ valuation q 173 = true ∨ valuation q 174 = true ∨ valuation q 175 = true ∨ valuation q 176 = true ∨ valuation q 177 = true ∨ valuation q 178 = true ∨ valuation q 179 = true ∨ valuation q 180 = true ∨ valuation q 181 = true ∨ valuation q 182 = true ∨ valuation q 183 = true ∨ valuation q 184 = true ∨ valuation q 185 = true ∨ valuation q 186 = true ∨ valuation q 187 = true ∨ valuation q 188 = true ∨ valuation q 189 = true ∨ valuation q 190 = true ∨ valuation q 191 = true ∨ valuation q 192 = true ∨ valuation q 193 = true ∨ valuation q 194 = true ∨ valuation q 195 = true ∨ valuation q 196 = true ∨ valuation q 197 = true ∨ valuation q 198 = true ∨ valuation q 199 = true ∨ valuation q 200 = true ∨ valuation q 201 = true ∨ valuation q 202 = true ∨ valuation q 203 = true ∨ valuation q 204 = true ∨ valuation q 205 = true ∨ valuation q 206 = true ∨ valuation q 207 = true ∨ valuation q 208 = true ∨ valuation q 209 = true ∨ valuation q 210 = true ∨ valuation q 211 = true ∨ valuation q 212 = true ∨ valuation q 213 = true ∨ valuation q 214 = true ∨ valuation q 215 = true ∨ valuation q 216 = true ∨ valuation q 217 = true ∨ valuation q 218 = true ∨ valuation q 219 = true ∨ valuation q 220 = true ∨ valuation q 221 = true ∨ valuation q 222 = true := by
  rw [value112, value113, value114, value115, value116, value117, value119, value120, value121, value122, value123, value124, value125, value126, value127, value128, value129, value130, value131, value132, value133, value134, value135, value136, value137, value138, value139, value140, value141, value142, value143, value144, value145, value146, value147, value148, value149, value150, value151, value152, value153, value154, value155, value156, value157, value158, value159, value160, value161, value162, value163, value164, value165, value166, value167, value168, value169, value170, value171, value172, value173, value174, value175, value176, value177, value178, value179, value180, value181, value182, value183, value184, value185, value186, value187, value188, value189, value190, value191, value192, value193, value194, value195, value196, value197, value198, value199, value200, value201, value202, value203, value204, value205, value206, value207, value208, value209, value210, value211, value212, value213, value214, value215, value216, value217, value218, value219, value220, value221, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hg := other_endpoint q others (fun v hv hn => others_mem v (h.covered v hv) (by simpa only [h.head_fixed] using hn))
  simpa only [others, List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem counterClause709 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 749 = true := by
  have hs : count749 q = (countLit q [-3]) + (countLit q [-4]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-4])
  have hm := merge_left (literal (valuationOf q) (-3)) (literal (valuationOf q) (749)) (countLit q [-3]) (countLit q [-4]) (count749 q) 1 (meaningNeg3 q) (meaning749 q) hs
  change (! (valuationOf q 3)) = false ∨ valuationOf q 749 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause709 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 749 = true := counterClause709 (baseVal q)

theorem counterClause710 (q : Nat → Bool) : valuationOf q 1 = true ∨ valuationOf q 749 = false ∨ valuationOf q 752 = true := by
  have hs : count751 q = (countLit q [-1]) + (countLit q [-3, -4]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-3, -4])
  have hm := merge_two (literal (valuationOf q) (-1)) (literal (valuationOf q) (749)) (literal (valuationOf q) (752)) (countLit q [-1]) (countLit q [-3, -4]) (count751 q) 1 1 (meaningNeg1 q) (meaning749 q) (meaning752 q) hs
  change (! (valuationOf q 1)) = false ∨ valuationOf q 749 = false ∨ valuationOf q 752 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause710 (q : Snake 81) (h : Conditions q) : valuation q 1 = true ∨ valuation q 749 = false ∨ valuation q 752 = true := counterClause710 (baseVal q)

theorem counterClause711 (q : Nat → Bool) : valuationOf q 752 = false ∨ valuationOf q 760 = true := by
  have hs : count759 q = (countLit q [-1, -3, -4]) + (countLit q [-5, -7, -9]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4]) (l₂ := [-5, -7, -9])
  have hm := merge_left (literal (valuationOf q) (752)) (literal (valuationOf q) (760)) (countLit q [-1, -3, -4]) (countLit q [-5, -7, -9]) (count759 q) 2 (meaning752 q) (meaning760 q) hs
  change valuationOf q 752 = false ∨ valuationOf q 760 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause711 (q : Snake 81) (h : Conditions q) : valuation q 752 = false ∨ valuation q 760 = true := counterClause711 (baseVal q)

theorem counterClause712 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 767 = true := by
  have hs : count767 q = (countLit q [-11]) + (countLit q [-13, -15]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-13, -15])
  have hm := merge_left (literal (valuationOf q) (-11)) (literal (valuationOf q) (767)) (countLit q [-11]) (countLit q [-13, -15]) (count767 q) 1 (meaningNeg11 q) (meaning767 q) hs
  change (! (valuationOf q 11)) = false ∨ valuationOf q 767 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause712 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 767 = true := counterClause712 (baseVal q)

theorem counterClause713 (q : Nat → Bool) : valuationOf q 23 = true ∨ valuationOf q 26 = true ∨ valuationOf q 773 = true := by
  have hs : count772 q = (countLit q [-23]) + (countLit q [-26]) := List.countP_append (p := literal q) (l₁ := [-23]) (l₂ := [-26])
  have hm := merge_two (literal (valuationOf q) (-23)) (literal (valuationOf q) (-26)) (literal (valuationOf q) (773)) (countLit q [-23]) (countLit q [-26]) (count772 q) 1 1 (meaningNeg23 q) (meaningNeg26 q) (meaning773 q) hs
  change (! (valuationOf q 23)) = false ∨ (! (valuationOf q 26)) = false ∨ valuationOf q 773 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause713 (q : Snake 81) (h : Conditions q) : valuation q 23 = true ∨ valuation q 26 = true ∨ valuation q 773 = true := counterClause713 (baseVal q)

theorem counterClause714 (q : Nat → Bool) : valuationOf q 773 = false ∨ valuationOf q 775 = true := by
  have hs : count774 q = (countLit q [-18, -20]) + (countLit q [-23, -26]) := List.countP_append (p := literal q) (l₁ := [-18, -20]) (l₂ := [-23, -26])
  have hm := merge_right (literal (valuationOf q) (773)) (literal (valuationOf q) (775)) (countLit q [-18, -20]) (countLit q [-23, -26]) (count774 q) 2 (meaning773 q) (meaning775 q) hs
  change valuationOf q 773 = false ∨ valuationOf q 775 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause714 (q : Snake 81) (h : Conditions q) : valuation q 773 = false ∨ valuation q 775 = true := counterClause714 (baseVal q)

theorem counterClause715 (q : Nat → Bool) : valuationOf q 767 = false ∨ valuationOf q 775 = false ∨ valuationOf q 780 = true := by
  have hs : count778 q = (countLit q [-11, -13, -15]) + (countLit q [-18, -20, -23, -26]) := List.countP_append (p := literal q) (l₁ := [-11, -13, -15]) (l₂ := [-18, -20, -23, -26])
  have hm := merge_two (literal (valuationOf q) (767)) (literal (valuationOf q) (775)) (literal (valuationOf q) (780)) (countLit q [-11, -13, -15]) (countLit q [-18, -20, -23, -26]) (count778 q) 1 2 (meaning767 q) (meaning775 q) (meaning780 q) hs
  change valuationOf q 767 = false ∨ valuationOf q 775 = false ∨ valuationOf q 780 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause715 (q : Snake 81) (h : Conditions q) : valuation q 767 = false ∨ valuation q 775 = false ∨ valuation q 780 = true := counterClause715 (baseVal q)

theorem counterClause716 (q : Nat → Bool) : valuationOf q 760 = false ∨ valuationOf q 780 = false ∨ valuationOf q 789 = true := by
  have hs : count785 q = (countLit q [-1, -3, -4, -5, -7, -9]) + (countLit q [-11, -13, -15, -18, -20, -23, -26]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9]) (l₂ := [-11, -13, -15, -18, -20, -23, -26])
  have hm := merge_two (literal (valuationOf q) (760)) (literal (valuationOf q) (780)) (literal (valuationOf q) (789)) (countLit q [-1, -3, -4, -5, -7, -9]) (countLit q [-11, -13, -15, -18, -20, -23, -26]) (count785 q) 2 3 (meaning760 q) (meaning780 q) (meaning789 q) hs
  change valuationOf q 760 = false ∨ valuationOf q 780 = false ∨ valuationOf q 789 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause716 (q : Snake 81) (h : Conditions q) : valuation q 760 = false ∨ valuation q 780 = false ∨ valuation q 789 = true := counterClause716 (baseVal q)

theorem counterClause717 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 798 = true := by
  have hs : count798 q = (countLit q [-28]) + (countLit q [-31]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-31])
  have hm := merge_right (literal (valuationOf q) (-31)) (literal (valuationOf q) (798)) (countLit q [-28]) (countLit q [-31]) (count798 q) 1 (meaningNeg31 q) (meaning798 q) hs
  change (! (valuationOf q 31)) = false ∨ valuationOf q 798 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause717 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 798 = true := counterClause717 (baseVal q)

theorem counterClause718 (q : Nat → Bool) : valuationOf q 798 = false ∨ valuationOf q 800 = true := by
  have hs : count800 q = (countLit q [-27]) + (countLit q [-28, -31]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-28, -31])
  have hm := merge_right (literal (valuationOf q) (798)) (literal (valuationOf q) (800)) (countLit q [-27]) (countLit q [-28, -31]) (count800 q) 1 (meaning798 q) (meaning800 q) hs
  change valuationOf q 798 = false ∨ valuationOf q 800 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause718 (q : Snake 81) (h : Conditions q) : valuation q 798 = false ∨ valuation q 800 = true := counterClause718 (baseVal q)

theorem counterClause719 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 36 = true ∨ valuationOf q 804 = true := by
  have hs : count803 q = (countLit q [-34]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-36])
  have hm := merge_two (literal (valuationOf q) (-34)) (literal (valuationOf q) (-36)) (literal (valuationOf q) (804)) (countLit q [-34]) (countLit q [-36]) (count803 q) 1 1 (meaningNeg34 q) (meaningNeg36 q) (meaning804 q) hs
  change (! (valuationOf q 34)) = false ∨ (! (valuationOf q 36)) = false ∨ valuationOf q 804 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause719 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 36 = true ∨ valuation q 804 = true := counterClause719 (baseVal q)

theorem counterClause720 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 38 = true ∨ valuationOf q 806 = true := by
  have hs : count805 q = (countLit q [-37]) + (countLit q [-38]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-38])
  have hm := merge_two (literal (valuationOf q) (-37)) (literal (valuationOf q) (-38)) (literal (valuationOf q) (806)) (countLit q [-37]) (countLit q [-38]) (count805 q) 1 1 (meaningNeg37 q) (meaningNeg38 q) (meaning806 q) hs
  change (! (valuationOf q 37)) = false ∨ (! (valuationOf q 38)) = false ∨ valuationOf q 806 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause720 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 38 = true ∨ valuation q 806 = true := counterClause720 (baseVal q)

theorem counterClause721 (q : Nat → Bool) : valuationOf q 804 = false ∨ valuationOf q 806 = false ∨ valuationOf q 810 = true := by
  have hs : count807 q = (countLit q [-34, -36]) + (countLit q [-37, -38]) := List.countP_append (p := literal q) (l₁ := [-34, -36]) (l₂ := [-37, -38])
  have hm := merge_two (literal (valuationOf q) (804)) (literal (valuationOf q) (806)) (literal (valuationOf q) (810)) (countLit q [-34, -36]) (countLit q [-37, -38]) (count807 q) 2 2 (meaning804 q) (meaning806 q) (meaning810 q) hs
  change valuationOf q 804 = false ∨ valuationOf q 806 = false ∨ valuationOf q 810 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause721 (q : Snake 81) (h : Conditions q) : valuation q 804 = false ∨ valuation q 806 = false ∨ valuation q 810 = true := counterClause721 (baseVal q)

theorem counterClause722 (q : Nat → Bool) : valuationOf q 800 = false ∨ valuationOf q 810 = false ∨ valuationOf q 815 = true := by
  have hs : count811 q = (countLit q [-27, -28, -31]) + (countLit q [-34, -36, -37, -38]) := List.countP_append (p := literal q) (l₁ := [-27, -28, -31]) (l₂ := [-34, -36, -37, -38])
  have hm := merge_two (literal (valuationOf q) (800)) (literal (valuationOf q) (810)) (literal (valuationOf q) (815)) (countLit q [-27, -28, -31]) (countLit q [-34, -36, -37, -38]) (count811 q) 1 4 (meaning800 q) (meaning810 q) (meaning815 q) hs
  change valuationOf q 800 = false ∨ valuationOf q 810 = false ∨ valuationOf q 815 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause722 (q : Snake 81) (h : Conditions q) : valuation q 800 = false ∨ valuation q 810 = false ∨ valuation q 815 = true := counterClause722 (baseVal q)

theorem counterClause723 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 818 = true := by
  have hs : count818 q = (countLit q [-43]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-44])
  have hm := merge_right (literal (valuationOf q) (-44)) (literal (valuationOf q) (818)) (countLit q [-43]) (countLit q [-44]) (count818 q) 1 (meaningNeg44 q) (meaning818 q) hs
  change (! (valuationOf q 44)) = false ∨ valuationOf q 818 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause723 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 818 = true := counterClause723 (baseVal q)

theorem counterClause724 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 818 = true := by
  have hs : count818 q = (countLit q [-43]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-44])
  have hm := merge_left (literal (valuationOf q) (-43)) (literal (valuationOf q) (818)) (countLit q [-43]) (countLit q [-44]) (count818 q) 1 (meaningNeg43 q) (meaning818 q) hs
  change (! (valuationOf q 43)) = false ∨ valuationOf q 818 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause724 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 818 = true := counterClause724 (baseVal q)

theorem counterClause725 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 820 = true := by
  have hs : count820 q = (countLit q [-41]) + (countLit q [-43, -44]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-43, -44])
  have hm := merge_left (literal (valuationOf q) (-41)) (literal (valuationOf q) (820)) (countLit q [-41]) (countLit q [-43, -44]) (count820 q) 1 (meaningNeg41 q) (meaning820 q) hs
  change (! (valuationOf q 41)) = false ∨ valuationOf q 820 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause725 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 820 = true := counterClause725 (baseVal q)

theorem counterClause726 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 818 = false ∨ valuationOf q 821 = true := by
  have hs : count820 q = (countLit q [-41]) + (countLit q [-43, -44]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-43, -44])
  have hm := merge_two (literal (valuationOf q) (-41)) (literal (valuationOf q) (818)) (literal (valuationOf q) (821)) (countLit q [-41]) (countLit q [-43, -44]) (count820 q) 1 1 (meaningNeg41 q) (meaning818 q) (meaning821 q) hs
  change (! (valuationOf q 41)) = false ∨ valuationOf q 818 = false ∨ valuationOf q 821 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause726 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 818 = false ∨ valuation q 821 = true := counterClause726 (baseVal q)

theorem counterClause727 (q : Nat → Bool) : valuationOf q 49 = true ∨ valuationOf q 823 = true := by
  have hs : count823 q = (countLit q [-48]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-49])
  have hm := merge_right (literal (valuationOf q) (-49)) (literal (valuationOf q) (823)) (countLit q [-48]) (countLit q [-49]) (count823 q) 1 (meaningNeg49 q) (meaning823 q) hs
  change (! (valuationOf q 49)) = false ∨ valuationOf q 823 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause727 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 823 = true := counterClause727 (baseVal q)

theorem counterClause728 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 825 = true := by
  have hs : count825 q = (countLit q [-52]) + (countLit q [-56]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-56])
  have hm := merge_left (literal (valuationOf q) (-52)) (literal (valuationOf q) (825)) (countLit q [-52]) (countLit q [-56]) (count825 q) 1 (meaningNeg52 q) (meaning825 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 825 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause728 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 825 = true := counterClause728 (baseVal q)

theorem counterClause729 (q : Nat → Bool) : valuationOf q 825 = false ∨ valuationOf q 827 = true := by
  have hs : count827 q = (countLit q [-48, -49]) + (countLit q [-52, -56]) := List.countP_append (p := literal q) (l₁ := [-48, -49]) (l₂ := [-52, -56])
  have hm := merge_right (literal (valuationOf q) (825)) (literal (valuationOf q) (827)) (countLit q [-48, -49]) (countLit q [-52, -56]) (count827 q) 1 (meaning825 q) (meaning827 q) hs
  change valuationOf q 825 = false ∨ valuationOf q 827 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause729 (q : Snake 81) (h : Conditions q) : valuation q 825 = false ∨ valuation q 827 = true := counterClause729 (baseVal q)

theorem counterClause730 (q : Nat → Bool) : valuationOf q 823 = false ∨ valuationOf q 827 = true := by
  have hs : count827 q = (countLit q [-48, -49]) + (countLit q [-52, -56]) := List.countP_append (p := literal q) (l₁ := [-48, -49]) (l₂ := [-52, -56])
  have hm := merge_left (literal (valuationOf q) (823)) (literal (valuationOf q) (827)) (countLit q [-48, -49]) (countLit q [-52, -56]) (count827 q) 1 (meaning823 q) (meaning827 q) hs
  change valuationOf q 823 = false ∨ valuationOf q 827 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause730 (q : Snake 81) (h : Conditions q) : valuation q 823 = false ∨ valuation q 827 = true := counterClause730 (baseVal q)

theorem counterClause731 (q : Nat → Bool) : valuationOf q 820 = false ∨ valuationOf q 827 = false ∨ valuationOf q 832 = true := by
  have hs : count831 q = (countLit q [-41, -43, -44]) + (countLit q [-48, -49, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-41, -43, -44]) (l₂ := [-48, -49, -52, -56])
  have hm := merge_two (literal (valuationOf q) (820)) (literal (valuationOf q) (827)) (literal (valuationOf q) (832)) (countLit q [-41, -43, -44]) (countLit q [-48, -49, -52, -56]) (count831 q) 1 1 (meaning820 q) (meaning827 q) (meaning832 q) hs
  change valuationOf q 820 = false ∨ valuationOf q 827 = false ∨ valuationOf q 832 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause731 (q : Snake 81) (h : Conditions q) : valuation q 820 = false ∨ valuation q 827 = false ∨ valuation q 832 = true := counterClause731 (baseVal q)

theorem counterClause732 (q : Nat → Bool) : valuationOf q 821 = false ∨ valuationOf q 832 = true := by
  have hs : count831 q = (countLit q [-41, -43, -44]) + (countLit q [-48, -49, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-41, -43, -44]) (l₂ := [-48, -49, -52, -56])
  have hm := merge_left (literal (valuationOf q) (821)) (literal (valuationOf q) (832)) (countLit q [-41, -43, -44]) (countLit q [-48, -49, -52, -56]) (count831 q) 2 (meaning821 q) (meaning832 q) hs
  change valuationOf q 821 = false ∨ valuationOf q 832 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause732 (q : Snake 81) (h : Conditions q) : valuation q 821 = false ∨ valuation q 832 = true := counterClause732 (baseVal q)

theorem counterClause733 (q : Nat → Bool) : valuationOf q 815 = false ∨ valuationOf q 832 = false ∨ valuationOf q 844 = true := by
  have hs : count838 q = (countLit q [-27, -28, -31, -34, -36, -37, -38]) + (countLit q [-41, -43, -44, -48, -49, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -28, -31, -34, -36, -37, -38]) (l₂ := [-41, -43, -44, -48, -49, -52, -56])
  have hm := merge_two (literal (valuationOf q) (815)) (literal (valuationOf q) (832)) (literal (valuationOf q) (844)) (countLit q [-27, -28, -31, -34, -36, -37, -38]) (countLit q [-41, -43, -44, -48, -49, -52, -56]) (count838 q) 5 2 (meaning815 q) (meaning832 q) (meaning844 q) hs
  change valuationOf q 815 = false ∨ valuationOf q 832 = false ∨ valuationOf q 844 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause733 (q : Snake 81) (h : Conditions q) : valuation q 815 = false ∨ valuation q 832 = false ∨ valuation q 844 = true := counterClause733 (baseVal q)

theorem counterClause734 (q : Nat → Bool) : valuationOf q 789 = false ∨ valuationOf q 844 = false ∨ valuationOf q 863 = true := by
  have hs : count852 q = (countLit q [-1, -3, -4, -5, -7, -9, -11, -13, -15, -18, -20, -23, -26]) + (countLit q [-27, -28, -31, -34, -36, -37, -38, -41, -43, -44, -48, -49, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -7, -9, -11, -13, -15, -18, -20, -23, -26]) (l₂ := [-27, -28, -31, -34, -36, -37, -38, -41, -43, -44, -48, -49, -52, -56])
  have hm := merge_two (literal (valuationOf q) (789)) (literal (valuationOf q) (844)) (literal (valuationOf q) (863)) (countLit q [-1, -3, -4, -5, -7, -9, -11, -13, -15, -18, -20, -23, -26]) (countLit q [-27, -28, -31, -34, -36, -37, -38, -41, -43, -44, -48, -49, -52, -56]) (count852 q) 5 7 (meaning789 q) (meaning844 q) (meaning863 q) hs
  change valuationOf q 789 = false ∨ valuationOf q 844 = false ∨ valuationOf q 863 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause734 (q : Snake 81) (h : Conditions q) : valuation q 789 = false ∨ valuation q 844 = false ∨ valuation q 863 = true := counterClause734 (baseVal q)

theorem counterClause735 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 892 = true := by
  have hs : count892 q = (countLit q [-77]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-79])
  have hm := merge_right (literal (valuationOf q) (-79)) (literal (valuationOf q) (892)) (countLit q [-77]) (countLit q [-79]) (count892 q) 1 (meaningNeg79 q) (meaning892 q) hs
  change (! (valuationOf q 79)) = false ∨ valuationOf q 892 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause735 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 892 = true := counterClause735 (baseVal q)

theorem counterClause736 (q : Nat → Bool) : valuationOf q 892 = false ∨ valuationOf q 896 = true := by
  have hs : count896 q = (countLit q [-77, -79]) + (countLit q [-82, -83]) := List.countP_append (p := literal q) (l₁ := [-77, -79]) (l₂ := [-82, -83])
  have hm := merge_left (literal (valuationOf q) (892)) (literal (valuationOf q) (896)) (countLit q [-77, -79]) (countLit q [-82, -83]) (count896 q) 1 (meaning892 q) (meaning896 q) hs
  change valuationOf q 892 = false ∨ valuationOf q 896 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause736 (q : Snake 81) (h : Conditions q) : valuation q 892 = false ∨ valuation q 896 = true := counterClause736 (baseVal q)

theorem block22 (q : Snake 81) (h : Conditions q) : B112E161.Block22 (valuation q) :=
  ⟨clause705 q h, clause706 q h, clause707 q h, clause708 q h, clause709 q h, clause710 q h, clause711 q h, clause712 q h, clause713 q h, clause714 q h, clause715 q h, clause716 q h, clause717 q h, clause718 q h, clause719 q h, clause720 q h, clause721 q h, clause722 q h, clause723 q h, clause724 q h, clause725 q h, clause726 q h, clause727 q h, clause728 q h, clause729 q h, clause730 q h, clause731 q h, clause732 q h, clause733 q h, clause734 q h, clause735 q h, clause736 q h⟩

end
end Snake9.Regrowth.E112161
