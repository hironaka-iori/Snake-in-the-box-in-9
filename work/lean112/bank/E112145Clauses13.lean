import E112145Semantics
import B112E145Inputs
namespace Snake9.Regrowth.E112145
noncomputable section
local instance blockDec13 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause417 (q : Nat → Bool) : valuationOf q 407 = false ∨ valuationOf q 409 = true := by
  have hs : count409 q = (countLit q [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) + (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (l₂ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208])
  have hm := merge_right (literal (valuationOf q) (407)) (literal (valuationOf q) (409)) (countLit q [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (count409 q) 1 (meaning407 q) (meaning409 q) hs
  change valuationOf q 407 = false ∨ valuationOf q 409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause417 (q : Snake 81) (h : Conditions q) : valuation q 407 = false ∨ valuation q 409 = true := counterClause417 (baseVal q)

theorem counterClause418 (q : Nat → Bool) : valuationOf q 408 = false ∨ valuationOf q 410 = true := by
  have hs : count409 q = (countLit q [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) + (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (l₂ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208])
  have hm := merge_right (literal (valuationOf q) (408)) (literal (valuationOf q) (410)) (countLit q [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (count409 q) 2 (meaning408 q) (meaning410 q) hs
  change valuationOf q 408 = false ∨ valuationOf q 410 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause418 (q : Snake 81) (h : Conditions q) : valuation q 408 = false ∨ valuation q 410 = true := counterClause418 (baseVal q)

theorem counterClause419 (q : Nat → Bool) : valuationOf q 357 = false ∨ valuationOf q 409 = true := by
  have hs : count409 q = (countLit q [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) + (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (l₂ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208])
  have hm := merge_left (literal (valuationOf q) (357)) (literal (valuationOf q) (409)) (countLit q [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (count409 q) 1 (meaning357 q) (meaning409 q) hs
  change valuationOf q 357 = false ∨ valuationOf q 409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause419 (q : Snake 81) (h : Conditions q) : valuation q 357 = false ∨ valuation q 409 = true := counterClause419 (baseVal q)

theorem counterClause420 (q : Nat → Bool) : valuationOf q 358 = false ∨ valuationOf q 410 = true := by
  have hs : count409 q = (countLit q [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) + (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (l₂ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208])
  have hm := merge_left (literal (valuationOf q) (358)) (literal (valuationOf q) (410)) (countLit q [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (count409 q) 2 (meaning358 q) (meaning410 q) hs
  change valuationOf q 358 = false ∨ valuationOf q 410 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause420 (q : Snake 81) (h : Conditions q) : valuation q 358 = false ∨ valuation q 410 = true := counterClause420 (baseVal q)

theorem counterClause421 (q : Nat → Bool) : valuationOf q 410 = false ∨ valuationOf q 412 = true := by
  have hs : count411 q = (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156]) + (countLit q [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156]) (l₂ := [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208])
  have hm := merge_right (literal (valuationOf q) (410)) (literal (valuationOf q) (412)) (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156]) (countLit q [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (count411 q) 2 (meaning410 q) (meaning412 q) hs
  change valuationOf q 410 = false ∨ valuationOf q 412 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause421 (q : Snake 81) (h : Conditions q) : valuation q 410 = false ∨ valuation q 412 = true := counterClause421 (baseVal q)

theorem counterClause422 (q : Nat → Bool) : valuationOf q 307 = false ∨ valuationOf q 409 = false ∨ valuationOf q 412 = true := by
  have hs : count411 q = (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156]) + (countLit q [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156]) (l₂ := [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208])
  have hm := merge_two (literal (valuationOf q) (307)) (literal (valuationOf q) (409)) (literal (valuationOf q) (412)) (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156]) (countLit q [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (count411 q) 1 1 (meaning307 q) (meaning409 q) (meaning412 q) hs
  change valuationOf q 307 = false ∨ valuationOf q 409 = false ∨ valuationOf q 412 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause422 (q : Snake 81) (h : Conditions q) : valuation q 307 = false ∨ valuation q 409 = false ∨ valuation q 412 = true := counterClause422 (baseVal q)

theorem counterClause423 (q : Nat → Bool) : valuationOf q 308 = false ∨ valuationOf q 412 = true := by
  have hs : count411 q = (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156]) + (countLit q [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) := List.countP_append (p := literal q) (l₁ := [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156]) (l₂ := [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208])
  have hm := merge_left (literal (valuationOf q) (308)) (literal (valuationOf q) (412)) (countLit q [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156]) (countLit q [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]) (count411 q) 2 (meaning308 q) (meaning412 q) hs
  change valuationOf q 308 = false ∨ valuationOf q 412 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause423 (q : Snake 81) (h : Conditions q) : valuation q 308 = false ∨ valuation q 412 = true := counterClause423 (baseVal q)

theorem clause424 (q : Snake 81) (h : Conditions q) : valuation q 412 = false := by
  rw [value412]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count411 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem clause425 (q : Snake 81) (h : Conditions q) : valuation q 105 = true ∨ valuation q 106 = true ∨ valuation q 107 = true ∨ valuation q 108 = true ∨ valuation q 109 = true ∨ valuation q 110 = true ∨ valuation q 111 = true ∨ valuation q 112 = true ∨ valuation q 113 = true ∨ valuation q 114 = true ∨ valuation q 115 = true ∨ valuation q 116 = true ∨ valuation q 117 = true ∨ valuation q 118 = true ∨ valuation q 119 = true ∨ valuation q 120 = true ∨ valuation q 121 = true ∨ valuation q 122 = true ∨ valuation q 124 = true ∨ valuation q 125 = true ∨ valuation q 126 = true ∨ valuation q 127 = true ∨ valuation q 128 = true ∨ valuation q 129 = true ∨ valuation q 130 = true ∨ valuation q 131 = true ∨ valuation q 132 = true ∨ valuation q 133 = true ∨ valuation q 134 = true ∨ valuation q 135 = true ∨ valuation q 136 = true ∨ valuation q 137 = true ∨ valuation q 138 = true ∨ valuation q 139 = true ∨ valuation q 140 = true ∨ valuation q 141 = true ∨ valuation q 142 = true ∨ valuation q 143 = true ∨ valuation q 144 = true ∨ valuation q 145 = true ∨ valuation q 146 = true ∨ valuation q 147 = true ∨ valuation q 148 = true ∨ valuation q 149 = true ∨ valuation q 150 = true ∨ valuation q 151 = true ∨ valuation q 152 = true ∨ valuation q 153 = true ∨ valuation q 154 = true ∨ valuation q 155 = true ∨ valuation q 156 = true ∨ valuation q 157 = true ∨ valuation q 158 = true ∨ valuation q 159 = true ∨ valuation q 160 = true ∨ valuation q 161 = true ∨ valuation q 162 = true ∨ valuation q 163 = true ∨ valuation q 164 = true ∨ valuation q 165 = true ∨ valuation q 166 = true ∨ valuation q 167 = true ∨ valuation q 168 = true ∨ valuation q 169 = true ∨ valuation q 170 = true ∨ valuation q 171 = true ∨ valuation q 172 = true ∨ valuation q 173 = true ∨ valuation q 174 = true ∨ valuation q 175 = true ∨ valuation q 176 = true ∨ valuation q 177 = true ∨ valuation q 178 = true ∨ valuation q 179 = true ∨ valuation q 180 = true ∨ valuation q 181 = true ∨ valuation q 182 = true ∨ valuation q 183 = true ∨ valuation q 184 = true ∨ valuation q 185 = true ∨ valuation q 186 = true ∨ valuation q 187 = true ∨ valuation q 188 = true ∨ valuation q 189 = true ∨ valuation q 190 = true ∨ valuation q 191 = true ∨ valuation q 192 = true ∨ valuation q 193 = true ∨ valuation q 194 = true ∨ valuation q 195 = true ∨ valuation q 196 = true ∨ valuation q 197 = true ∨ valuation q 198 = true ∨ valuation q 199 = true ∨ valuation q 200 = true ∨ valuation q 201 = true ∨ valuation q 202 = true ∨ valuation q 203 = true ∨ valuation q 204 = true ∨ valuation q 205 = true ∨ valuation q 206 = true ∨ valuation q 207 = true ∨ valuation q 208 = true := by
  rw [value105, value106, value107, value108, value109, value110, value111, value112, value113, value114, value115, value116, value117, value118, value119, value120, value121, value122, value124, value125, value126, value127, value128, value129, value130, value131, value132, value133, value134, value135, value136, value137, value138, value139, value140, value141, value142, value143, value144, value145, value146, value147, value148, value149, value150, value151, value152, value153, value154, value155, value156, value157, value158, value159, value160, value161, value162, value163, value164, value165, value166, value167, value168, value169, value170, value171, value172, value173, value174, value175, value176, value177, value178, value179, value180, value181, value182, value183, value184, value185, value186, value187, value188, value189, value190, value191, value192, value193, value194, value195, value196, value197, value198, value199, value200, value201, value202, value203, value204, value205, value206, value207, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hg := other_endpoint q others (fun v hv hn => others_mem v (h.covered v hv) (by simpa only [h.head_fixed] using hn))
  simpa only [others, List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem counterClause426 (q : Nat → Bool) : valuationOf q 9 = true ∨ valuationOf q 10 = true ∨ valuationOf q 715 = true := by
  have hs : count714 q = (countLit q [-9]) + (countLit q [-10]) := List.countP_append (p := literal q) (l₁ := [-9]) (l₂ := [-10])
  have hm := merge_two (literal (valuationOf q) (-9)) (literal (valuationOf q) (-10)) (literal (valuationOf q) (715)) (countLit q [-9]) (countLit q [-10]) (count714 q) 1 1 (meaningNeg9 q) (meaningNeg10 q) (meaning715 q) hs
  change (! (valuationOf q 9)) = false ∨ (! (valuationOf q 10)) = false ∨ valuationOf q 715 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause426 (q : Snake 81) (h : Conditions q) : valuation q 9 = true ∨ valuation q 10 = true ∨ valuation q 715 = true := counterClause426 (baseVal q)

theorem counterClause427 (q : Nat → Bool) : valuationOf q 715 = false ∨ valuationOf q 717 = true := by
  have hs : count716 q = (countLit q [-5]) + (countLit q [-9, -10]) := List.countP_append (p := literal q) (l₁ := [-5]) (l₂ := [-9, -10])
  have hm := merge_right (literal (valuationOf q) (715)) (literal (valuationOf q) (717)) (countLit q [-5]) (countLit q [-9, -10]) (count716 q) 2 (meaning715 q) (meaning717 q) hs
  change valuationOf q 715 = false ∨ valuationOf q 717 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause427 (q : Snake 81) (h : Conditions q) : valuation q 715 = false ∨ valuation q 717 = true := counterClause427 (baseVal q)

theorem counterClause428 (q : Nat → Bool) : valuationOf q 717 = false ∨ valuationOf q 720 = true := by
  have hs : count719 q = (countLit q [-1, -3, -4]) + (countLit q [-5, -9, -10]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4]) (l₂ := [-5, -9, -10])
  have hm := merge_right (literal (valuationOf q) (717)) (literal (valuationOf q) (720)) (countLit q [-1, -3, -4]) (countLit q [-5, -9, -10]) (count719 q) 2 (meaning717 q) (meaning720 q) hs
  change valuationOf q 717 = false ∨ valuationOf q 720 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause428 (q : Snake 81) (h : Conditions q) : valuation q 717 = false ∨ valuation q 720 = true := counterClause428 (baseVal q)

theorem counterClause429 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 725 = true := by
  have hs : count725 q = (countLit q [-15]) + (countLit q [-17]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-17])
  have hm := merge_right (literal (valuationOf q) (-17)) (literal (valuationOf q) (725)) (countLit q [-15]) (countLit q [-17]) (count725 q) 1 (meaningNeg17 q) (meaning725 q) hs
  change (! (valuationOf q 17)) = false ∨ valuationOf q 725 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause429 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 725 = true := counterClause429 (baseVal q)

theorem counterClause430 (q : Nat → Bool) : valuationOf q 12 = true ∨ valuationOf q 725 = false ∨ valuationOf q 728 = true := by
  have hs : count727 q = (countLit q [-12]) + (countLit q [-15, -17]) := List.countP_append (p := literal q) (l₁ := [-12]) (l₂ := [-15, -17])
  have hm := merge_two (literal (valuationOf q) (-12)) (literal (valuationOf q) (725)) (literal (valuationOf q) (728)) (countLit q [-12]) (countLit q [-15, -17]) (count727 q) 1 1 (meaningNeg12 q) (meaning725 q) (meaning728 q) hs
  change (! (valuationOf q 12)) = false ∨ valuationOf q 725 = false ∨ valuationOf q 728 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause430 (q : Snake 81) (h : Conditions q) : valuation q 12 = true ∨ valuation q 725 = false ∨ valuation q 728 = true := counterClause430 (baseVal q)

theorem counterClause431 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 26 = true ∨ valuationOf q 733 = true := by
  have hs : count732 q = (countLit q [-22]) + (countLit q [-26]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-26])
  have hm := merge_two (literal (valuationOf q) (-22)) (literal (valuationOf q) (-26)) (literal (valuationOf q) (733)) (countLit q [-22]) (countLit q [-26]) (count732 q) 1 1 (meaningNeg22 q) (meaningNeg26 q) (meaning733 q) hs
  change (! (valuationOf q 22)) = false ∨ (! (valuationOf q 26)) = false ∨ valuationOf q 733 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause431 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 26 = true ∨ valuation q 733 = true := counterClause431 (baseVal q)

theorem counterClause432 (q : Nat → Bool) : valuationOf q 733 = false ∨ valuationOf q 735 = true := by
  have hs : count734 q = (countLit q [-19, -20]) + (countLit q [-22, -26]) := List.countP_append (p := literal q) (l₁ := [-19, -20]) (l₂ := [-22, -26])
  have hm := merge_right (literal (valuationOf q) (733)) (literal (valuationOf q) (735)) (countLit q [-19, -20]) (countLit q [-22, -26]) (count734 q) 2 (meaning733 q) (meaning735 q) hs
  change valuationOf q 733 = false ∨ valuationOf q 735 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause432 (q : Snake 81) (h : Conditions q) : valuation q 733 = false ∨ valuation q 735 = true := counterClause432 (baseVal q)

theorem counterClause433 (q : Nat → Bool) : valuationOf q 728 = false ∨ valuationOf q 735 = false ∨ valuationOf q 741 = true := by
  have hs : count738 q = (countLit q [-12, -15, -17]) + (countLit q [-19, -20, -22, -26]) := List.countP_append (p := literal q) (l₁ := [-12, -15, -17]) (l₂ := [-19, -20, -22, -26])
  have hm := merge_two (literal (valuationOf q) (728)) (literal (valuationOf q) (735)) (literal (valuationOf q) (741)) (countLit q [-12, -15, -17]) (countLit q [-19, -20, -22, -26]) (count738 q) 2 2 (meaning728 q) (meaning735 q) (meaning741 q) hs
  change valuationOf q 728 = false ∨ valuationOf q 735 = false ∨ valuationOf q 741 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause433 (q : Snake 81) (h : Conditions q) : valuation q 728 = false ∨ valuation q 735 = false ∨ valuation q 741 = true := counterClause433 (baseVal q)

theorem counterClause434 (q : Nat → Bool) : valuationOf q 720 = false ∨ valuationOf q 741 = false ∨ valuationOf q 750 = true := by
  have hs : count745 q = (countLit q [-1, -3, -4, -5, -9, -10]) + (countLit q [-12, -15, -17, -19, -20, -22, -26]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10]) (l₂ := [-12, -15, -17, -19, -20, -22, -26])
  have hm := merge_two (literal (valuationOf q) (720)) (literal (valuationOf q) (741)) (literal (valuationOf q) (750)) (countLit q [-1, -3, -4, -5, -9, -10]) (countLit q [-12, -15, -17, -19, -20, -22, -26]) (count745 q) 2 4 (meaning720 q) (meaning741 q) (meaning750 q) hs
  change valuationOf q 720 = false ∨ valuationOf q 741 = false ∨ valuationOf q 750 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause434 (q : Snake 81) (h : Conditions q) : valuation q 720 = false ∨ valuation q 741 = false ∨ valuation q 750 = true := counterClause434 (baseVal q)

theorem counterClause435 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 758 = true := by
  have hs : count758 q = (countLit q [-28]) + (countLit q [-33]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-33])
  have hm := merge_right (literal (valuationOf q) (-33)) (literal (valuationOf q) (758)) (countLit q [-28]) (countLit q [-33]) (count758 q) 1 (meaningNeg33 q) (meaning758 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 758 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause435 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 758 = true := counterClause435 (baseVal q)

theorem counterClause436 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 758 = false ∨ valuationOf q 761 = true := by
  have hs : count760 q = (countLit q [-27]) + (countLit q [-28, -33]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-28, -33])
  have hm := merge_two (literal (valuationOf q) (-27)) (literal (valuationOf q) (758)) (literal (valuationOf q) (761)) (countLit q [-27]) (countLit q [-28, -33]) (count760 q) 1 1 (meaningNeg27 q) (meaning758 q) (meaning761 q) hs
  change (! (valuationOf q 27)) = false ∨ valuationOf q 758 = false ∨ valuationOf q 761 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause436 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 758 = false ∨ valuation q 761 = true := counterClause436 (baseVal q)

theorem counterClause437 (q : Nat → Bool) : valuationOf q 761 = false ∨ valuationOf q 769 = true := by
  have hs : count768 q = (countLit q [-27, -28, -33]) + (countLit q [-34, -36, -37]) := List.countP_append (p := literal q) (l₁ := [-27, -28, -33]) (l₂ := [-34, -36, -37])
  have hm := merge_left (literal (valuationOf q) (761)) (literal (valuationOf q) (769)) (countLit q [-27, -28, -33]) (countLit q [-34, -36, -37]) (count768 q) 2 (meaning761 q) (meaning769 q) hs
  change valuationOf q 761 = false ∨ valuationOf q 769 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause437 (q : Snake 81) (h : Conditions q) : valuation q 761 = false ∨ valuation q 769 = true := counterClause437 (baseVal q)

theorem counterClause438 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 776 = true := by
  have hs : count776 q = (countLit q [-39]) + (countLit q [-40, -44]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-40, -44])
  have hm := merge_left (literal (valuationOf q) (-39)) (literal (valuationOf q) (776)) (countLit q [-39]) (countLit q [-40, -44]) (count776 q) 1 (meaningNeg39 q) (meaning776 q) hs
  change (! (valuationOf q 39)) = false ∨ valuationOf q 776 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause438 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 776 = true := counterClause438 (baseVal q)

theorem counterClause439 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 779 = true := by
  have hs : count779 q = (countLit q [-46]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-48])
  have hm := merge_left (literal (valuationOf q) (-46)) (literal (valuationOf q) (779)) (countLit q [-46]) (countLit q [-48]) (count779 q) 1 (meaningNeg46 q) (meaning779 q) hs
  change (! (valuationOf q 46)) = false ∨ valuationOf q 779 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause439 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 779 = true := counterClause439 (baseVal q)

theorem counterClause440 (q : Nat → Bool) : valuationOf q 51 = true ∨ valuationOf q 781 = true := by
  have hs : count781 q = (countLit q [-49]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-49]) (l₂ := [-51])
  have hm := merge_right (literal (valuationOf q) (-51)) (literal (valuationOf q) (781)) (countLit q [-49]) (countLit q [-51]) (count781 q) 1 (meaningNeg51 q) (meaning781 q) hs
  change (! (valuationOf q 51)) = false ∨ valuationOf q 781 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause440 (q : Snake 81) (h : Conditions q) : valuation q 51 = true ∨ valuation q 781 = true := counterClause440 (baseVal q)

theorem counterClause441 (q : Nat → Bool) : valuationOf q 781 = false ∨ valuationOf q 783 = true := by
  have hs : count783 q = (countLit q [-46, -48]) + (countLit q [-49, -51]) := List.countP_append (p := literal q) (l₁ := [-46, -48]) (l₂ := [-49, -51])
  have hm := merge_right (literal (valuationOf q) (781)) (literal (valuationOf q) (783)) (countLit q [-46, -48]) (countLit q [-49, -51]) (count783 q) 1 (meaning781 q) (meaning783 q) hs
  change valuationOf q 781 = false ∨ valuationOf q 783 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause441 (q : Snake 81) (h : Conditions q) : valuation q 781 = false ∨ valuation q 783 = true := counterClause441 (baseVal q)

theorem counterClause442 (q : Nat → Bool) : valuationOf q 779 = false ∨ valuationOf q 783 = true := by
  have hs : count783 q = (countLit q [-46, -48]) + (countLit q [-49, -51]) := List.countP_append (p := literal q) (l₁ := [-46, -48]) (l₂ := [-49, -51])
  have hm := merge_left (literal (valuationOf q) (779)) (literal (valuationOf q) (783)) (countLit q [-46, -48]) (countLit q [-49, -51]) (count783 q) 1 (meaning779 q) (meaning783 q) hs
  change valuationOf q 779 = false ∨ valuationOf q 783 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause442 (q : Snake 81) (h : Conditions q) : valuation q 779 = false ∨ valuation q 783 = true := counterClause442 (baseVal q)

theorem counterClause443 (q : Nat → Bool) : valuationOf q 783 = false ∨ valuationOf q 787 = true := by
  have hs : count787 q = (countLit q [-39, -40, -44]) + (countLit q [-46, -48, -49, -51]) := List.countP_append (p := literal q) (l₁ := [-39, -40, -44]) (l₂ := [-46, -48, -49, -51])
  have hm := merge_right (literal (valuationOf q) (783)) (literal (valuationOf q) (787)) (countLit q [-39, -40, -44]) (countLit q [-46, -48, -49, -51]) (count787 q) 1 (meaning783 q) (meaning787 q) hs
  change valuationOf q 783 = false ∨ valuationOf q 787 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause443 (q : Snake 81) (h : Conditions q) : valuation q 783 = false ∨ valuation q 787 = true := counterClause443 (baseVal q)

theorem counterClause444 (q : Nat → Bool) : valuationOf q 776 = false ∨ valuationOf q 787 = true := by
  have hs : count787 q = (countLit q [-39, -40, -44]) + (countLit q [-46, -48, -49, -51]) := List.countP_append (p := literal q) (l₁ := [-39, -40, -44]) (l₂ := [-46, -48, -49, -51])
  have hm := merge_left (literal (valuationOf q) (776)) (literal (valuationOf q) (787)) (countLit q [-39, -40, -44]) (countLit q [-46, -48, -49, -51]) (count787 q) 1 (meaning776 q) (meaning787 q) hs
  change valuationOf q 776 = false ∨ valuationOf q 787 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause444 (q : Snake 81) (h : Conditions q) : valuation q 776 = false ∨ valuation q 787 = true := counterClause444 (baseVal q)

theorem counterClause445 (q : Nat → Bool) : valuationOf q 769 = false ∨ valuationOf q 787 = false ∨ valuationOf q 796 = true := by
  have hs : count794 q = (countLit q [-27, -28, -33, -34, -36, -37]) + (countLit q [-39, -40, -44, -46, -48, -49, -51]) := List.countP_append (p := literal q) (l₁ := [-27, -28, -33, -34, -36, -37]) (l₂ := [-39, -40, -44, -46, -48, -49, -51])
  have hm := merge_two (literal (valuationOf q) (769)) (literal (valuationOf q) (787)) (literal (valuationOf q) (796)) (countLit q [-27, -28, -33, -34, -36, -37]) (countLit q [-39, -40, -44, -46, -48, -49, -51]) (count794 q) 2 1 (meaning769 q) (meaning787 q) (meaning796 q) hs
  change valuationOf q 769 = false ∨ valuationOf q 787 = false ∨ valuationOf q 796 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause445 (q : Snake 81) (h : Conditions q) : valuation q 769 = false ∨ valuation q 787 = false ∨ valuation q 796 = true := counterClause445 (baseVal q)

theorem counterClause446 (q : Nat → Bool) : valuationOf q 750 = false ∨ valuationOf q 796 = false ∨ valuationOf q 815 = true := by
  have hs : count807 q = (countLit q [-1, -3, -4, -5, -9, -10, -12, -15, -17, -19, -20, -22, -26]) + (countLit q [-27, -28, -33, -34, -36, -37, -39, -40, -44, -46, -48, -49, -51]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -12, -15, -17, -19, -20, -22, -26]) (l₂ := [-27, -28, -33, -34, -36, -37, -39, -40, -44, -46, -48, -49, -51])
  have hm := merge_two (literal (valuationOf q) (750)) (literal (valuationOf q) (796)) (literal (valuationOf q) (815)) (countLit q [-1, -3, -4, -5, -9, -10, -12, -15, -17, -19, -20, -22, -26]) (countLit q [-27, -28, -33, -34, -36, -37, -39, -40, -44, -46, -48, -49, -51]) (count807 q) 6 3 (meaning750 q) (meaning796 q) (meaning815 q) hs
  change valuationOf q 750 = false ∨ valuationOf q 796 = false ∨ valuationOf q 815 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause446 (q : Snake 81) (h : Conditions q) : valuation q 750 = false ∨ valuation q 796 = false ∨ valuation q 815 = true := counterClause446 (baseVal q)

theorem counterClause447 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 820 = true := by
  have hs : count820 q = (countLit q [-54]) + (countLit q [-56]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-56])
  have hm := merge_right (literal (valuationOf q) (-56)) (literal (valuationOf q) (820)) (countLit q [-54]) (countLit q [-56]) (count820 q) 1 (meaningNeg56 q) (meaning820 q) hs
  change (! (valuationOf q 56)) = false ∨ valuationOf q 820 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause447 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 820 = true := counterClause447 (baseVal q)

theorem counterClause448 (q : Nat → Bool) : valuationOf q 820 = false ∨ valuationOf q 822 = true := by
  have hs : count822 q = (countLit q [-52]) + (countLit q [-54, -56]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-54, -56])
  have hm := merge_right (literal (valuationOf q) (820)) (literal (valuationOf q) (822)) (countLit q [-52]) (countLit q [-54, -56]) (count822 q) 1 (meaning820 q) (meaning822 q) hs
  change valuationOf q 820 = false ∨ valuationOf q 822 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause448 (q : Snake 81) (h : Conditions q) : valuation q 820 = false ∨ valuation q 822 = true := counterClause448 (baseVal q)

theorem block13 (q : Snake 81) (h : Conditions q) : B112E145.Block13 (valuation q) :=
  ⟨clause417 q h, clause418 q h, clause419 q h, clause420 q h, clause421 q h, clause422 q h, clause423 q h, clause424 q h, clause425 q h, clause426 q h, clause427 q h, clause428 q h, clause429 q h, clause430 q h, clause431 q h, clause432 q h, clause433 q h, clause434 q h, clause435 q h, clause436 q h, clause437 q h, clause438 q h, clause439 q h, clause440 q h, clause441 q h, clause442 q h, clause443 q h, clause444 q h, clause445 q h, clause446 q h, clause447 q h, clause448 q h⟩

end
end Snake9.Regrowth.E112145
