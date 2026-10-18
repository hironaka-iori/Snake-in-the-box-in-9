import E112050Semantics
import B112E050Inputs
namespace Snake9.Regrowth.E112050
noncomputable section
local instance blockDec34 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1089 (q : Nat → Bool) : valuationOf q 503 = false ∨ valuationOf q 505 = true := by
  have hs : count505 q = (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224]) + (countLit q [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]) := List.countP_append (p := literal q) (l₁ := [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224]) (l₂ := [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256])
  have hm := merge_right (literal (valuationOf q) (503)) (literal (valuationOf q) (505)) (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224]) (countLit q [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]) (count505 q) 1 (meaning503 q) (meaning505 q) hs
  change valuationOf q 503 = false ∨ valuationOf q 505 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1089 (q : Snake 81) (h : Conditions q) : valuation q 503 = false ∨ valuation q 505 = true := counterClause1089 (baseVal q)

theorem counterClause1090 (q : Nat → Bool) : valuationOf q 504 = false ∨ valuationOf q 506 = true := by
  have hs : count505 q = (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224]) + (countLit q [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]) := List.countP_append (p := literal q) (l₁ := [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224]) (l₂ := [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256])
  have hm := merge_right (literal (valuationOf q) (504)) (literal (valuationOf q) (506)) (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224]) (countLit q [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]) (count505 q) 2 (meaning504 q) (meaning506 q) hs
  change valuationOf q 504 = false ∨ valuationOf q 506 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1090 (q : Snake 81) (h : Conditions q) : valuation q 504 = false ∨ valuation q 506 = true := counterClause1090 (baseVal q)

theorem counterClause1091 (q : Nat → Bool) : valuationOf q 441 = false ∨ valuationOf q 505 = true := by
  have hs : count505 q = (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224]) + (countLit q [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]) := List.countP_append (p := literal q) (l₁ := [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224]) (l₂ := [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256])
  have hm := merge_left (literal (valuationOf q) (441)) (literal (valuationOf q) (505)) (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224]) (countLit q [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]) (count505 q) 1 (meaning441 q) (meaning505 q) hs
  change valuationOf q 441 = false ∨ valuationOf q 505 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1091 (q : Snake 81) (h : Conditions q) : valuation q 441 = false ∨ valuation q 505 = true := counterClause1091 (baseVal q)

theorem counterClause1092 (q : Nat → Bool) : valuationOf q 441 = false ∨ valuationOf q 503 = false ∨ valuationOf q 506 = true := by
  have hs : count505 q = (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224]) + (countLit q [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]) := List.countP_append (p := literal q) (l₁ := [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224]) (l₂ := [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256])
  have hm := merge_two (literal (valuationOf q) (441)) (literal (valuationOf q) (503)) (literal (valuationOf q) (506)) (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224]) (countLit q [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]) (count505 q) 1 1 (meaning441 q) (meaning503 q) (meaning506 q) hs
  change valuationOf q 441 = false ∨ valuationOf q 503 = false ∨ valuationOf q 506 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1092 (q : Snake 81) (h : Conditions q) : valuation q 441 = false ∨ valuation q 503 = false ∨ valuation q 506 = true := counterClause1092 (baseVal q)

theorem counterClause1093 (q : Nat → Bool) : valuationOf q 442 = false ∨ valuationOf q 506 = true := by
  have hs : count505 q = (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224]) + (countLit q [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]) := List.countP_append (p := literal q) (l₁ := [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224]) (l₂ := [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256])
  have hm := merge_left (literal (valuationOf q) (442)) (literal (valuationOf q) (506)) (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224]) (countLit q [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]) (count505 q) 2 (meaning442 q) (meaning506 q) hs
  change valuationOf q 442 = false ∨ valuationOf q 506 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1093 (q : Snake 81) (h : Conditions q) : valuation q 442 = false ∨ valuation q 506 = true := counterClause1093 (baseVal q)

theorem counterClause1094 (q : Nat → Bool) : valuationOf q 506 = false ∨ valuationOf q 508 = true := by
  have hs : count507 q = (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) + (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]) := List.countP_append (p := literal q) (l₁ := [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (l₂ := [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256])
  have hm := merge_right (literal (valuationOf q) (506)) (literal (valuationOf q) (508)) (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]) (count507 q) 2 (meaning506 q) (meaning508 q) hs
  change valuationOf q 506 = false ∨ valuationOf q 508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1094 (q : Snake 81) (h : Conditions q) : valuation q 506 = false ∨ valuation q 508 = true := counterClause1094 (baseVal q)

theorem counterClause1095 (q : Nat → Bool) : valuationOf q 379 = false ∨ valuationOf q 505 = false ∨ valuationOf q 508 = true := by
  have hs : count507 q = (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) + (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]) := List.countP_append (p := literal q) (l₁ := [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (l₂ := [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256])
  have hm := merge_two (literal (valuationOf q) (379)) (literal (valuationOf q) (505)) (literal (valuationOf q) (508)) (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]) (count507 q) 1 1 (meaning379 q) (meaning505 q) (meaning508 q) hs
  change valuationOf q 379 = false ∨ valuationOf q 505 = false ∨ valuationOf q 508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1095 (q : Snake 81) (h : Conditions q) : valuation q 379 = false ∨ valuation q 505 = false ∨ valuation q 508 = true := counterClause1095 (baseVal q)

theorem counterClause1096 (q : Nat → Bool) : valuationOf q 380 = false ∨ valuationOf q 508 = true := by
  have hs : count507 q = (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) + (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]) := List.countP_append (p := literal q) (l₁ := [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (l₂ := [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256])
  have hm := merge_left (literal (valuationOf q) (380)) (literal (valuationOf q) (508)) (countLit q [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]) (countLit q [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]) (count507 q) 2 (meaning380 q) (meaning508 q) hs
  change valuationOf q 380 = false ∨ valuationOf q 508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1096 (q : Snake 81) (h : Conditions q) : valuation q 380 = false ∨ valuation q 508 = true := counterClause1096 (baseVal q)

theorem clause1097 (q : Snake 81) (h : Conditions q) : valuation q 508 = false := by
  rw [value508]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count507 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem counterClause1098 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 1554 = true := by
  have hs : count1554 q = (countLit q [-1]) + (countLit q [-3]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-3])
  have hm := merge_right (literal (valuationOf q) (-3)) (literal (valuationOf q) (1554)) (countLit q [-1]) (countLit q [-3]) (count1554 q) 1 (meaningNeg3 q) (meaning1554 q) hs
  change (! (valuationOf q 3)) = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1098 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 1554 = true := counterClause1098 (baseVal q)

theorem counterClause1099 (q : Nat → Bool) : valuationOf q 7 = true ∨ valuationOf q 1556 = true := by
  have hs : count1556 q = (countLit q [-5]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-5]) (l₂ := [-7])
  have hm := merge_right (literal (valuationOf q) (-7)) (literal (valuationOf q) (1556)) (countLit q [-5]) (countLit q [-7]) (count1556 q) 1 (meaningNeg7 q) (meaning1556 q) hs
  change (! (valuationOf q 7)) = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1099 (q : Snake 81) (h : Conditions q) : valuation q 7 = true ∨ valuation q 1556 = true := counterClause1099 (baseVal q)

theorem counterClause1100 (q : Nat → Bool) : valuationOf q 5 = true ∨ valuationOf q 1556 = true := by
  have hs : count1556 q = (countLit q [-5]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-5]) (l₂ := [-7])
  have hm := merge_left (literal (valuationOf q) (-5)) (literal (valuationOf q) (1556)) (countLit q [-5]) (countLit q [-7]) (count1556 q) 1 (meaningNeg5 q) (meaning1556 q) hs
  change (! (valuationOf q 5)) = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1100 (q : Snake 81) (h : Conditions q) : valuation q 5 = true ∨ valuation q 1556 = true := counterClause1100 (baseVal q)

theorem counterClause1101 (q : Nat → Bool) : valuationOf q 5 = true ∨ valuationOf q 7 = true ∨ valuationOf q 1557 = true := by
  have hs : count1556 q = (countLit q [-5]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-5]) (l₂ := [-7])
  have hm := merge_two (literal (valuationOf q) (-5)) (literal (valuationOf q) (-7)) (literal (valuationOf q) (1557)) (countLit q [-5]) (countLit q [-7]) (count1556 q) 1 1 (meaningNeg5 q) (meaningNeg7 q) (meaning1557 q) hs
  change (! (valuationOf q 5)) = false ∨ (! (valuationOf q 7)) = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1101 (q : Snake 81) (h : Conditions q) : valuation q 5 = true ∨ valuation q 7 = true ∨ valuation q 1557 = true := counterClause1101 (baseVal q)

theorem counterClause1102 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1558 = true := by
  have hs : count1558 q = (countLit q [-1, -3]) + (countLit q [-5, -7]) := List.countP_append (p := literal q) (l₁ := [-1, -3]) (l₂ := [-5, -7])
  have hm := merge_right (literal (valuationOf q) (1556)) (literal (valuationOf q) (1558)) (countLit q [-1, -3]) (countLit q [-5, -7]) (count1558 q) 1 (meaning1556 q) (meaning1558 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1102 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1558 = true := counterClause1102 (baseVal q)

theorem counterClause1103 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1559 = true := by
  have hs : count1558 q = (countLit q [-1, -3]) + (countLit q [-5, -7]) := List.countP_append (p := literal q) (l₁ := [-1, -3]) (l₂ := [-5, -7])
  have hm := merge_right (literal (valuationOf q) (1557)) (literal (valuationOf q) (1559)) (countLit q [-1, -3]) (countLit q [-5, -7]) (count1558 q) 2 (meaning1557 q) (meaning1559 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1103 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1559 = true := counterClause1103 (baseVal q)

theorem counterClause1104 (q : Nat → Bool) : valuationOf q 1554 = false ∨ valuationOf q 1558 = true := by
  have hs : count1558 q = (countLit q [-1, -3]) + (countLit q [-5, -7]) := List.countP_append (p := literal q) (l₁ := [-1, -3]) (l₂ := [-5, -7])
  have hm := merge_left (literal (valuationOf q) (1554)) (literal (valuationOf q) (1558)) (countLit q [-1, -3]) (countLit q [-5, -7]) (count1558 q) 1 (meaning1554 q) (meaning1558 q) hs
  change valuationOf q 1554 = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1104 (q : Snake 81) (h : Conditions q) : valuation q 1554 = false ∨ valuation q 1558 = true := counterClause1104 (baseVal q)

theorem counterClause1105 (q : Nat → Bool) : valuationOf q 1554 = false ∨ valuationOf q 1556 = false ∨ valuationOf q 1559 = true := by
  have hs : count1558 q = (countLit q [-1, -3]) + (countLit q [-5, -7]) := List.countP_append (p := literal q) (l₁ := [-1, -3]) (l₂ := [-5, -7])
  have hm := merge_two (literal (valuationOf q) (1554)) (literal (valuationOf q) (1556)) (literal (valuationOf q) (1559)) (countLit q [-1, -3]) (countLit q [-5, -7]) (count1558 q) 1 1 (meaning1554 q) (meaning1556 q) (meaning1559 q) hs
  change valuationOf q 1554 = false ∨ valuationOf q 1556 = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1105 (q : Snake 81) (h : Conditions q) : valuation q 1554 = false ∨ valuation q 1556 = false ∨ valuation q 1559 = true := counterClause1105 (baseVal q)

theorem counterClause1106 (q : Nat → Bool) : valuationOf q 1554 = false ∨ valuationOf q 1557 = false ∨ valuationOf q 1560 = true := by
  have hs : count1558 q = (countLit q [-1, -3]) + (countLit q [-5, -7]) := List.countP_append (p := literal q) (l₁ := [-1, -3]) (l₂ := [-5, -7])
  have hm := merge_two (literal (valuationOf q) (1554)) (literal (valuationOf q) (1557)) (literal (valuationOf q) (1560)) (countLit q [-1, -3]) (countLit q [-5, -7]) (count1558 q) 1 2 (meaning1554 q) (meaning1557 q) (meaning1560 q) hs
  change valuationOf q 1554 = false ∨ valuationOf q 1557 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1106 (q : Snake 81) (h : Conditions q) : valuation q 1554 = false ∨ valuation q 1557 = false ∨ valuation q 1560 = true := counterClause1106 (baseVal q)

theorem counterClause1107 (q : Nat → Bool) : valuationOf q 10 = true ∨ valuationOf q 1562 = true := by
  have hs : count1562 q = (countLit q [-8]) + (countLit q [-10]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-10])
  have hm := merge_right (literal (valuationOf q) (-10)) (literal (valuationOf q) (1562)) (countLit q [-8]) (countLit q [-10]) (count1562 q) 1 (meaningNeg10 q) (meaning1562 q) hs
  change (! (valuationOf q 10)) = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1107 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 1562 = true := counterClause1107 (baseVal q)

theorem counterClause1108 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 1562 = true := by
  have hs : count1562 q = (countLit q [-8]) + (countLit q [-10]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-10])
  have hm := merge_left (literal (valuationOf q) (-8)) (literal (valuationOf q) (1562)) (countLit q [-8]) (countLit q [-10]) (count1562 q) 1 (meaningNeg8 q) (meaning1562 q) hs
  change (! (valuationOf q 8)) = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1108 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 1562 = true := counterClause1108 (baseVal q)

theorem counterClause1109 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 10 = true ∨ valuationOf q 1563 = true := by
  have hs : count1562 q = (countLit q [-8]) + (countLit q [-10]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-10])
  have hm := merge_two (literal (valuationOf q) (-8)) (literal (valuationOf q) (-10)) (literal (valuationOf q) (1563)) (countLit q [-8]) (countLit q [-10]) (count1562 q) 1 1 (meaningNeg8 q) (meaningNeg10 q) (meaning1563 q) hs
  change (! (valuationOf q 8)) = false ∨ (! (valuationOf q 10)) = false ∨ valuationOf q 1563 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1109 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 10 = true ∨ valuation q 1563 = true := counterClause1109 (baseVal q)

theorem counterClause1110 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 12 = true ∨ valuationOf q 1565 = true := by
  have hs : count1564 q = (countLit q [-11]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-12])
  have hm := merge_two (literal (valuationOf q) (-11)) (literal (valuationOf q) (-12)) (literal (valuationOf q) (1565)) (countLit q [-11]) (countLit q [-12]) (count1564 q) 1 1 (meaningNeg11 q) (meaningNeg12 q) (meaning1565 q) hs
  change (! (valuationOf q 11)) = false ∨ (! (valuationOf q 12)) = false ∨ valuationOf q 1565 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1110 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 12 = true ∨ valuation q 1565 = true := counterClause1110 (baseVal q)

theorem counterClause1111 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1567 = true := by
  have hs : count1566 q = (countLit q [-8, -10]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-8, -10]) (l₂ := [-11, -12])
  have hm := merge_right (literal (valuationOf q) (1565)) (literal (valuationOf q) (1567)) (countLit q [-8, -10]) (countLit q [-11, -12]) (count1566 q) 2 (meaning1565 q) (meaning1567 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1111 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1567 = true := counterClause1111 (baseVal q)

theorem counterClause1112 (q : Nat → Bool) : valuationOf q 1562 = false ∨ valuationOf q 1565 = false ∨ valuationOf q 1568 = true := by
  have hs : count1566 q = (countLit q [-8, -10]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-8, -10]) (l₂ := [-11, -12])
  have hm := merge_two (literal (valuationOf q) (1562)) (literal (valuationOf q) (1565)) (literal (valuationOf q) (1568)) (countLit q [-8, -10]) (countLit q [-11, -12]) (count1566 q) 1 2 (meaning1562 q) (meaning1565 q) (meaning1568 q) hs
  change valuationOf q 1562 = false ∨ valuationOf q 1565 = false ∨ valuationOf q 1568 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1112 (q : Snake 81) (h : Conditions q) : valuation q 1562 = false ∨ valuation q 1565 = false ∨ valuation q 1568 = true := counterClause1112 (baseVal q)

theorem counterClause1113 (q : Nat → Bool) : valuationOf q 1563 = false ∨ valuationOf q 1565 = false ∨ valuationOf q 1569 = true := by
  have hs : count1566 q = (countLit q [-8, -10]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-8, -10]) (l₂ := [-11, -12])
  have hm := merge_two (literal (valuationOf q) (1563)) (literal (valuationOf q) (1565)) (literal (valuationOf q) (1569)) (countLit q [-8, -10]) (countLit q [-11, -12]) (count1566 q) 2 2 (meaning1563 q) (meaning1565 q) (meaning1569 q) hs
  change valuationOf q 1563 = false ∨ valuationOf q 1565 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1113 (q : Snake 81) (h : Conditions q) : valuation q 1563 = false ∨ valuation q 1565 = false ∨ valuation q 1569 = true := counterClause1113 (baseVal q)

theorem counterClause1114 (q : Nat → Bool) : valuationOf q 1567 = false ∨ valuationOf q 1571 = true := by
  have hs : count1570 q = (countLit q [-1, -3, -5, -7]) + (countLit q [-8, -10, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7]) (l₂ := [-8, -10, -11, -12])
  have hm := merge_right (literal (valuationOf q) (1567)) (literal (valuationOf q) (1571)) (countLit q [-1, -3, -5, -7]) (countLit q [-8, -10, -11, -12]) (count1570 q) 2 (meaning1567 q) (meaning1571 q) hs
  change valuationOf q 1567 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1114 (q : Snake 81) (h : Conditions q) : valuation q 1567 = false ∨ valuation q 1571 = true := counterClause1114 (baseVal q)

theorem counterClause1115 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1572 = true := by
  have hs : count1570 q = (countLit q [-1, -3, -5, -7]) + (countLit q [-8, -10, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7]) (l₂ := [-8, -10, -11, -12])
  have hm := merge_right (literal (valuationOf q) (1568)) (literal (valuationOf q) (1572)) (countLit q [-1, -3, -5, -7]) (countLit q [-8, -10, -11, -12]) (count1570 q) 3 (meaning1568 q) (meaning1572 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1115 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1572 = true := counterClause1115 (baseVal q)

theorem counterClause1116 (q : Nat → Bool) : valuationOf q 1569 = false ∨ valuationOf q 1573 = true := by
  have hs : count1570 q = (countLit q [-1, -3, -5, -7]) + (countLit q [-8, -10, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7]) (l₂ := [-8, -10, -11, -12])
  have hm := merge_right (literal (valuationOf q) (1569)) (literal (valuationOf q) (1573)) (countLit q [-1, -3, -5, -7]) (countLit q [-8, -10, -11, -12]) (count1570 q) 4 (meaning1569 q) (meaning1573 q) hs
  change valuationOf q 1569 = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1116 (q : Snake 81) (h : Conditions q) : valuation q 1569 = false ∨ valuation q 1573 = true := counterClause1116 (baseVal q)

theorem counterClause1117 (q : Nat → Bool) : valuationOf q 1558 = false ∨ valuationOf q 1567 = false ∨ valuationOf q 1572 = true := by
  have hs : count1570 q = (countLit q [-1, -3, -5, -7]) + (countLit q [-8, -10, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7]) (l₂ := [-8, -10, -11, -12])
  have hm := merge_two (literal (valuationOf q) (1558)) (literal (valuationOf q) (1567)) (literal (valuationOf q) (1572)) (countLit q [-1, -3, -5, -7]) (countLit q [-8, -10, -11, -12]) (count1570 q) 1 2 (meaning1558 q) (meaning1567 q) (meaning1572 q) hs
  change valuationOf q 1558 = false ∨ valuationOf q 1567 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1117 (q : Snake 81) (h : Conditions q) : valuation q 1558 = false ∨ valuation q 1567 = false ∨ valuation q 1572 = true := counterClause1117 (baseVal q)

theorem counterClause1118 (q : Nat → Bool) : valuationOf q 1558 = false ∨ valuationOf q 1568 = false ∨ valuationOf q 1573 = true := by
  have hs : count1570 q = (countLit q [-1, -3, -5, -7]) + (countLit q [-8, -10, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7]) (l₂ := [-8, -10, -11, -12])
  have hm := merge_two (literal (valuationOf q) (1558)) (literal (valuationOf q) (1568)) (literal (valuationOf q) (1573)) (countLit q [-1, -3, -5, -7]) (countLit q [-8, -10, -11, -12]) (count1570 q) 1 3 (meaning1558 q) (meaning1568 q) (meaning1573 q) hs
  change valuationOf q 1558 = false ∨ valuationOf q 1568 = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1118 (q : Snake 81) (h : Conditions q) : valuation q 1558 = false ∨ valuation q 1568 = false ∨ valuation q 1573 = true := counterClause1118 (baseVal q)

theorem counterClause1119 (q : Nat → Bool) : valuationOf q 1559 = false ∨ valuationOf q 1567 = false ∨ valuationOf q 1573 = true := by
  have hs : count1570 q = (countLit q [-1, -3, -5, -7]) + (countLit q [-8, -10, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7]) (l₂ := [-8, -10, -11, -12])
  have hm := merge_two (literal (valuationOf q) (1559)) (literal (valuationOf q) (1567)) (literal (valuationOf q) (1573)) (countLit q [-1, -3, -5, -7]) (countLit q [-8, -10, -11, -12]) (count1570 q) 2 2 (meaning1559 q) (meaning1567 q) (meaning1573 q) hs
  change valuationOf q 1559 = false ∨ valuationOf q 1567 = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1119 (q : Snake 81) (h : Conditions q) : valuation q 1559 = false ∨ valuation q 1567 = false ∨ valuation q 1573 = true := counterClause1119 (baseVal q)

theorem counterClause1120 (q : Nat → Bool) : valuationOf q 1559 = false ∨ valuationOf q 1568 = false ∨ valuationOf q 1574 = true := by
  have hs : count1570 q = (countLit q [-1, -3, -5, -7]) + (countLit q [-8, -10, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7]) (l₂ := [-8, -10, -11, -12])
  have hm := merge_two (literal (valuationOf q) (1559)) (literal (valuationOf q) (1568)) (literal (valuationOf q) (1574)) (countLit q [-1, -3, -5, -7]) (countLit q [-8, -10, -11, -12]) (count1570 q) 2 3 (meaning1559 q) (meaning1568 q) (meaning1574 q) hs
  change valuationOf q 1559 = false ∨ valuationOf q 1568 = false ∨ valuationOf q 1574 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1120 (q : Snake 81) (h : Conditions q) : valuation q 1559 = false ∨ valuation q 1568 = false ∨ valuation q 1574 = true := counterClause1120 (baseVal q)

theorem block34 (q : Snake 81) (h : Conditions q) : B112E050.Block34 (valuation q) :=
  ⟨clause1089 q h, clause1090 q h, clause1091 q h, clause1092 q h, clause1093 q h, clause1094 q h, clause1095 q h, clause1096 q h, clause1097 q h, clause1098 q h, clause1099 q h, clause1100 q h, clause1101 q h, clause1102 q h, clause1103 q h, clause1104 q h, clause1105 q h, clause1106 q h, clause1107 q h, clause1108 q h, clause1109 q h, clause1110 q h, clause1111 q h, clause1112 q h, clause1113 q h, clause1114 q h, clause1115 q h, clause1116 q h, clause1117 q h, clause1118 q h, clause1119 q h, clause1120 q h⟩

end
end Snake9.Regrowth.E112050
