import E112057Semantics
import B112E057Inputs
namespace Snake9.Regrowth.E112057
noncomputable section
local instance blockDec39 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1249 (q : Nat → Bool) : valuationOf q 497 = false ∨ valuationOf q 499 = true := by
  have hs : count499 q = (countLit q [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237]) + (countLit q [238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253]) := List.countP_append (p := literal q) (l₁ := [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237]) (l₂ := [238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253])
  have hm := merge_right (literal (valuationOf q) (497)) (literal (valuationOf q) (499)) (countLit q [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237]) (countLit q [238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253]) (count499 q) 1 (meaning497 q) (meaning499 q) hs
  change valuationOf q 497 = false ∨ valuationOf q 499 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1249 (q : Snake 81) (h : Conditions q) : valuation q 497 = false ∨ valuation q 499 = true := counterClause1249 (baseVal q)

theorem counterClause1250 (q : Nat → Bool) : valuationOf q 498 = false ∨ valuationOf q 500 = true := by
  have hs : count499 q = (countLit q [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237]) + (countLit q [238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253]) := List.countP_append (p := literal q) (l₁ := [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237]) (l₂ := [238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253])
  have hm := merge_right (literal (valuationOf q) (498)) (literal (valuationOf q) (500)) (countLit q [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237]) (countLit q [238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253]) (count499 q) 2 (meaning498 q) (meaning500 q) hs
  change valuationOf q 498 = false ∨ valuationOf q 500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1250 (q : Snake 81) (h : Conditions q) : valuation q 498 = false ∨ valuation q 500 = true := counterClause1250 (baseVal q)

theorem counterClause1251 (q : Nat → Bool) : valuationOf q 467 = false ∨ valuationOf q 499 = true := by
  have hs : count499 q = (countLit q [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237]) + (countLit q [238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253]) := List.countP_append (p := literal q) (l₁ := [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237]) (l₂ := [238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253])
  have hm := merge_left (literal (valuationOf q) (467)) (literal (valuationOf q) (499)) (countLit q [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237]) (countLit q [238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253]) (count499 q) 1 (meaning467 q) (meaning499 q) hs
  change valuationOf q 467 = false ∨ valuationOf q 499 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1251 (q : Snake 81) (h : Conditions q) : valuation q 467 = false ∨ valuation q 499 = true := counterClause1251 (baseVal q)

theorem counterClause1252 (q : Nat → Bool) : valuationOf q 467 = false ∨ valuationOf q 497 = false ∨ valuationOf q 500 = true := by
  have hs : count499 q = (countLit q [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237]) + (countLit q [238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253]) := List.countP_append (p := literal q) (l₁ := [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237]) (l₂ := [238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253])
  have hm := merge_two (literal (valuationOf q) (467)) (literal (valuationOf q) (497)) (literal (valuationOf q) (500)) (countLit q [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237]) (countLit q [238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253]) (count499 q) 1 1 (meaning467 q) (meaning497 q) (meaning500 q) hs
  change valuationOf q 467 = false ∨ valuationOf q 497 = false ∨ valuationOf q 500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1252 (q : Snake 81) (h : Conditions q) : valuation q 467 = false ∨ valuation q 497 = false ∨ valuation q 500 = true := counterClause1252 (baseVal q)

theorem counterClause1253 (q : Nat → Bool) : valuationOf q 468 = false ∨ valuationOf q 500 = true := by
  have hs : count499 q = (countLit q [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237]) + (countLit q [238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253]) := List.countP_append (p := literal q) (l₁ := [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237]) (l₂ := [238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253])
  have hm := merge_left (literal (valuationOf q) (468)) (literal (valuationOf q) (500)) (countLit q [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237]) (countLit q [238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253]) (count499 q) 2 (meaning468 q) (meaning500 q) hs
  change valuationOf q 468 = false ∨ valuationOf q 500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1253 (q : Snake 81) (h : Conditions q) : valuation q 468 = false ∨ valuation q 500 = true := counterClause1253 (baseVal q)

theorem counterClause1254 (q : Nat → Bool) : valuationOf q 499 = false ∨ valuationOf q 501 = true := by
  have hs : count501 q = (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) + (countLit q [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) (l₂ := [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253])
  have hm := merge_right (literal (valuationOf q) (499)) (literal (valuationOf q) (501)) (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) (countLit q [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253]) (count501 q) 1 (meaning499 q) (meaning501 q) hs
  change valuationOf q 499 = false ∨ valuationOf q 501 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1254 (q : Snake 81) (h : Conditions q) : valuation q 499 = false ∨ valuation q 501 = true := counterClause1254 (baseVal q)

theorem counterClause1255 (q : Nat → Bool) : valuationOf q 500 = false ∨ valuationOf q 502 = true := by
  have hs : count501 q = (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) + (countLit q [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) (l₂ := [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253])
  have hm := merge_right (literal (valuationOf q) (500)) (literal (valuationOf q) (502)) (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) (countLit q [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253]) (count501 q) 2 (meaning500 q) (meaning502 q) hs
  change valuationOf q 500 = false ∨ valuationOf q 502 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1255 (q : Snake 81) (h : Conditions q) : valuation q 500 = false ∨ valuation q 502 = true := counterClause1255 (baseVal q)

theorem counterClause1256 (q : Nat → Bool) : valuationOf q 437 = false ∨ valuationOf q 501 = true := by
  have hs : count501 q = (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) + (countLit q [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) (l₂ := [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253])
  have hm := merge_left (literal (valuationOf q) (437)) (literal (valuationOf q) (501)) (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) (countLit q [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253]) (count501 q) 1 (meaning437 q) (meaning501 q) hs
  change valuationOf q 437 = false ∨ valuationOf q 501 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1256 (q : Snake 81) (h : Conditions q) : valuation q 437 = false ∨ valuation q 501 = true := counterClause1256 (baseVal q)

theorem counterClause1257 (q : Nat → Bool) : valuationOf q 437 = false ∨ valuationOf q 499 = false ∨ valuationOf q 502 = true := by
  have hs : count501 q = (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) + (countLit q [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) (l₂ := [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253])
  have hm := merge_two (literal (valuationOf q) (437)) (literal (valuationOf q) (499)) (literal (valuationOf q) (502)) (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) (countLit q [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253]) (count501 q) 1 1 (meaning437 q) (meaning499 q) (meaning502 q) hs
  change valuationOf q 437 = false ∨ valuationOf q 499 = false ∨ valuationOf q 502 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1257 (q : Snake 81) (h : Conditions q) : valuation q 437 = false ∨ valuation q 499 = false ∨ valuation q 502 = true := counterClause1257 (baseVal q)

theorem counterClause1258 (q : Nat → Bool) : valuationOf q 438 = false ∨ valuationOf q 502 = true := by
  have hs : count501 q = (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) + (countLit q [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253]) := List.countP_append (p := literal q) (l₁ := [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) (l₂ := [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253])
  have hm := merge_left (literal (valuationOf q) (438)) (literal (valuationOf q) (502)) (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]) (countLit q [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253]) (count501 q) 2 (meaning438 q) (meaning502 q) hs
  change valuationOf q 438 = false ∨ valuationOf q 502 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1258 (q : Snake 81) (h : Conditions q) : valuation q 438 = false ∨ valuation q 502 = true := counterClause1258 (baseVal q)

theorem counterClause1259 (q : Nat → Bool) : valuationOf q 502 = false ∨ valuationOf q 504 = true := by
  have hs : count503 q = (countLit q [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) + (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253]) := List.countP_append (p := literal q) (l₁ := [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) (l₂ := [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253])
  have hm := merge_right (literal (valuationOf q) (502)) (literal (valuationOf q) (504)) (countLit q [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253]) (count503 q) 2 (meaning502 q) (meaning504 q) hs
  change valuationOf q 502 = false ∨ valuationOf q 504 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1259 (q : Snake 81) (h : Conditions q) : valuation q 502 = false ∨ valuation q 504 = true := counterClause1259 (baseVal q)

theorem counterClause1260 (q : Nat → Bool) : valuationOf q 377 = false ∨ valuationOf q 501 = false ∨ valuationOf q 504 = true := by
  have hs : count503 q = (countLit q [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) + (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253]) := List.countP_append (p := literal q) (l₁ := [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) (l₂ := [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253])
  have hm := merge_two (literal (valuationOf q) (377)) (literal (valuationOf q) (501)) (literal (valuationOf q) (504)) (countLit q [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253]) (count503 q) 1 1 (meaning377 q) (meaning501 q) (meaning504 q) hs
  change valuationOf q 377 = false ∨ valuationOf q 501 = false ∨ valuationOf q 504 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1260 (q : Snake 81) (h : Conditions q) : valuation q 377 = false ∨ valuation q 501 = false ∨ valuation q 504 = true := counterClause1260 (baseVal q)

theorem counterClause1261 (q : Nat → Bool) : valuationOf q 378 = false ∨ valuationOf q 504 = true := by
  have hs : count503 q = (countLit q [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) + (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253]) := List.countP_append (p := literal q) (l₁ := [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) (l₂ := [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253])
  have hm := merge_left (literal (valuationOf q) (378)) (literal (valuationOf q) (504)) (countLit q [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]) (countLit q [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253]) (count503 q) 2 (meaning378 q) (meaning504 q) hs
  change valuationOf q 378 = false ∨ valuationOf q 504 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1261 (q : Snake 81) (h : Conditions q) : valuation q 378 = false ∨ valuation q 504 = true := counterClause1261 (baseVal q)

theorem clause1262 (q : Snake 81) (h : Conditions q) : valuation q 504 = false := by
  rw [value504]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count503 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem clause1263 (q : Snake 81) (h : Conditions q) : valuation q 128 = true ∨ valuation q 129 = true ∨ valuation q 130 = true ∨ valuation q 131 = true ∨ valuation q 132 = true ∨ valuation q 133 = true ∨ valuation q 134 = true ∨ valuation q 135 = true ∨ valuation q 136 = true ∨ valuation q 137 = true ∨ valuation q 138 = true ∨ valuation q 139 = true ∨ valuation q 140 = true ∨ valuation q 141 = true ∨ valuation q 142 = true ∨ valuation q 143 = true ∨ valuation q 144 = true ∨ valuation q 145 = true ∨ valuation q 146 = true ∨ valuation q 147 = true ∨ valuation q 148 = true ∨ valuation q 149 = true ∨ valuation q 150 = true ∨ valuation q 151 = true ∨ valuation q 152 = true ∨ valuation q 153 = true ∨ valuation q 154 = true ∨ valuation q 155 = true ∨ valuation q 156 = true ∨ valuation q 157 = true ∨ valuation q 158 = true ∨ valuation q 159 = true ∨ valuation q 160 = true ∨ valuation q 161 = true ∨ valuation q 162 = true ∨ valuation q 163 = true ∨ valuation q 164 = true ∨ valuation q 165 = true ∨ valuation q 166 = true ∨ valuation q 167 = true ∨ valuation q 168 = true ∨ valuation q 169 = true ∨ valuation q 170 = true ∨ valuation q 171 = true ∨ valuation q 172 = true ∨ valuation q 173 = true ∨ valuation q 174 = true ∨ valuation q 175 = true ∨ valuation q 176 = true ∨ valuation q 177 = true ∨ valuation q 178 = true ∨ valuation q 179 = true ∨ valuation q 180 = true ∨ valuation q 181 = true ∨ valuation q 182 = true ∨ valuation q 183 = true ∨ valuation q 184 = true ∨ valuation q 185 = true ∨ valuation q 186 = true ∨ valuation q 187 = true ∨ valuation q 188 = true ∨ valuation q 189 = true ∨ valuation q 190 = true ∨ valuation q 191 = true ∨ valuation q 192 = true ∨ valuation q 193 = true ∨ valuation q 194 = true ∨ valuation q 195 = true ∨ valuation q 196 = true ∨ valuation q 197 = true ∨ valuation q 198 = true ∨ valuation q 199 = true ∨ valuation q 200 = true ∨ valuation q 201 = true ∨ valuation q 202 = true ∨ valuation q 203 = true ∨ valuation q 204 = true ∨ valuation q 205 = true ∨ valuation q 206 = true ∨ valuation q 207 = true ∨ valuation q 208 = true ∨ valuation q 209 = true ∨ valuation q 210 = true ∨ valuation q 211 = true ∨ valuation q 212 = true ∨ valuation q 213 = true ∨ valuation q 214 = true ∨ valuation q 215 = true ∨ valuation q 216 = true ∨ valuation q 217 = true ∨ valuation q 218 = true ∨ valuation q 219 = true ∨ valuation q 220 = true ∨ valuation q 221 = true ∨ valuation q 222 = true ∨ valuation q 223 = true ∨ valuation q 224 = true ∨ valuation q 225 = true ∨ valuation q 226 = true ∨ valuation q 227 = true ∨ valuation q 228 = true ∨ valuation q 229 = true ∨ valuation q 230 = true ∨ valuation q 231 = true ∨ valuation q 232 = true ∨ valuation q 233 = true ∨ valuation q 234 = true ∨ valuation q 235 = true ∨ valuation q 236 = true ∨ valuation q 237 = true ∨ valuation q 238 = true ∨ valuation q 239 = true ∨ valuation q 240 = true ∨ valuation q 241 = true ∨ valuation q 242 = true ∨ valuation q 243 = true ∨ valuation q 244 = true ∨ valuation q 245 = true ∨ valuation q 246 = true ∨ valuation q 247 = true ∨ valuation q 248 = true ∨ valuation q 249 = true ∨ valuation q 250 = true ∨ valuation q 251 = true ∨ valuation q 252 = true ∨ valuation q 253 = true := by
  rw [value128, value129, value130, value131, value132, value133, value134, value135, value136, value137, value138, value139, value140, value141, value142, value143, value144, value145, value146, value147, value148, value149, value150, value151, value152, value153, value154, value155, value156, value157, value158, value159, value160, value161, value162, value163, value164, value165, value166, value167, value168, value169, value170, value171, value172, value173, value174, value175, value176, value177, value178, value179, value180, value181, value182, value183, value184, value185, value186, value187, value188, value189, value190, value191, value192, value193, value194, value195, value196, value197, value198, value199, value200, value201, value202, value203, value204, value205, value206, value207, value208, value209, value210, value211, value212, value213, value214, value215, value216, value217, value218, value219, value220, value221, value222, value223, value224, value225, value226, value227, value228, value229, value230, value231, value232, value233, value234, value235, value236, value237, value238, value239, value240, value241, value242, value243, value244, value245, value246, value247, value248, value249, value250, value251, value252, value253]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hg := other_endpoint q others (fun v hv hn => others_mem v (h.covered v hv) (by simpa only [h.head_fixed] using hn))
  simpa only [others, List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem counterClause1264 (q : Nat → Bool) : valuationOf q 4 = true ∨ valuationOf q 867 = true := by
  have hs : count867 q = (countLit q [-1]) + (countLit q [-4]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-4])
  have hm := merge_right (literal (valuationOf q) (-4)) (literal (valuationOf q) (867)) (countLit q [-1]) (countLit q [-4]) (count867 q) 1 (meaningNeg4 q) (meaning867 q) hs
  change (! (valuationOf q 4)) = false ∨ valuationOf q 867 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1264 (q : Snake 81) (h : Conditions q) : valuation q 4 = true ∨ valuation q 867 = true := counterClause1264 (baseVal q)

theorem counterClause1265 (q : Nat → Bool) : valuationOf q 1 = true ∨ valuationOf q 867 = true := by
  have hs : count867 q = (countLit q [-1]) + (countLit q [-4]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-4])
  have hm := merge_left (literal (valuationOf q) (-1)) (literal (valuationOf q) (867)) (countLit q [-1]) (countLit q [-4]) (count867 q) 1 (meaningNeg1 q) (meaning867 q) hs
  change (! (valuationOf q 1)) = false ∨ valuationOf q 867 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1265 (q : Snake 81) (h : Conditions q) : valuation q 1 = true ∨ valuation q 867 = true := counterClause1265 (baseVal q)

theorem counterClause1266 (q : Nat → Bool) : valuationOf q 1 = true ∨ valuationOf q 4 = true ∨ valuationOf q 868 = true := by
  have hs : count867 q = (countLit q [-1]) + (countLit q [-4]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-4])
  have hm := merge_two (literal (valuationOf q) (-1)) (literal (valuationOf q) (-4)) (literal (valuationOf q) (868)) (countLit q [-1]) (countLit q [-4]) (count867 q) 1 1 (meaningNeg1 q) (meaningNeg4 q) (meaning868 q) hs
  change (! (valuationOf q 1)) = false ∨ (! (valuationOf q 4)) = false ∨ valuationOf q 868 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1266 (q : Snake 81) (h : Conditions q) : valuation q 1 = true ∨ valuation q 4 = true ∨ valuation q 868 = true := counterClause1266 (baseVal q)

theorem counterClause1267 (q : Nat → Bool) : valuationOf q 7 = true ∨ valuationOf q 869 = true := by
  have hs : count869 q = (countLit q [-6]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-7])
  have hm := merge_right (literal (valuationOf q) (-7)) (literal (valuationOf q) (869)) (countLit q [-6]) (countLit q [-7]) (count869 q) 1 (meaningNeg7 q) (meaning869 q) hs
  change (! (valuationOf q 7)) = false ∨ valuationOf q 869 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1267 (q : Snake 81) (h : Conditions q) : valuation q 7 = true ∨ valuation q 869 = true := counterClause1267 (baseVal q)

theorem counterClause1268 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 869 = true := by
  have hs : count869 q = (countLit q [-6]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-7])
  have hm := merge_left (literal (valuationOf q) (-6)) (literal (valuationOf q) (869)) (countLit q [-6]) (countLit q [-7]) (count869 q) 1 (meaningNeg6 q) (meaning869 q) hs
  change (! (valuationOf q 6)) = false ∨ valuationOf q 869 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1268 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 869 = true := counterClause1268 (baseVal q)

theorem counterClause1269 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 7 = true ∨ valuationOf q 870 = true := by
  have hs : count869 q = (countLit q [-6]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-7])
  have hm := merge_two (literal (valuationOf q) (-6)) (literal (valuationOf q) (-7)) (literal (valuationOf q) (870)) (countLit q [-6]) (countLit q [-7]) (count869 q) 1 1 (meaningNeg6 q) (meaningNeg7 q) (meaning870 q) hs
  change (! (valuationOf q 6)) = false ∨ (! (valuationOf q 7)) = false ∨ valuationOf q 870 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1269 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 7 = true ∨ valuation q 870 = true := counterClause1269 (baseVal q)

theorem counterClause1270 (q : Nat → Bool) : valuationOf q 869 = false ∨ valuationOf q 871 = true := by
  have hs : count871 q = (countLit q [-1, -4]) + (countLit q [-6, -7]) := List.countP_append (p := literal q) (l₁ := [-1, -4]) (l₂ := [-6, -7])
  have hm := merge_right (literal (valuationOf q) (869)) (literal (valuationOf q) (871)) (countLit q [-1, -4]) (countLit q [-6, -7]) (count871 q) 1 (meaning869 q) (meaning871 q) hs
  change valuationOf q 869 = false ∨ valuationOf q 871 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1270 (q : Snake 81) (h : Conditions q) : valuation q 869 = false ∨ valuation q 871 = true := counterClause1270 (baseVal q)

theorem counterClause1271 (q : Nat → Bool) : valuationOf q 870 = false ∨ valuationOf q 872 = true := by
  have hs : count871 q = (countLit q [-1, -4]) + (countLit q [-6, -7]) := List.countP_append (p := literal q) (l₁ := [-1, -4]) (l₂ := [-6, -7])
  have hm := merge_right (literal (valuationOf q) (870)) (literal (valuationOf q) (872)) (countLit q [-1, -4]) (countLit q [-6, -7]) (count871 q) 2 (meaning870 q) (meaning872 q) hs
  change valuationOf q 870 = false ∨ valuationOf q 872 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1271 (q : Snake 81) (h : Conditions q) : valuation q 870 = false ∨ valuation q 872 = true := counterClause1271 (baseVal q)

theorem counterClause1272 (q : Nat → Bool) : valuationOf q 867 = false ∨ valuationOf q 871 = true := by
  have hs : count871 q = (countLit q [-1, -4]) + (countLit q [-6, -7]) := List.countP_append (p := literal q) (l₁ := [-1, -4]) (l₂ := [-6, -7])
  have hm := merge_left (literal (valuationOf q) (867)) (literal (valuationOf q) (871)) (countLit q [-1, -4]) (countLit q [-6, -7]) (count871 q) 1 (meaning867 q) (meaning871 q) hs
  change valuationOf q 867 = false ∨ valuationOf q 871 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1272 (q : Snake 81) (h : Conditions q) : valuation q 867 = false ∨ valuation q 871 = true := counterClause1272 (baseVal q)

theorem counterClause1273 (q : Nat → Bool) : valuationOf q 867 = false ∨ valuationOf q 869 = false ∨ valuationOf q 872 = true := by
  have hs : count871 q = (countLit q [-1, -4]) + (countLit q [-6, -7]) := List.countP_append (p := literal q) (l₁ := [-1, -4]) (l₂ := [-6, -7])
  have hm := merge_two (literal (valuationOf q) (867)) (literal (valuationOf q) (869)) (literal (valuationOf q) (872)) (countLit q [-1, -4]) (countLit q [-6, -7]) (count871 q) 1 1 (meaning867 q) (meaning869 q) (meaning872 q) hs
  change valuationOf q 867 = false ∨ valuationOf q 869 = false ∨ valuationOf q 872 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1273 (q : Snake 81) (h : Conditions q) : valuation q 867 = false ∨ valuation q 869 = false ∨ valuation q 872 = true := counterClause1273 (baseVal q)

theorem counterClause1274 (q : Nat → Bool) : valuationOf q 867 = false ∨ valuationOf q 870 = false ∨ valuationOf q 873 = true := by
  have hs : count871 q = (countLit q [-1, -4]) + (countLit q [-6, -7]) := List.countP_append (p := literal q) (l₁ := [-1, -4]) (l₂ := [-6, -7])
  have hm := merge_two (literal (valuationOf q) (867)) (literal (valuationOf q) (870)) (literal (valuationOf q) (873)) (countLit q [-1, -4]) (countLit q [-6, -7]) (count871 q) 1 2 (meaning867 q) (meaning870 q) (meaning873 q) hs
  change valuationOf q 867 = false ∨ valuationOf q 870 = false ∨ valuationOf q 873 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1274 (q : Snake 81) (h : Conditions q) : valuation q 867 = false ∨ valuation q 870 = false ∨ valuation q 873 = true := counterClause1274 (baseVal q)

theorem counterClause1275 (q : Nat → Bool) : valuationOf q 868 = false ∨ valuationOf q 872 = true := by
  have hs : count871 q = (countLit q [-1, -4]) + (countLit q [-6, -7]) := List.countP_append (p := literal q) (l₁ := [-1, -4]) (l₂ := [-6, -7])
  have hm := merge_left (literal (valuationOf q) (868)) (literal (valuationOf q) (872)) (countLit q [-1, -4]) (countLit q [-6, -7]) (count871 q) 2 (meaning868 q) (meaning872 q) hs
  change valuationOf q 868 = false ∨ valuationOf q 872 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1275 (q : Snake 81) (h : Conditions q) : valuation q 868 = false ∨ valuation q 872 = true := counterClause1275 (baseVal q)

theorem counterClause1276 (q : Nat → Bool) : valuationOf q 868 = false ∨ valuationOf q 869 = false ∨ valuationOf q 873 = true := by
  have hs : count871 q = (countLit q [-1, -4]) + (countLit q [-6, -7]) := List.countP_append (p := literal q) (l₁ := [-1, -4]) (l₂ := [-6, -7])
  have hm := merge_two (literal (valuationOf q) (868)) (literal (valuationOf q) (869)) (literal (valuationOf q) (873)) (countLit q [-1, -4]) (countLit q [-6, -7]) (count871 q) 2 1 (meaning868 q) (meaning869 q) (meaning873 q) hs
  change valuationOf q 868 = false ∨ valuationOf q 869 = false ∨ valuationOf q 873 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1276 (q : Snake 81) (h : Conditions q) : valuation q 868 = false ∨ valuation q 869 = false ∨ valuation q 873 = true := counterClause1276 (baseVal q)

theorem counterClause1277 (q : Nat → Bool) : valuationOf q 868 = false ∨ valuationOf q 870 = false ∨ valuationOf q 874 = true := by
  have hs : count871 q = (countLit q [-1, -4]) + (countLit q [-6, -7]) := List.countP_append (p := literal q) (l₁ := [-1, -4]) (l₂ := [-6, -7])
  have hm := merge_two (literal (valuationOf q) (868)) (literal (valuationOf q) (870)) (literal (valuationOf q) (874)) (countLit q [-1, -4]) (countLit q [-6, -7]) (count871 q) 2 2 (meaning868 q) (meaning870 q) (meaning874 q) hs
  change valuationOf q 868 = false ∨ valuationOf q 870 = false ∨ valuationOf q 874 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1277 (q : Snake 81) (h : Conditions q) : valuation q 868 = false ∨ valuation q 870 = false ∨ valuation q 874 = true := counterClause1277 (baseVal q)

theorem counterClause1278 (q : Nat → Bool) : valuationOf q 10 = true ∨ valuationOf q 875 = true := by
  have hs : count875 q = (countLit q [-9]) + (countLit q [-10]) := List.countP_append (p := literal q) (l₁ := [-9]) (l₂ := [-10])
  have hm := merge_right (literal (valuationOf q) (-10)) (literal (valuationOf q) (875)) (countLit q [-9]) (countLit q [-10]) (count875 q) 1 (meaningNeg10 q) (meaning875 q) hs
  change (! (valuationOf q 10)) = false ∨ valuationOf q 875 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1278 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 875 = true := counterClause1278 (baseVal q)

theorem counterClause1279 (q : Nat → Bool) : valuationOf q 9 = true ∨ valuationOf q 875 = true := by
  have hs : count875 q = (countLit q [-9]) + (countLit q [-10]) := List.countP_append (p := literal q) (l₁ := [-9]) (l₂ := [-10])
  have hm := merge_left (literal (valuationOf q) (-9)) (literal (valuationOf q) (875)) (countLit q [-9]) (countLit q [-10]) (count875 q) 1 (meaningNeg9 q) (meaning875 q) hs
  change (! (valuationOf q 9)) = false ∨ valuationOf q 875 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1279 (q : Snake 81) (h : Conditions q) : valuation q 9 = true ∨ valuation q 875 = true := counterClause1279 (baseVal q)

theorem counterClause1280 (q : Nat → Bool) : valuationOf q 9 = true ∨ valuationOf q 10 = true ∨ valuationOf q 876 = true := by
  have hs : count875 q = (countLit q [-9]) + (countLit q [-10]) := List.countP_append (p := literal q) (l₁ := [-9]) (l₂ := [-10])
  have hm := merge_two (literal (valuationOf q) (-9)) (literal (valuationOf q) (-10)) (literal (valuationOf q) (876)) (countLit q [-9]) (countLit q [-10]) (count875 q) 1 1 (meaningNeg9 q) (meaningNeg10 q) (meaning876 q) hs
  change (! (valuationOf q 9)) = false ∨ (! (valuationOf q 10)) = false ∨ valuationOf q 876 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1280 (q : Snake 81) (h : Conditions q) : valuation q 9 = true ∨ valuation q 10 = true ∨ valuation q 876 = true := counterClause1280 (baseVal q)

theorem block39 (q : Snake 81) (h : Conditions q) : B112E057.Block39 (valuation q) :=
  ⟨clause1249 q h, clause1250 q h, clause1251 q h, clause1252 q h, clause1253 q h, clause1254 q h, clause1255 q h, clause1256 q h, clause1257 q h, clause1258 q h, clause1259 q h, clause1260 q h, clause1261 q h, clause1262 q h, clause1263 q h, clause1264 q h, clause1265 q h, clause1266 q h, clause1267 q h, clause1268 q h, clause1269 q h, clause1270 q h, clause1271 q h, clause1272 q h, clause1273 q h, clause1274 q h, clause1275 q h, clause1276 q h, clause1277 q h, clause1278 q h, clause1279 q h, clause1280 q h⟩

end
end Snake9.Regrowth.E112057
