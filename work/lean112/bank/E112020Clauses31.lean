import E112020Semantics
import B112E020Inputs
namespace Snake9.Regrowth.E112020
noncomputable section
local instance blockDec31 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause993 (q : Nat → Bool) : valuationOf q 247 = false ∨ valuationOf q 479 = true := by
  have hs : count479 q = (countLit q [247]) + (countLit q [248]) := List.countP_append (p := literal q) (l₁ := [247]) (l₂ := [248])
  have hm := merge_left (literal (valuationOf q) (247)) (literal (valuationOf q) (479)) (countLit q [247]) (countLit q [248]) (count479 q) 1 (meaning247 q) (meaning479 q) hs
  change valuationOf q 247 = false ∨ valuationOf q 479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause993 (q : Snake 81) (h : Conditions q) : valuation q 247 = false ∨ valuation q 479 = true := counterClause993 (baseVal q)

theorem counterClause994 (q : Nat → Bool) : valuationOf q 479 = false ∨ valuationOf q 481 = true := by
  have hs : count481 q = (countLit q [245, 246]) + (countLit q [247, 248]) := List.countP_append (p := literal q) (l₁ := [245, 246]) (l₂ := [247, 248])
  have hm := merge_right (literal (valuationOf q) (479)) (literal (valuationOf q) (481)) (countLit q [245, 246]) (countLit q [247, 248]) (count481 q) 1 (meaning479 q) (meaning481 q) hs
  change valuationOf q 479 = false ∨ valuationOf q 481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause994 (q : Snake 81) (h : Conditions q) : valuation q 479 = false ∨ valuation q 481 = true := counterClause994 (baseVal q)

theorem counterClause995 (q : Nat → Bool) : valuationOf q 481 = false ∨ valuationOf q 483 = true := by
  have hs : count483 q = (countLit q [241, 242, 243, 244]) + (countLit q [245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [241, 242, 243, 244]) (l₂ := [245, 246, 247, 248])
  have hm := merge_right (literal (valuationOf q) (481)) (literal (valuationOf q) (483)) (countLit q [241, 242, 243, 244]) (countLit q [245, 246, 247, 248]) (count483 q) 1 (meaning481 q) (meaning483 q) hs
  change valuationOf q 481 = false ∨ valuationOf q 483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause995 (q : Snake 81) (h : Conditions q) : valuation q 481 = false ∨ valuation q 483 = true := counterClause995 (baseVal q)

theorem counterClause996 (q : Nat → Bool) : valuationOf q 475 = false ∨ valuationOf q 483 = true := by
  have hs : count483 q = (countLit q [241, 242, 243, 244]) + (countLit q [245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [241, 242, 243, 244]) (l₂ := [245, 246, 247, 248])
  have hm := merge_left (literal (valuationOf q) (475)) (literal (valuationOf q) (483)) (countLit q [241, 242, 243, 244]) (countLit q [245, 246, 247, 248]) (count483 q) 1 (meaning475 q) (meaning483 q) hs
  change valuationOf q 475 = false ∨ valuationOf q 483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause996 (q : Snake 81) (h : Conditions q) : valuation q 475 = false ∨ valuation q 483 = true := counterClause996 (baseVal q)

theorem counterClause997 (q : Nat → Bool) : valuationOf q 475 = false ∨ valuationOf q 481 = false ∨ valuationOf q 484 = true := by
  have hs : count483 q = (countLit q [241, 242, 243, 244]) + (countLit q [245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [241, 242, 243, 244]) (l₂ := [245, 246, 247, 248])
  have hm := merge_two (literal (valuationOf q) (475)) (literal (valuationOf q) (481)) (literal (valuationOf q) (484)) (countLit q [241, 242, 243, 244]) (countLit q [245, 246, 247, 248]) (count483 q) 1 1 (meaning475 q) (meaning481 q) (meaning484 q) hs
  change valuationOf q 475 = false ∨ valuationOf q 481 = false ∨ valuationOf q 484 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause997 (q : Snake 81) (h : Conditions q) : valuation q 475 = false ∨ valuation q 481 = false ∨ valuation q 484 = true := counterClause997 (baseVal q)

theorem counterClause998 (q : Nat → Bool) : valuationOf q 483 = false ∨ valuationOf q 485 = true := by
  have hs : count485 q = (countLit q [233, 234, 235, 236, 237, 238, 239, 240]) + (countLit q [241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [233, 234, 235, 236, 237, 238, 239, 240]) (l₂ := [241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_right (literal (valuationOf q) (483)) (literal (valuationOf q) (485)) (countLit q [233, 234, 235, 236, 237, 238, 239, 240]) (countLit q [241, 242, 243, 244, 245, 246, 247, 248]) (count485 q) 1 (meaning483 q) (meaning485 q) hs
  change valuationOf q 483 = false ∨ valuationOf q 485 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause998 (q : Snake 81) (h : Conditions q) : valuation q 483 = false ∨ valuation q 485 = true := counterClause998 (baseVal q)

theorem counterClause999 (q : Nat → Bool) : valuationOf q 484 = false ∨ valuationOf q 486 = true := by
  have hs : count485 q = (countLit q [233, 234, 235, 236, 237, 238, 239, 240]) + (countLit q [241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [233, 234, 235, 236, 237, 238, 239, 240]) (l₂ := [241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_right (literal (valuationOf q) (484)) (literal (valuationOf q) (486)) (countLit q [233, 234, 235, 236, 237, 238, 239, 240]) (countLit q [241, 242, 243, 244, 245, 246, 247, 248]) (count485 q) 2 (meaning484 q) (meaning486 q) hs
  change valuationOf q 484 = false ∨ valuationOf q 486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause999 (q : Snake 81) (h : Conditions q) : valuation q 484 = false ∨ valuation q 486 = true := counterClause999 (baseVal q)

theorem counterClause1000 (q : Nat → Bool) : valuationOf q 469 = false ∨ valuationOf q 485 = true := by
  have hs : count485 q = (countLit q [233, 234, 235, 236, 237, 238, 239, 240]) + (countLit q [241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [233, 234, 235, 236, 237, 238, 239, 240]) (l₂ := [241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_left (literal (valuationOf q) (469)) (literal (valuationOf q) (485)) (countLit q [233, 234, 235, 236, 237, 238, 239, 240]) (countLit q [241, 242, 243, 244, 245, 246, 247, 248]) (count485 q) 1 (meaning469 q) (meaning485 q) hs
  change valuationOf q 469 = false ∨ valuationOf q 485 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1000 (q : Snake 81) (h : Conditions q) : valuation q 469 = false ∨ valuation q 485 = true := counterClause1000 (baseVal q)

theorem counterClause1001 (q : Nat → Bool) : valuationOf q 469 = false ∨ valuationOf q 483 = false ∨ valuationOf q 486 = true := by
  have hs : count485 q = (countLit q [233, 234, 235, 236, 237, 238, 239, 240]) + (countLit q [241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [233, 234, 235, 236, 237, 238, 239, 240]) (l₂ := [241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_two (literal (valuationOf q) (469)) (literal (valuationOf q) (483)) (literal (valuationOf q) (486)) (countLit q [233, 234, 235, 236, 237, 238, 239, 240]) (countLit q [241, 242, 243, 244, 245, 246, 247, 248]) (count485 q) 1 1 (meaning469 q) (meaning483 q) (meaning486 q) hs
  change valuationOf q 469 = false ∨ valuationOf q 483 = false ∨ valuationOf q 486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1001 (q : Snake 81) (h : Conditions q) : valuation q 469 = false ∨ valuation q 483 = false ∨ valuation q 486 = true := counterClause1001 (baseVal q)

theorem counterClause1002 (q : Nat → Bool) : valuationOf q 485 = false ∨ valuationOf q 487 = true := by
  have hs : count487 q = (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) + (countLit q [233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (l₂ := [233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_right (literal (valuationOf q) (485)) (literal (valuationOf q) (487)) (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (countLit q [233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) (count487 q) 1 (meaning485 q) (meaning487 q) hs
  change valuationOf q 485 = false ∨ valuationOf q 487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1002 (q : Snake 81) (h : Conditions q) : valuation q 485 = false ∨ valuation q 487 = true := counterClause1002 (baseVal q)

theorem counterClause1003 (q : Nat → Bool) : valuationOf q 486 = false ∨ valuationOf q 488 = true := by
  have hs : count487 q = (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) + (countLit q [233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (l₂ := [233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_right (literal (valuationOf q) (486)) (literal (valuationOf q) (488)) (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (countLit q [233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) (count487 q) 2 (meaning486 q) (meaning488 q) hs
  change valuationOf q 486 = false ∨ valuationOf q 488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1003 (q : Snake 81) (h : Conditions q) : valuation q 486 = false ∨ valuation q 488 = true := counterClause1003 (baseVal q)

theorem counterClause1004 (q : Nat → Bool) : valuationOf q 455 = false ∨ valuationOf q 487 = true := by
  have hs : count487 q = (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) + (countLit q [233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (l₂ := [233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_left (literal (valuationOf q) (455)) (literal (valuationOf q) (487)) (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (countLit q [233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) (count487 q) 1 (meaning455 q) (meaning487 q) hs
  change valuationOf q 455 = false ∨ valuationOf q 487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1004 (q : Snake 81) (h : Conditions q) : valuation q 455 = false ∨ valuation q 487 = true := counterClause1004 (baseVal q)

theorem counterClause1005 (q : Nat → Bool) : valuationOf q 455 = false ∨ valuationOf q 485 = false ∨ valuationOf q 488 = true := by
  have hs : count487 q = (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) + (countLit q [233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (l₂ := [233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_two (literal (valuationOf q) (455)) (literal (valuationOf q) (485)) (literal (valuationOf q) (488)) (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (countLit q [233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) (count487 q) 1 1 (meaning455 q) (meaning485 q) (meaning488 q) hs
  change valuationOf q 455 = false ∨ valuationOf q 485 = false ∨ valuationOf q 488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1005 (q : Snake 81) (h : Conditions q) : valuation q 455 = false ∨ valuation q 485 = false ∨ valuation q 488 = true := counterClause1005 (baseVal q)

theorem counterClause1006 (q : Nat → Bool) : valuationOf q 456 = false ∨ valuationOf q 488 = true := by
  have hs : count487 q = (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) + (countLit q [233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (l₂ := [233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_left (literal (valuationOf q) (456)) (literal (valuationOf q) (488)) (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]) (countLit q [233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) (count487 q) 2 (meaning456 q) (meaning488 q) hs
  change valuationOf q 456 = false ∨ valuationOf q 488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1006 (q : Snake 81) (h : Conditions q) : valuation q 456 = false ∨ valuation q 488 = true := counterClause1006 (baseVal q)

theorem counterClause1007 (q : Nat → Bool) : valuationOf q 487 = false ∨ valuationOf q 489 = true := by
  have hs : count489 q = (countLit q [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) + (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) (l₂ := [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_right (literal (valuationOf q) (487)) (literal (valuationOf q) (489)) (countLit q [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) (count489 q) 1 (meaning487 q) (meaning489 q) hs
  change valuationOf q 487 = false ∨ valuationOf q 489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1007 (q : Snake 81) (h : Conditions q) : valuation q 487 = false ∨ valuation q 489 = true := counterClause1007 (baseVal q)

theorem counterClause1008 (q : Nat → Bool) : valuationOf q 488 = false ∨ valuationOf q 490 = true := by
  have hs : count489 q = (countLit q [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) + (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) (l₂ := [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_right (literal (valuationOf q) (488)) (literal (valuationOf q) (490)) (countLit q [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) (count489 q) 2 (meaning488 q) (meaning490 q) hs
  change valuationOf q 488 = false ∨ valuationOf q 490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1008 (q : Snake 81) (h : Conditions q) : valuation q 488 = false ∨ valuation q 490 = true := counterClause1008 (baseVal q)

theorem counterClause1009 (q : Nat → Bool) : valuationOf q 427 = false ∨ valuationOf q 489 = true := by
  have hs : count489 q = (countLit q [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) + (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) (l₂ := [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_left (literal (valuationOf q) (427)) (literal (valuationOf q) (489)) (countLit q [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) (count489 q) 1 (meaning427 q) (meaning489 q) hs
  change valuationOf q 427 = false ∨ valuationOf q 489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1009 (q : Snake 81) (h : Conditions q) : valuation q 427 = false ∨ valuation q 489 = true := counterClause1009 (baseVal q)

theorem counterClause1010 (q : Nat → Bool) : valuationOf q 427 = false ∨ valuationOf q 487 = false ∨ valuationOf q 490 = true := by
  have hs : count489 q = (countLit q [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) + (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) (l₂ := [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_two (literal (valuationOf q) (427)) (literal (valuationOf q) (487)) (literal (valuationOf q) (490)) (countLit q [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) (count489 q) 1 1 (meaning427 q) (meaning487 q) (meaning490 q) hs
  change valuationOf q 427 = false ∨ valuationOf q 487 = false ∨ valuationOf q 490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1010 (q : Snake 81) (h : Conditions q) : valuation q 427 = false ∨ valuation q 487 = false ∨ valuation q 490 = true := counterClause1010 (baseVal q)

theorem counterClause1011 (q : Nat → Bool) : valuationOf q 428 = false ∨ valuationOf q 490 = true := by
  have hs : count489 q = (countLit q [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) + (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) (l₂ := [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_left (literal (valuationOf q) (428)) (literal (valuationOf q) (490)) (countLit q [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]) (countLit q [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) (count489 q) 2 (meaning428 q) (meaning490 q) hs
  change valuationOf q 428 = false ∨ valuationOf q 490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1011 (q : Snake 81) (h : Conditions q) : valuation q 428 = false ∨ valuation q 490 = true := counterClause1011 (baseVal q)

theorem counterClause1012 (q : Nat → Bool) : valuationOf q 490 = false ∨ valuationOf q 492 = true := by
  have hs : count491 q = (countLit q [125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) + (countLit q [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) (l₂ := [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_right (literal (valuationOf q) (490)) (literal (valuationOf q) (492)) (countLit q [125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) (countLit q [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) (count491 q) 2 (meaning490 q) (meaning492 q) hs
  change valuationOf q 490 = false ∨ valuationOf q 492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1012 (q : Snake 81) (h : Conditions q) : valuation q 490 = false ∨ valuation q 492 = true := counterClause1012 (baseVal q)

theorem counterClause1013 (q : Nat → Bool) : valuationOf q 367 = false ∨ valuationOf q 489 = false ∨ valuationOf q 492 = true := by
  have hs : count491 q = (countLit q [125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) + (countLit q [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) (l₂ := [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_two (literal (valuationOf q) (367)) (literal (valuationOf q) (489)) (literal (valuationOf q) (492)) (countLit q [125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) (countLit q [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) (count491 q) 1 1 (meaning367 q) (meaning489 q) (meaning492 q) hs
  change valuationOf q 367 = false ∨ valuationOf q 489 = false ∨ valuationOf q 492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1013 (q : Snake 81) (h : Conditions q) : valuation q 367 = false ∨ valuation q 489 = false ∨ valuation q 492 = true := counterClause1013 (baseVal q)

theorem counterClause1014 (q : Nat → Bool) : valuationOf q 368 = false ∨ valuationOf q 492 = true := by
  have hs : count491 q = (countLit q [125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) + (countLit q [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) (l₂ := [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_left (literal (valuationOf q) (368)) (literal (valuationOf q) (492)) (countLit q [125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) (countLit q [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) (count491 q) 2 (meaning368 q) (meaning492 q) hs
  change valuationOf q 368 = false ∨ valuationOf q 492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1014 (q : Snake 81) (h : Conditions q) : valuation q 368 = false ∨ valuation q 492 = true := counterClause1014 (baseVal q)

theorem clause1015 (q : Snake 81) (h : Conditions q) : valuation q 492 = false := by
  rw [value492]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count491 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem counterClause1016 (q : Nat → Bool) : valuationOf q 5 = true ∨ valuationOf q 1497 = true := by
  have hs : count1497 q = (countLit q [-3]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-5])
  have hm := merge_right (literal (valuationOf q) (-5)) (literal (valuationOf q) (1497)) (countLit q [-3]) (countLit q [-5]) (count1497 q) 1 (meaningNeg5 q) (meaning1497 q) hs
  change (! (valuationOf q 5)) = false ∨ valuationOf q 1497 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1016 (q : Snake 81) (h : Conditions q) : valuation q 5 = true ∨ valuation q 1497 = true := counterClause1016 (baseVal q)

theorem counterClause1017 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 1497 = true := by
  have hs : count1497 q = (countLit q [-3]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-5])
  have hm := merge_left (literal (valuationOf q) (-3)) (literal (valuationOf q) (1497)) (countLit q [-3]) (countLit q [-5]) (count1497 q) 1 (meaningNeg3 q) (meaning1497 q) hs
  change (! (valuationOf q 3)) = false ∨ valuationOf q 1497 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1017 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 1497 = true := counterClause1017 (baseVal q)

theorem counterClause1018 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 5 = true ∨ valuationOf q 1498 = true := by
  have hs : count1497 q = (countLit q [-3]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-5])
  have hm := merge_two (literal (valuationOf q) (-3)) (literal (valuationOf q) (-5)) (literal (valuationOf q) (1498)) (countLit q [-3]) (countLit q [-5]) (count1497 q) 1 1 (meaningNeg3 q) (meaningNeg5 q) (meaning1498 q) hs
  change (! (valuationOf q 3)) = false ∨ (! (valuationOf q 5)) = false ∨ valuationOf q 1498 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1018 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 5 = true ∨ valuation q 1498 = true := counterClause1018 (baseVal q)

theorem counterClause1019 (q : Nat → Bool) : valuationOf q 1497 = false ∨ valuationOf q 1499 = true := by
  have hs : count1499 q = (countLit q [-2]) + (countLit q [-3, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3, -5])
  have hm := merge_right (literal (valuationOf q) (1497)) (literal (valuationOf q) (1499)) (countLit q [-2]) (countLit q [-3, -5]) (count1499 q) 1 (meaning1497 q) (meaning1499 q) hs
  change valuationOf q 1497 = false ∨ valuationOf q 1499 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1019 (q : Snake 81) (h : Conditions q) : valuation q 1497 = false ∨ valuation q 1499 = true := counterClause1019 (baseVal q)

theorem counterClause1020 (q : Nat → Bool) : valuationOf q 1498 = false ∨ valuationOf q 1500 = true := by
  have hs : count1499 q = (countLit q [-2]) + (countLit q [-3, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3, -5])
  have hm := merge_right (literal (valuationOf q) (1498)) (literal (valuationOf q) (1500)) (countLit q [-2]) (countLit q [-3, -5]) (count1499 q) 2 (meaning1498 q) (meaning1500 q) hs
  change valuationOf q 1498 = false ∨ valuationOf q 1500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1020 (q : Snake 81) (h : Conditions q) : valuation q 1498 = false ∨ valuation q 1500 = true := counterClause1020 (baseVal q)

theorem counterClause1021 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 1502 = true := by
  have hs : count1502 q = (countLit q [-6]) + (countLit q [-8]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-8])
  have hm := merge_right (literal (valuationOf q) (-8)) (literal (valuationOf q) (1502)) (countLit q [-6]) (countLit q [-8]) (count1502 q) 1 (meaningNeg8 q) (meaning1502 q) hs
  change (! (valuationOf q 8)) = false ∨ valuationOf q 1502 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1021 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 1502 = true := counterClause1021 (baseVal q)

theorem counterClause1022 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 1502 = true := by
  have hs : count1502 q = (countLit q [-6]) + (countLit q [-8]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-8])
  have hm := merge_left (literal (valuationOf q) (-6)) (literal (valuationOf q) (1502)) (countLit q [-6]) (countLit q [-8]) (count1502 q) 1 (meaningNeg6 q) (meaning1502 q) hs
  change (! (valuationOf q 6)) = false ∨ valuationOf q 1502 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1022 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 1502 = true := counterClause1022 (baseVal q)

theorem counterClause1023 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 8 = true ∨ valuationOf q 1503 = true := by
  have hs : count1502 q = (countLit q [-6]) + (countLit q [-8]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-8])
  have hm := merge_two (literal (valuationOf q) (-6)) (literal (valuationOf q) (-8)) (literal (valuationOf q) (1503)) (countLit q [-6]) (countLit q [-8]) (count1502 q) 1 1 (meaningNeg6 q) (meaningNeg8 q) (meaning1503 q) hs
  change (! (valuationOf q 6)) = false ∨ (! (valuationOf q 8)) = false ∨ valuationOf q 1503 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1023 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 8 = true ∨ valuation q 1503 = true := counterClause1023 (baseVal q)

theorem counterClause1024 (q : Nat → Bool) : valuationOf q 12 = true ∨ valuationOf q 1504 = true := by
  have hs : count1504 q = (countLit q [-9]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-9]) (l₂ := [-12])
  have hm := merge_right (literal (valuationOf q) (-12)) (literal (valuationOf q) (1504)) (countLit q [-9]) (countLit q [-12]) (count1504 q) 1 (meaningNeg12 q) (meaning1504 q) hs
  change (! (valuationOf q 12)) = false ∨ valuationOf q 1504 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1024 (q : Snake 81) (h : Conditions q) : valuation q 12 = true ∨ valuation q 1504 = true := counterClause1024 (baseVal q)

theorem block31 (q : Snake 81) (h : Conditions q) : B112E020.Block31 (valuation q) :=
  ⟨clause993 q h, clause994 q h, clause995 q h, clause996 q h, clause997 q h, clause998 q h, clause999 q h, clause1000 q h, clause1001 q h, clause1002 q h, clause1003 q h, clause1004 q h, clause1005 q h, clause1006 q h, clause1007 q h, clause1008 q h, clause1009 q h, clause1010 q h, clause1011 q h, clause1012 q h, clause1013 q h, clause1014 q h, clause1015 q h, clause1016 q h, clause1017 q h, clause1018 q h, clause1019 q h, clause1020 q h, clause1021 q h, clause1022 q h, clause1023 q h, clause1024 q h⟩

end
end Snake9.Regrowth.E112020
