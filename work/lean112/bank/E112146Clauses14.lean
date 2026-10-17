import E112146Semantics
import B112E146Inputs
namespace Snake9.Regrowth.E112146
noncomputable section
local instance blockDec14 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause449 (q : Nat → Bool) : valuationOf q 415 = false ∨ valuationOf q 417 = true := by
  have hs : count417 q = (countLit q [200, 201, 202, 203, 204, 205, 206]) + (countLit q [207, 208, 209, 210, 211, 212, 213]) := List.countP_append (p := literal q) (l₁ := [200, 201, 202, 203, 204, 205, 206]) (l₂ := [207, 208, 209, 210, 211, 212, 213])
  have hm := merge_right (literal (valuationOf q) (415)) (literal (valuationOf q) (417)) (countLit q [200, 201, 202, 203, 204, 205, 206]) (countLit q [207, 208, 209, 210, 211, 212, 213]) (count417 q) 1 (meaning415 q) (meaning417 q) hs
  change valuationOf q 415 = false ∨ valuationOf q 417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause449 (q : Snake 81) (h : Conditions q) : valuation q 415 = false ∨ valuation q 417 = true := counterClause449 (baseVal q)

theorem counterClause450 (q : Nat → Bool) : valuationOf q 403 = false ∨ valuationOf q 417 = true := by
  have hs : count417 q = (countLit q [200, 201, 202, 203, 204, 205, 206]) + (countLit q [207, 208, 209, 210, 211, 212, 213]) := List.countP_append (p := literal q) (l₁ := [200, 201, 202, 203, 204, 205, 206]) (l₂ := [207, 208, 209, 210, 211, 212, 213])
  have hm := merge_left (literal (valuationOf q) (403)) (literal (valuationOf q) (417)) (countLit q [200, 201, 202, 203, 204, 205, 206]) (countLit q [207, 208, 209, 210, 211, 212, 213]) (count417 q) 1 (meaning403 q) (meaning417 q) hs
  change valuationOf q 403 = false ∨ valuationOf q 417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause450 (q : Snake 81) (h : Conditions q) : valuation q 403 = false ∨ valuation q 417 = true := counterClause450 (baseVal q)

theorem counterClause451 (q : Nat → Bool) : valuationOf q 403 = false ∨ valuationOf q 415 = false ∨ valuationOf q 418 = true := by
  have hs : count417 q = (countLit q [200, 201, 202, 203, 204, 205, 206]) + (countLit q [207, 208, 209, 210, 211, 212, 213]) := List.countP_append (p := literal q) (l₁ := [200, 201, 202, 203, 204, 205, 206]) (l₂ := [207, 208, 209, 210, 211, 212, 213])
  have hm := merge_two (literal (valuationOf q) (403)) (literal (valuationOf q) (415)) (literal (valuationOf q) (418)) (countLit q [200, 201, 202, 203, 204, 205, 206]) (countLit q [207, 208, 209, 210, 211, 212, 213]) (count417 q) 1 1 (meaning403 q) (meaning415 q) (meaning418 q) hs
  change valuationOf q 403 = false ∨ valuationOf q 415 = false ∨ valuationOf q 418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause451 (q : Snake 81) (h : Conditions q) : valuation q 403 = false ∨ valuation q 415 = false ∨ valuation q 418 = true := counterClause451 (baseVal q)

theorem counterClause452 (q : Nat → Bool) : valuationOf q 404 = false ∨ valuationOf q 418 = true := by
  have hs : count417 q = (countLit q [200, 201, 202, 203, 204, 205, 206]) + (countLit q [207, 208, 209, 210, 211, 212, 213]) := List.countP_append (p := literal q) (l₁ := [200, 201, 202, 203, 204, 205, 206]) (l₂ := [207, 208, 209, 210, 211, 212, 213])
  have hm := merge_left (literal (valuationOf q) (404)) (literal (valuationOf q) (418)) (countLit q [200, 201, 202, 203, 204, 205, 206]) (countLit q [207, 208, 209, 210, 211, 212, 213]) (count417 q) 2 (meaning404 q) (meaning418 q) hs
  change valuationOf q 404 = false ∨ valuationOf q 418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause452 (q : Snake 81) (h : Conditions q) : valuation q 404 = false ∨ valuation q 418 = true := counterClause452 (baseVal q)

theorem counterClause453 (q : Nat → Bool) : valuationOf q 417 = false ∨ valuationOf q 447 = true := by
  have hs : count447 q = (countLit q [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) + (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) := List.countP_append (p := literal q) (l₁ := [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) (l₂ := [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228])
  have hm := merge_left (literal (valuationOf q) (417)) (literal (valuationOf q) (447)) (countLit q [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) (count447 q) 1 (meaning417 q) (meaning447 q) hs
  change valuationOf q 417 = false ∨ valuationOf q 447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause453 (q : Snake 81) (h : Conditions q) : valuation q 417 = false ∨ valuation q 447 = true := counterClause453 (baseVal q)

theorem counterClause454 (q : Nat → Bool) : valuationOf q 418 = false ∨ valuationOf q 448 = true := by
  have hs : count447 q = (countLit q [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) + (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) := List.countP_append (p := literal q) (l₁ := [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) (l₂ := [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228])
  have hm := merge_left (literal (valuationOf q) (418)) (literal (valuationOf q) (448)) (countLit q [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]) (countLit q [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) (count447 q) 2 (meaning418 q) (meaning448 q) hs
  change valuationOf q 418 = false ∨ valuationOf q 448 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause454 (q : Snake 81) (h : Conditions q) : valuation q 418 = false ∨ valuation q 448 = true := counterClause454 (baseVal q)

theorem counterClause455 (q : Nat → Bool) : valuationOf q 447 = false ∨ valuationOf q 449 = true := by
  have hs : count449 q = (countLit q [171, 172, 173, 174, 175, 176, 177, 178, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199]) + (countLit q [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) := List.countP_append (p := literal q) (l₁ := [171, 172, 173, 174, 175, 176, 177, 178, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199]) (l₂ := [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228])
  have hm := merge_right (literal (valuationOf q) (447)) (literal (valuationOf q) (449)) (countLit q [171, 172, 173, 174, 175, 176, 177, 178, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199]) (countLit q [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) (count449 q) 1 (meaning447 q) (meaning449 q) hs
  change valuationOf q 447 = false ∨ valuationOf q 449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause455 (q : Snake 81) (h : Conditions q) : valuation q 447 = false ∨ valuation q 449 = true := counterClause455 (baseVal q)

theorem counterClause456 (q : Nat → Bool) : valuationOf q 448 = false ∨ valuationOf q 450 = true := by
  have hs : count449 q = (countLit q [171, 172, 173, 174, 175, 176, 177, 178, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199]) + (countLit q [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) := List.countP_append (p := literal q) (l₁ := [171, 172, 173, 174, 175, 176, 177, 178, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199]) (l₂ := [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228])
  have hm := merge_right (literal (valuationOf q) (448)) (literal (valuationOf q) (450)) (countLit q [171, 172, 173, 174, 175, 176, 177, 178, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199]) (countLit q [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) (count449 q) 2 (meaning448 q) (meaning450 q) hs
  change valuationOf q 448 = false ∨ valuationOf q 450 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause456 (q : Snake 81) (h : Conditions q) : valuation q 448 = false ∨ valuation q 450 = true := counterClause456 (baseVal q)

theorem counterClause457 (q : Nat → Bool) : valuationOf q 391 = false ∨ valuationOf q 449 = true := by
  have hs : count449 q = (countLit q [171, 172, 173, 174, 175, 176, 177, 178, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199]) + (countLit q [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) := List.countP_append (p := literal q) (l₁ := [171, 172, 173, 174, 175, 176, 177, 178, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199]) (l₂ := [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228])
  have hm := merge_left (literal (valuationOf q) (391)) (literal (valuationOf q) (449)) (countLit q [171, 172, 173, 174, 175, 176, 177, 178, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199]) (countLit q [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) (count449 q) 1 (meaning391 q) (meaning449 q) hs
  change valuationOf q 391 = false ∨ valuationOf q 449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause457 (q : Snake 81) (h : Conditions q) : valuation q 391 = false ∨ valuation q 449 = true := counterClause457 (baseVal q)

theorem counterClause458 (q : Nat → Bool) : valuationOf q 391 = false ∨ valuationOf q 447 = false ∨ valuationOf q 450 = true := by
  have hs : count449 q = (countLit q [171, 172, 173, 174, 175, 176, 177, 178, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199]) + (countLit q [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) := List.countP_append (p := literal q) (l₁ := [171, 172, 173, 174, 175, 176, 177, 178, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199]) (l₂ := [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228])
  have hm := merge_two (literal (valuationOf q) (391)) (literal (valuationOf q) (447)) (literal (valuationOf q) (450)) (countLit q [171, 172, 173, 174, 175, 176, 177, 178, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199]) (countLit q [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) (count449 q) 1 1 (meaning391 q) (meaning447 q) (meaning450 q) hs
  change valuationOf q 391 = false ∨ valuationOf q 447 = false ∨ valuationOf q 450 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause458 (q : Snake 81) (h : Conditions q) : valuation q 391 = false ∨ valuation q 447 = false ∨ valuation q 450 = true := counterClause458 (baseVal q)

theorem counterClause459 (q : Nat → Bool) : valuationOf q 392 = false ∨ valuationOf q 450 = true := by
  have hs : count449 q = (countLit q [171, 172, 173, 174, 175, 176, 177, 178, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199]) + (countLit q [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) := List.countP_append (p := literal q) (l₁ := [171, 172, 173, 174, 175, 176, 177, 178, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199]) (l₂ := [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228])
  have hm := merge_left (literal (valuationOf q) (392)) (literal (valuationOf q) (450)) (countLit q [171, 172, 173, 174, 175, 176, 177, 178, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199]) (countLit q [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) (count449 q) 2 (meaning392 q) (meaning450 q) hs
  change valuationOf q 392 = false ∨ valuationOf q 450 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause459 (q : Snake 81) (h : Conditions q) : valuation q 392 = false ∨ valuation q 450 = true := counterClause459 (baseVal q)

theorem counterClause460 (q : Nat → Bool) : valuationOf q 450 = false ∨ valuationOf q 452 = true := by
  have hs : count451 q = (countLit q [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) + (countLit q [171, 172, 173, 174, 175, 176, 177, 178, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) := List.countP_append (p := literal q) (l₁ := [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) (l₂ := [171, 172, 173, 174, 175, 176, 177, 178, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228])
  have hm := merge_right (literal (valuationOf q) (450)) (literal (valuationOf q) (452)) (countLit q [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) (countLit q [171, 172, 173, 174, 175, 176, 177, 178, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) (count451 q) 2 (meaning450 q) (meaning452 q) hs
  change valuationOf q 450 = false ∨ valuationOf q 452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause460 (q : Snake 81) (h : Conditions q) : valuation q 450 = false ∨ valuation q 452 = true := counterClause460 (baseVal q)

theorem counterClause461 (q : Nat → Bool) : valuationOf q 337 = false ∨ valuationOf q 449 = false ∨ valuationOf q 452 = true := by
  have hs : count451 q = (countLit q [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) + (countLit q [171, 172, 173, 174, 175, 176, 177, 178, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) := List.countP_append (p := literal q) (l₁ := [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) (l₂ := [171, 172, 173, 174, 175, 176, 177, 178, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228])
  have hm := merge_two (literal (valuationOf q) (337)) (literal (valuationOf q) (449)) (literal (valuationOf q) (452)) (countLit q [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) (countLit q [171, 172, 173, 174, 175, 176, 177, 178, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) (count451 q) 1 1 (meaning337 q) (meaning449 q) (meaning452 q) hs
  change valuationOf q 337 = false ∨ valuationOf q 449 = false ∨ valuationOf q 452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause461 (q : Snake 81) (h : Conditions q) : valuation q 337 = false ∨ valuation q 449 = false ∨ valuation q 452 = true := counterClause461 (baseVal q)

theorem counterClause462 (q : Nat → Bool) : valuationOf q 338 = false ∨ valuationOf q 452 = true := by
  have hs : count451 q = (countLit q [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) + (countLit q [171, 172, 173, 174, 175, 176, 177, 178, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) := List.countP_append (p := literal q) (l₁ := [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) (l₂ := [171, 172, 173, 174, 175, 176, 177, 178, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228])
  have hm := merge_left (literal (valuationOf q) (338)) (literal (valuationOf q) (452)) (countLit q [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]) (countLit q [171, 172, 173, 174, 175, 176, 177, 178, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]) (count451 q) 2 (meaning338 q) (meaning452 q) hs
  change valuationOf q 338 = false ∨ valuationOf q 452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause462 (q : Snake 81) (h : Conditions q) : valuation q 338 = false ∨ valuation q 452 = true := counterClause462 (baseVal q)

theorem clause463 (q : Snake 81) (h : Conditions q) : valuation q 452 = false := by
  rw [value452]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count451 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem counterClause464 (q : Nat → Bool) : valuationOf q 5 = true ∨ valuationOf q 1349 = true := by
  have hs : count1349 q = (countLit q [-3]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-5])
  have hm := merge_right (literal (valuationOf q) (-5)) (literal (valuationOf q) (1349)) (countLit q [-3]) (countLit q [-5]) (count1349 q) 1 (meaningNeg5 q) (meaning1349 q) hs
  change (! (valuationOf q 5)) = false ∨ valuationOf q 1349 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause464 (q : Snake 81) (h : Conditions q) : valuation q 5 = true ∨ valuation q 1349 = true := counterClause464 (baseVal q)

theorem counterClause465 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 1349 = true := by
  have hs : count1349 q = (countLit q [-3]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-5])
  have hm := merge_left (literal (valuationOf q) (-3)) (literal (valuationOf q) (1349)) (countLit q [-3]) (countLit q [-5]) (count1349 q) 1 (meaningNeg3 q) (meaning1349 q) hs
  change (! (valuationOf q 3)) = false ∨ valuationOf q 1349 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause465 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 1349 = true := counterClause465 (baseVal q)

theorem counterClause466 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 5 = true ∨ valuationOf q 1350 = true := by
  have hs : count1349 q = (countLit q [-3]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-5])
  have hm := merge_two (literal (valuationOf q) (-3)) (literal (valuationOf q) (-5)) (literal (valuationOf q) (1350)) (countLit q [-3]) (countLit q [-5]) (count1349 q) 1 1 (meaningNeg3 q) (meaningNeg5 q) (meaning1350 q) hs
  change (! (valuationOf q 3)) = false ∨ (! (valuationOf q 5)) = false ∨ valuationOf q 1350 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause466 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 5 = true ∨ valuation q 1350 = true := counterClause466 (baseVal q)

theorem counterClause467 (q : Nat → Bool) : valuationOf q 1349 = false ∨ valuationOf q 1351 = true := by
  have hs : count1351 q = (countLit q [-2]) + (countLit q [-3, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3, -5])
  have hm := merge_right (literal (valuationOf q) (1349)) (literal (valuationOf q) (1351)) (countLit q [-2]) (countLit q [-3, -5]) (count1351 q) 1 (meaning1349 q) (meaning1351 q) hs
  change valuationOf q 1349 = false ∨ valuationOf q 1351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause467 (q : Snake 81) (h : Conditions q) : valuation q 1349 = false ∨ valuation q 1351 = true := counterClause467 (baseVal q)

theorem counterClause468 (q : Nat → Bool) : valuationOf q 1350 = false ∨ valuationOf q 1352 = true := by
  have hs : count1351 q = (countLit q [-2]) + (countLit q [-3, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3, -5])
  have hm := merge_right (literal (valuationOf q) (1350)) (literal (valuationOf q) (1352)) (countLit q [-2]) (countLit q [-3, -5]) (count1351 q) 2 (meaning1350 q) (meaning1352 q) hs
  change valuationOf q 1350 = false ∨ valuationOf q 1352 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause468 (q : Snake 81) (h : Conditions q) : valuation q 1350 = false ∨ valuation q 1352 = true := counterClause468 (baseVal q)

theorem counterClause469 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1351 = true := by
  have hs : count1351 q = (countLit q [-2]) + (countLit q [-3, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3, -5])
  have hm := merge_left (literal (valuationOf q) (-2)) (literal (valuationOf q) (1351)) (countLit q [-2]) (countLit q [-3, -5]) (count1351 q) 1 (meaningNeg2 q) (meaning1351 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1351 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause469 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1351 = true := counterClause469 (baseVal q)

theorem counterClause470 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1349 = false ∨ valuationOf q 1352 = true := by
  have hs : count1351 q = (countLit q [-2]) + (countLit q [-3, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3, -5])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (1349)) (literal (valuationOf q) (1352)) (countLit q [-2]) (countLit q [-3, -5]) (count1351 q) 1 1 (meaningNeg2 q) (meaning1349 q) (meaning1352 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1349 = false ∨ valuationOf q 1352 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause470 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1349 = false ∨ valuation q 1352 = true := counterClause470 (baseVal q)

theorem counterClause471 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1350 = false ∨ valuationOf q 1353 = true := by
  have hs : count1351 q = (countLit q [-2]) + (countLit q [-3, -5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-3, -5])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (1350)) (literal (valuationOf q) (1353)) (countLit q [-2]) (countLit q [-3, -5]) (count1351 q) 1 2 (meaningNeg2 q) (meaning1350 q) (meaning1353 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1350 = false ∨ valuationOf q 1353 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause471 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1350 = false ∨ valuation q 1353 = true := counterClause471 (baseVal q)

theorem counterClause472 (q : Nat → Bool) : valuationOf q 9 = true ∨ valuationOf q 1354 = true := by
  have hs : count1354 q = (countLit q [-6]) + (countLit q [-9]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-9])
  have hm := merge_right (literal (valuationOf q) (-9)) (literal (valuationOf q) (1354)) (countLit q [-6]) (countLit q [-9]) (count1354 q) 1 (meaningNeg9 q) (meaning1354 q) hs
  change (! (valuationOf q 9)) = false ∨ valuationOf q 1354 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause472 (q : Snake 81) (h : Conditions q) : valuation q 9 = true ∨ valuation q 1354 = true := counterClause472 (baseVal q)

theorem counterClause473 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 1354 = true := by
  have hs : count1354 q = (countLit q [-6]) + (countLit q [-9]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-9])
  have hm := merge_left (literal (valuationOf q) (-6)) (literal (valuationOf q) (1354)) (countLit q [-6]) (countLit q [-9]) (count1354 q) 1 (meaningNeg6 q) (meaning1354 q) hs
  change (! (valuationOf q 6)) = false ∨ valuationOf q 1354 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause473 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 1354 = true := counterClause473 (baseVal q)

theorem counterClause474 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 9 = true ∨ valuationOf q 1355 = true := by
  have hs : count1354 q = (countLit q [-6]) + (countLit q [-9]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-9])
  have hm := merge_two (literal (valuationOf q) (-6)) (literal (valuationOf q) (-9)) (literal (valuationOf q) (1355)) (countLit q [-6]) (countLit q [-9]) (count1354 q) 1 1 (meaningNeg6 q) (meaningNeg9 q) (meaning1355 q) hs
  change (! (valuationOf q 6)) = false ∨ (! (valuationOf q 9)) = false ∨ valuationOf q 1355 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause474 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 9 = true ∨ valuation q 1355 = true := counterClause474 (baseVal q)

theorem counterClause475 (q : Nat → Bool) : valuationOf q 12 = true ∨ valuationOf q 1356 = true := by
  have hs : count1356 q = (countLit q [-10]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-12])
  have hm := merge_right (literal (valuationOf q) (-12)) (literal (valuationOf q) (1356)) (countLit q [-10]) (countLit q [-12]) (count1356 q) 1 (meaningNeg12 q) (meaning1356 q) hs
  change (! (valuationOf q 12)) = false ∨ valuationOf q 1356 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause475 (q : Snake 81) (h : Conditions q) : valuation q 12 = true ∨ valuation q 1356 = true := counterClause475 (baseVal q)

theorem counterClause476 (q : Nat → Bool) : valuationOf q 10 = true ∨ valuationOf q 1356 = true := by
  have hs : count1356 q = (countLit q [-10]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-12])
  have hm := merge_left (literal (valuationOf q) (-10)) (literal (valuationOf q) (1356)) (countLit q [-10]) (countLit q [-12]) (count1356 q) 1 (meaningNeg10 q) (meaning1356 q) hs
  change (! (valuationOf q 10)) = false ∨ valuationOf q 1356 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause476 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 1356 = true := counterClause476 (baseVal q)

theorem counterClause477 (q : Nat → Bool) : valuationOf q 10 = true ∨ valuationOf q 12 = true ∨ valuationOf q 1357 = true := by
  have hs : count1356 q = (countLit q [-10]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-12])
  have hm := merge_two (literal (valuationOf q) (-10)) (literal (valuationOf q) (-12)) (literal (valuationOf q) (1357)) (countLit q [-10]) (countLit q [-12]) (count1356 q) 1 1 (meaningNeg10 q) (meaningNeg12 q) (meaning1357 q) hs
  change (! (valuationOf q 10)) = false ∨ (! (valuationOf q 12)) = false ∨ valuationOf q 1357 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause477 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 12 = true ∨ valuation q 1357 = true := counterClause477 (baseVal q)

theorem counterClause478 (q : Nat → Bool) : valuationOf q 1356 = false ∨ valuationOf q 1358 = true := by
  have hs : count1358 q = (countLit q [-6, -9]) + (countLit q [-10, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -9]) (l₂ := [-10, -12])
  have hm := merge_right (literal (valuationOf q) (1356)) (literal (valuationOf q) (1358)) (countLit q [-6, -9]) (countLit q [-10, -12]) (count1358 q) 1 (meaning1356 q) (meaning1358 q) hs
  change valuationOf q 1356 = false ∨ valuationOf q 1358 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause478 (q : Snake 81) (h : Conditions q) : valuation q 1356 = false ∨ valuation q 1358 = true := counterClause478 (baseVal q)

theorem counterClause479 (q : Nat → Bool) : valuationOf q 1357 = false ∨ valuationOf q 1359 = true := by
  have hs : count1358 q = (countLit q [-6, -9]) + (countLit q [-10, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -9]) (l₂ := [-10, -12])
  have hm := merge_right (literal (valuationOf q) (1357)) (literal (valuationOf q) (1359)) (countLit q [-6, -9]) (countLit q [-10, -12]) (count1358 q) 2 (meaning1357 q) (meaning1359 q) hs
  change valuationOf q 1357 = false ∨ valuationOf q 1359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause479 (q : Snake 81) (h : Conditions q) : valuation q 1357 = false ∨ valuation q 1359 = true := counterClause479 (baseVal q)

theorem counterClause480 (q : Nat → Bool) : valuationOf q 1354 = false ∨ valuationOf q 1358 = true := by
  have hs : count1358 q = (countLit q [-6, -9]) + (countLit q [-10, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -9]) (l₂ := [-10, -12])
  have hm := merge_left (literal (valuationOf q) (1354)) (literal (valuationOf q) (1358)) (countLit q [-6, -9]) (countLit q [-10, -12]) (count1358 q) 1 (meaning1354 q) (meaning1358 q) hs
  change valuationOf q 1354 = false ∨ valuationOf q 1358 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause480 (q : Snake 81) (h : Conditions q) : valuation q 1354 = false ∨ valuation q 1358 = true := counterClause480 (baseVal q)

theorem block14 (q : Snake 81) (h : Conditions q) : B112E146.Block14 (valuation q) :=
  ⟨clause449 q h, clause450 q h, clause451 q h, clause452 q h, clause453 q h, clause454 q h, clause455 q h, clause456 q h, clause457 q h, clause458 q h, clause459 q h, clause460 q h, clause461 q h, clause462 q h, clause463 q h, clause464 q h, clause465 q h, clause466 q h, clause467 q h, clause468 q h, clause469 q h, clause470 q h, clause471 q h, clause472 q h, clause473 q h, clause474 q h, clause475 q h, clause476 q h, clause477 q h, clause478 q h, clause479 q h, clause480 q h⟩

end
end Snake9.Regrowth.E112146
