import E112026Semantics
import B112E026Inputs
namespace Snake9.Regrowth.E112026
noncomputable section
local instance blockDec26 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause833 (q : Nat → Bool) : valuationOf q 478 = false ∨ valuationOf q 480 = true := by
  have hs : count479 q = (countLit q [122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) + (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (l₂ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242])
  have hm := merge_right (literal (valuationOf q) (478)) (literal (valuationOf q) (480)) (countLit q [122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) (count479 q) 2 (meaning478 q) (meaning480 q) hs
  change valuationOf q 478 = false ∨ valuationOf q 480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause833 (q : Snake 81) (h : Conditions q) : valuation q 478 = false ∨ valuation q 480 = true := counterClause833 (baseVal q)

theorem counterClause834 (q : Nat → Bool) : valuationOf q 359 = false ∨ valuationOf q 477 = false ∨ valuationOf q 480 = true := by
  have hs : count479 q = (countLit q [122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) + (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (l₂ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242])
  have hm := merge_two (literal (valuationOf q) (359)) (literal (valuationOf q) (477)) (literal (valuationOf q) (480)) (countLit q [122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) (count479 q) 1 1 (meaning359 q) (meaning477 q) (meaning480 q) hs
  change valuationOf q 359 = false ∨ valuationOf q 477 = false ∨ valuationOf q 480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause834 (q : Snake 81) (h : Conditions q) : valuation q 359 = false ∨ valuation q 477 = false ∨ valuation q 480 = true := counterClause834 (baseVal q)

theorem counterClause835 (q : Nat → Bool) : valuationOf q 360 = false ∨ valuationOf q 480 = true := by
  have hs : count479 q = (countLit q [122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) + (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) := List.countP_append (p := literal q) (l₁ := [122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (l₂ := [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242])
  have hm := merge_left (literal (valuationOf q) (360)) (literal (valuationOf q) (480)) (countLit q [122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]) (countLit q [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]) (count479 q) 2 (meaning360 q) (meaning480 q) hs
  change valuationOf q 360 = false ∨ valuationOf q 480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause835 (q : Snake 81) (h : Conditions q) : valuation q 360 = false ∨ valuation q 480 = true := counterClause835 (baseVal q)

theorem clause836 (q : Snake 81) (h : Conditions q) : valuation q 480 = false := by
  rw [value480]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count479 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem counterClause837 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 1443 = true := by
  have hs : count1443 q = (countLit q [-3]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-5])
  have hm := merge_left (literal (valuationOf q) (-3)) (literal (valuationOf q) (1443)) (countLit q [-3]) (countLit q [-5]) (count1443 q) 1 (meaningNeg3 q) (meaning1443 q) hs
  change (! (valuationOf q 3)) = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause837 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 1443 = true := counterClause837 (baseVal q)

theorem counterClause838 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1445 = true := by
  have hs : count1445 q = (countLit q [-1]) + (countLit q [-3, -5]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-3, -5])
  have hm := merge_right (literal (valuationOf q) (1443)) (literal (valuationOf q) (1445)) (countLit q [-1]) (countLit q [-3, -5]) (count1445 q) 1 (meaning1443 q) (meaning1445 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause838 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1445 = true := counterClause838 (baseVal q)

theorem counterClause839 (q : Nat → Bool) : valuationOf q 1 = true ∨ valuationOf q 1445 = true := by
  have hs : count1445 q = (countLit q [-1]) + (countLit q [-3, -5]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-3, -5])
  have hm := merge_left (literal (valuationOf q) (-1)) (literal (valuationOf q) (1445)) (countLit q [-1]) (countLit q [-3, -5]) (count1445 q) 1 (meaningNeg1 q) (meaning1445 q) hs
  change (! (valuationOf q 1)) = false ∨ valuationOf q 1445 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause839 (q : Snake 81) (h : Conditions q) : valuation q 1 = true ∨ valuation q 1445 = true := counterClause839 (baseVal q)

theorem counterClause840 (q : Nat → Bool) : valuationOf q 1 = true ∨ valuationOf q 1443 = false ∨ valuationOf q 1446 = true := by
  have hs : count1445 q = (countLit q [-1]) + (countLit q [-3, -5]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-3, -5])
  have hm := merge_two (literal (valuationOf q) (-1)) (literal (valuationOf q) (1443)) (literal (valuationOf q) (1446)) (countLit q [-1]) (countLit q [-3, -5]) (count1445 q) 1 1 (meaningNeg1 q) (meaning1443 q) (meaning1446 q) hs
  change (! (valuationOf q 1)) = false ∨ valuationOf q 1443 = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause840 (q : Snake 81) (h : Conditions q) : valuation q 1 = true ∨ valuation q 1443 = false ∨ valuation q 1446 = true := counterClause840 (baseVal q)

theorem counterClause841 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 1448 = true := by
  have hs : count1448 q = (countLit q [-6]) + (countLit q [-8]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-8])
  have hm := merge_right (literal (valuationOf q) (-8)) (literal (valuationOf q) (1448)) (countLit q [-6]) (countLit q [-8]) (count1448 q) 1 (meaningNeg8 q) (meaning1448 q) hs
  change (! (valuationOf q 8)) = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause841 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 1448 = true := counterClause841 (baseVal q)

theorem counterClause842 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 1448 = true := by
  have hs : count1448 q = (countLit q [-6]) + (countLit q [-8]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-8])
  have hm := merge_left (literal (valuationOf q) (-6)) (literal (valuationOf q) (1448)) (countLit q [-6]) (countLit q [-8]) (count1448 q) 1 (meaningNeg6 q) (meaning1448 q) hs
  change (! (valuationOf q 6)) = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause842 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 1448 = true := counterClause842 (baseVal q)

theorem counterClause843 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 8 = true ∨ valuationOf q 1449 = true := by
  have hs : count1448 q = (countLit q [-6]) + (countLit q [-8]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-8])
  have hm := merge_two (literal (valuationOf q) (-6)) (literal (valuationOf q) (-8)) (literal (valuationOf q) (1449)) (countLit q [-6]) (countLit q [-8]) (count1448 q) 1 1 (meaningNeg6 q) (meaningNeg8 q) (meaning1449 q) hs
  change (! (valuationOf q 6)) = false ∨ (! (valuationOf q 8)) = false ∨ valuationOf q 1449 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause843 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 8 = true ∨ valuation q 1449 = true := counterClause843 (baseVal q)

theorem counterClause844 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 1450 = true := by
  have hs : count1450 q = (countLit q [-10]) + (countLit q [-11]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-11])
  have hm := merge_right (literal (valuationOf q) (-11)) (literal (valuationOf q) (1450)) (countLit q [-10]) (countLit q [-11]) (count1450 q) 1 (meaningNeg11 q) (meaning1450 q) hs
  change (! (valuationOf q 11)) = false ∨ valuationOf q 1450 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause844 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 1450 = true := counterClause844 (baseVal q)

theorem counterClause845 (q : Nat → Bool) : valuationOf q 10 = true ∨ valuationOf q 1450 = true := by
  have hs : count1450 q = (countLit q [-10]) + (countLit q [-11]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-11])
  have hm := merge_left (literal (valuationOf q) (-10)) (literal (valuationOf q) (1450)) (countLit q [-10]) (countLit q [-11]) (count1450 q) 1 (meaningNeg10 q) (meaning1450 q) hs
  change (! (valuationOf q 10)) = false ∨ valuationOf q 1450 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause845 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 1450 = true := counterClause845 (baseVal q)

theorem counterClause846 (q : Nat → Bool) : valuationOf q 10 = true ∨ valuationOf q 11 = true ∨ valuationOf q 1451 = true := by
  have hs : count1450 q = (countLit q [-10]) + (countLit q [-11]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-11])
  have hm := merge_two (literal (valuationOf q) (-10)) (literal (valuationOf q) (-11)) (literal (valuationOf q) (1451)) (countLit q [-10]) (countLit q [-11]) (count1450 q) 1 1 (meaningNeg10 q) (meaningNeg11 q) (meaning1451 q) hs
  change (! (valuationOf q 10)) = false ∨ (! (valuationOf q 11)) = false ∨ valuationOf q 1451 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause846 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 11 = true ∨ valuation q 1451 = true := counterClause846 (baseVal q)

theorem counterClause847 (q : Nat → Bool) : valuationOf q 1450 = false ∨ valuationOf q 1452 = true := by
  have hs : count1452 q = (countLit q [-6, -8]) + (countLit q [-10, -11]) := List.countP_append (p := literal q) (l₁ := [-6, -8]) (l₂ := [-10, -11])
  have hm := merge_right (literal (valuationOf q) (1450)) (literal (valuationOf q) (1452)) (countLit q [-6, -8]) (countLit q [-10, -11]) (count1452 q) 1 (meaning1450 q) (meaning1452 q) hs
  change valuationOf q 1450 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause847 (q : Snake 81) (h : Conditions q) : valuation q 1450 = false ∨ valuation q 1452 = true := counterClause847 (baseVal q)

theorem counterClause848 (q : Nat → Bool) : valuationOf q 1451 = false ∨ valuationOf q 1453 = true := by
  have hs : count1452 q = (countLit q [-6, -8]) + (countLit q [-10, -11]) := List.countP_append (p := literal q) (l₁ := [-6, -8]) (l₂ := [-10, -11])
  have hm := merge_right (literal (valuationOf q) (1451)) (literal (valuationOf q) (1453)) (countLit q [-6, -8]) (countLit q [-10, -11]) (count1452 q) 2 (meaning1451 q) (meaning1453 q) hs
  change valuationOf q 1451 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause848 (q : Snake 81) (h : Conditions q) : valuation q 1451 = false ∨ valuation q 1453 = true := counterClause848 (baseVal q)

theorem counterClause849 (q : Nat → Bool) : valuationOf q 1448 = false ∨ valuationOf q 1452 = true := by
  have hs : count1452 q = (countLit q [-6, -8]) + (countLit q [-10, -11]) := List.countP_append (p := literal q) (l₁ := [-6, -8]) (l₂ := [-10, -11])
  have hm := merge_left (literal (valuationOf q) (1448)) (literal (valuationOf q) (1452)) (countLit q [-6, -8]) (countLit q [-10, -11]) (count1452 q) 1 (meaning1448 q) (meaning1452 q) hs
  change valuationOf q 1448 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause849 (q : Snake 81) (h : Conditions q) : valuation q 1448 = false ∨ valuation q 1452 = true := counterClause849 (baseVal q)

theorem counterClause850 (q : Nat → Bool) : valuationOf q 1448 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1453 = true := by
  have hs : count1452 q = (countLit q [-6, -8]) + (countLit q [-10, -11]) := List.countP_append (p := literal q) (l₁ := [-6, -8]) (l₂ := [-10, -11])
  have hm := merge_two (literal (valuationOf q) (1448)) (literal (valuationOf q) (1450)) (literal (valuationOf q) (1453)) (countLit q [-6, -8]) (countLit q [-10, -11]) (count1452 q) 1 1 (meaning1448 q) (meaning1450 q) (meaning1453 q) hs
  change valuationOf q 1448 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause850 (q : Snake 81) (h : Conditions q) : valuation q 1448 = false ∨ valuation q 1450 = false ∨ valuation q 1453 = true := counterClause850 (baseVal q)

theorem counterClause851 (q : Nat → Bool) : valuationOf q 1448 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1454 = true := by
  have hs : count1452 q = (countLit q [-6, -8]) + (countLit q [-10, -11]) := List.countP_append (p := literal q) (l₁ := [-6, -8]) (l₂ := [-10, -11])
  have hm := merge_two (literal (valuationOf q) (1448)) (literal (valuationOf q) (1451)) (literal (valuationOf q) (1454)) (countLit q [-6, -8]) (countLit q [-10, -11]) (count1452 q) 1 2 (meaning1448 q) (meaning1451 q) (meaning1454 q) hs
  change valuationOf q 1448 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause851 (q : Snake 81) (h : Conditions q) : valuation q 1448 = false ∨ valuation q 1451 = false ∨ valuation q 1454 = true := counterClause851 (baseVal q)

theorem counterClause852 (q : Nat → Bool) : valuationOf q 1449 = false ∨ valuationOf q 1453 = true := by
  have hs : count1452 q = (countLit q [-6, -8]) + (countLit q [-10, -11]) := List.countP_append (p := literal q) (l₁ := [-6, -8]) (l₂ := [-10, -11])
  have hm := merge_left (literal (valuationOf q) (1449)) (literal (valuationOf q) (1453)) (countLit q [-6, -8]) (countLit q [-10, -11]) (count1452 q) 2 (meaning1449 q) (meaning1453 q) hs
  change valuationOf q 1449 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause852 (q : Snake 81) (h : Conditions q) : valuation q 1449 = false ∨ valuation q 1453 = true := counterClause852 (baseVal q)

theorem counterClause853 (q : Nat → Bool) : valuationOf q 1449 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1454 = true := by
  have hs : count1452 q = (countLit q [-6, -8]) + (countLit q [-10, -11]) := List.countP_append (p := literal q) (l₁ := [-6, -8]) (l₂ := [-10, -11])
  have hm := merge_two (literal (valuationOf q) (1449)) (literal (valuationOf q) (1450)) (literal (valuationOf q) (1454)) (countLit q [-6, -8]) (countLit q [-10, -11]) (count1452 q) 2 1 (meaning1449 q) (meaning1450 q) (meaning1454 q) hs
  change valuationOf q 1449 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause853 (q : Snake 81) (h : Conditions q) : valuation q 1449 = false ∨ valuation q 1450 = false ∨ valuation q 1454 = true := counterClause853 (baseVal q)

theorem counterClause854 (q : Nat → Bool) : valuationOf q 1449 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1455 = true := by
  have hs : count1452 q = (countLit q [-6, -8]) + (countLit q [-10, -11]) := List.countP_append (p := literal q) (l₁ := [-6, -8]) (l₂ := [-10, -11])
  have hm := merge_two (literal (valuationOf q) (1449)) (literal (valuationOf q) (1451)) (literal (valuationOf q) (1455)) (countLit q [-6, -8]) (countLit q [-10, -11]) (count1452 q) 2 2 (meaning1449 q) (meaning1451 q) (meaning1455 q) hs
  change valuationOf q 1449 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause854 (q : Snake 81) (h : Conditions q) : valuation q 1449 = false ∨ valuation q 1451 = false ∨ valuation q 1455 = true := counterClause854 (baseVal q)

theorem counterClause855 (q : Nat → Bool) : valuationOf q 1453 = false ∨ valuationOf q 1457 = true := by
  have hs : count1456 q = (countLit q [-1, -3, -5]) + (countLit q [-6, -8, -10, -11]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5]) (l₂ := [-6, -8, -10, -11])
  have hm := merge_right (literal (valuationOf q) (1453)) (literal (valuationOf q) (1457)) (countLit q [-1, -3, -5]) (countLit q [-6, -8, -10, -11]) (count1456 q) 2 (meaning1453 q) (meaning1457 q) hs
  change valuationOf q 1453 = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause855 (q : Snake 81) (h : Conditions q) : valuation q 1453 = false ∨ valuation q 1457 = true := counterClause855 (baseVal q)

theorem counterClause856 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1458 = true := by
  have hs : count1456 q = (countLit q [-1, -3, -5]) + (countLit q [-6, -8, -10, -11]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5]) (l₂ := [-6, -8, -10, -11])
  have hm := merge_right (literal (valuationOf q) (1454)) (literal (valuationOf q) (1458)) (countLit q [-1, -3, -5]) (countLit q [-6, -8, -10, -11]) (count1456 q) 3 (meaning1454 q) (meaning1458 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1458 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause856 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1458 = true := counterClause856 (baseVal q)

theorem counterClause857 (q : Nat → Bool) : valuationOf q 1455 = false ∨ valuationOf q 1459 = true := by
  have hs : count1456 q = (countLit q [-1, -3, -5]) + (countLit q [-6, -8, -10, -11]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5]) (l₂ := [-6, -8, -10, -11])
  have hm := merge_right (literal (valuationOf q) (1455)) (literal (valuationOf q) (1459)) (countLit q [-1, -3, -5]) (countLit q [-6, -8, -10, -11]) (count1456 q) 4 (meaning1455 q) (meaning1459 q) hs
  change valuationOf q 1455 = false ∨ valuationOf q 1459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause857 (q : Snake 81) (h : Conditions q) : valuation q 1455 = false ∨ valuation q 1459 = true := counterClause857 (baseVal q)

theorem counterClause858 (q : Nat → Bool) : valuationOf q 1445 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1457 = true := by
  have hs : count1456 q = (countLit q [-1, -3, -5]) + (countLit q [-6, -8, -10, -11]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5]) (l₂ := [-6, -8, -10, -11])
  have hm := merge_two (literal (valuationOf q) (1445)) (literal (valuationOf q) (1452)) (literal (valuationOf q) (1457)) (countLit q [-1, -3, -5]) (countLit q [-6, -8, -10, -11]) (count1456 q) 1 1 (meaning1445 q) (meaning1452 q) (meaning1457 q) hs
  change valuationOf q 1445 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause858 (q : Snake 81) (h : Conditions q) : valuation q 1445 = false ∨ valuation q 1452 = false ∨ valuation q 1457 = true := counterClause858 (baseVal q)

theorem counterClause859 (q : Nat → Bool) : valuationOf q 1445 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1458 = true := by
  have hs : count1456 q = (countLit q [-1, -3, -5]) + (countLit q [-6, -8, -10, -11]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5]) (l₂ := [-6, -8, -10, -11])
  have hm := merge_two (literal (valuationOf q) (1445)) (literal (valuationOf q) (1453)) (literal (valuationOf q) (1458)) (countLit q [-1, -3, -5]) (countLit q [-6, -8, -10, -11]) (count1456 q) 1 2 (meaning1445 q) (meaning1453 q) (meaning1458 q) hs
  change valuationOf q 1445 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1458 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause859 (q : Snake 81) (h : Conditions q) : valuation q 1445 = false ∨ valuation q 1453 = false ∨ valuation q 1458 = true := counterClause859 (baseVal q)

theorem counterClause860 (q : Nat → Bool) : valuationOf q 1445 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1459 = true := by
  have hs : count1456 q = (countLit q [-1, -3, -5]) + (countLit q [-6, -8, -10, -11]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5]) (l₂ := [-6, -8, -10, -11])
  have hm := merge_two (literal (valuationOf q) (1445)) (literal (valuationOf q) (1454)) (literal (valuationOf q) (1459)) (countLit q [-1, -3, -5]) (countLit q [-6, -8, -10, -11]) (count1456 q) 1 3 (meaning1445 q) (meaning1454 q) (meaning1459 q) hs
  change valuationOf q 1445 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause860 (q : Snake 81) (h : Conditions q) : valuation q 1445 = false ∨ valuation q 1454 = false ∨ valuation q 1459 = true := counterClause860 (baseVal q)

theorem counterClause861 (q : Nat → Bool) : valuationOf q 1445 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1460 = true := by
  have hs : count1456 q = (countLit q [-1, -3, -5]) + (countLit q [-6, -8, -10, -11]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5]) (l₂ := [-6, -8, -10, -11])
  have hm := merge_two (literal (valuationOf q) (1445)) (literal (valuationOf q) (1455)) (literal (valuationOf q) (1460)) (countLit q [-1, -3, -5]) (countLit q [-6, -8, -10, -11]) (count1456 q) 1 4 (meaning1445 q) (meaning1455 q) (meaning1460 q) hs
  change valuationOf q 1445 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1460 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause861 (q : Snake 81) (h : Conditions q) : valuation q 1445 = false ∨ valuation q 1455 = false ∨ valuation q 1460 = true := counterClause861 (baseVal q)

theorem counterClause862 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1457 = true := by
  have hs : count1456 q = (countLit q [-1, -3, -5]) + (countLit q [-6, -8, -10, -11]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5]) (l₂ := [-6, -8, -10, -11])
  have hm := merge_left (literal (valuationOf q) (1446)) (literal (valuationOf q) (1457)) (countLit q [-1, -3, -5]) (countLit q [-6, -8, -10, -11]) (count1456 q) 2 (meaning1446 q) (meaning1457 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause862 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1457 = true := counterClause862 (baseVal q)

theorem counterClause863 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1458 = true := by
  have hs : count1456 q = (countLit q [-1, -3, -5]) + (countLit q [-6, -8, -10, -11]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5]) (l₂ := [-6, -8, -10, -11])
  have hm := merge_two (literal (valuationOf q) (1446)) (literal (valuationOf q) (1452)) (literal (valuationOf q) (1458)) (countLit q [-1, -3, -5]) (countLit q [-6, -8, -10, -11]) (count1456 q) 2 1 (meaning1446 q) (meaning1452 q) (meaning1458 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1458 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause863 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1452 = false ∨ valuation q 1458 = true := counterClause863 (baseVal q)

theorem counterClause864 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1459 = true := by
  have hs : count1456 q = (countLit q [-1, -3, -5]) + (countLit q [-6, -8, -10, -11]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5]) (l₂ := [-6, -8, -10, -11])
  have hm := merge_two (literal (valuationOf q) (1446)) (literal (valuationOf q) (1453)) (literal (valuationOf q) (1459)) (countLit q [-1, -3, -5]) (countLit q [-6, -8, -10, -11]) (count1456 q) 2 2 (meaning1446 q) (meaning1453 q) (meaning1459 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause864 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1453 = false ∨ valuation q 1459 = true := counterClause864 (baseVal q)

theorem block26 (q : Snake 81) (h : Conditions q) : B112E026.Block26 (valuation q) :=
  ⟨clause833 q h, clause834 q h, clause835 q h, clause836 q h, clause837 q h, clause838 q h, clause839 q h, clause840 q h, clause841 q h, clause842 q h, clause843 q h, clause844 q h, clause845 q h, clause846 q h, clause847 q h, clause848 q h, clause849 q h, clause850 q h, clause851 q h, clause852 q h, clause853 q h, clause854 q h, clause855 q h, clause856 q h, clause857 q h, clause858 q h, clause859 q h, clause860 q h, clause861 q h, clause862 q h, clause863 q h, clause864 q h⟩

end
end Snake9.Regrowth.E112026
