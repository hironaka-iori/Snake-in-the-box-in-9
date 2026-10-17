import E112153Semantics
import B112E153Inputs
namespace Snake9.Regrowth.E112153
noncomputable section
local instance blockDec27 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause865 (q : Nat → Bool) : valuationOf q 367 = false ∨ valuationOf q 489 = false ∨ valuationOf q 492 = true := by
  have hs : count491 q = (countLit q [125, 126, 127, 128, 129, 130, 131, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) + (countLit q [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 130, 131, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) (l₂ := [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_two (literal (valuationOf q) (367)) (literal (valuationOf q) (489)) (literal (valuationOf q) (492)) (countLit q [125, 126, 127, 128, 129, 130, 131, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) (countLit q [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) (count491 q) 1 1 (meaning367 q) (meaning489 q) (meaning492 q) hs
  change valuationOf q 367 = false ∨ valuationOf q 489 = false ∨ valuationOf q 492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause865 (q : Snake 81) (h : Conditions q) : valuation q 367 = false ∨ valuation q 489 = false ∨ valuation q 492 = true := counterClause865 (baseVal q)

theorem counterClause866 (q : Nat → Bool) : valuationOf q 368 = false ∨ valuationOf q 492 = true := by
  have hs : count491 q = (countLit q [125, 126, 127, 128, 129, 130, 131, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) + (countLit q [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) := List.countP_append (p := literal q) (l₁ := [125, 126, 127, 128, 129, 130, 131, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) (l₂ := [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248])
  have hm := merge_left (literal (valuationOf q) (368)) (literal (valuationOf q) (492)) (countLit q [125, 126, 127, 128, 129, 130, 131, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]) (countLit q [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]) (count491 q) 2 (meaning368 q) (meaning492 q) hs
  change valuationOf q 368 = false ∨ valuationOf q 492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause866 (q : Snake 81) (h : Conditions q) : valuation q 368 = false ∨ valuation q 492 = true := counterClause866 (baseVal q)

theorem clause867 (q : Snake 81) (h : Conditions q) : valuation q 492 = false := by
  rw [value492]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count491 (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := other_count_bound q h
  rw [he]
  omega

theorem counterClause868 (q : Nat → Bool) : valuationOf q 4 = true ∨ valuationOf q 843 = true := by
  have hs : count843 q = (countLit q [-3]) + (countLit q [-4]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-4])
  have hm := merge_right (literal (valuationOf q) (-4)) (literal (valuationOf q) (843)) (countLit q [-3]) (countLit q [-4]) (count843 q) 1 (meaningNeg4 q) (meaning843 q) hs
  change (! (valuationOf q 4)) = false ∨ valuationOf q 843 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause868 (q : Snake 81) (h : Conditions q) : valuation q 4 = true ∨ valuation q 843 = true := counterClause868 (baseVal q)

theorem counterClause869 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 843 = true := by
  have hs : count843 q = (countLit q [-3]) + (countLit q [-4]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-4])
  have hm := merge_left (literal (valuationOf q) (-3)) (literal (valuationOf q) (843)) (countLit q [-3]) (countLit q [-4]) (count843 q) 1 (meaningNeg3 q) (meaning843 q) hs
  change (! (valuationOf q 3)) = false ∨ valuationOf q 843 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause869 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 843 = true := counterClause869 (baseVal q)

theorem counterClause870 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 4 = true ∨ valuationOf q 844 = true := by
  have hs : count843 q = (countLit q [-3]) + (countLit q [-4]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-4])
  have hm := merge_two (literal (valuationOf q) (-3)) (literal (valuationOf q) (-4)) (literal (valuationOf q) (844)) (countLit q [-3]) (countLit q [-4]) (count843 q) 1 1 (meaningNeg3 q) (meaningNeg4 q) (meaning844 q) hs
  change (! (valuationOf q 3)) = false ∨ (! (valuationOf q 4)) = false ∨ valuationOf q 844 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause870 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 4 = true ∨ valuation q 844 = true := counterClause870 (baseVal q)

theorem counterClause871 (q : Nat → Bool) : valuationOf q 1 = true ∨ valuationOf q 845 = true := by
  have hs : count845 q = (countLit q [-1]) + (countLit q [-3, -4]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-3, -4])
  have hm := merge_left (literal (valuationOf q) (-1)) (literal (valuationOf q) (845)) (countLit q [-1]) (countLit q [-3, -4]) (count845 q) 1 (meaningNeg1 q) (meaning845 q) hs
  change (! (valuationOf q 1)) = false ∨ valuationOf q 845 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause871 (q : Snake 81) (h : Conditions q) : valuation q 1 = true ∨ valuation q 845 = true := counterClause871 (baseVal q)

theorem counterClause872 (q : Nat → Bool) : valuationOf q 1 = true ∨ valuationOf q 843 = false ∨ valuationOf q 846 = true := by
  have hs : count845 q = (countLit q [-1]) + (countLit q [-3, -4]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-3, -4])
  have hm := merge_two (literal (valuationOf q) (-1)) (literal (valuationOf q) (843)) (literal (valuationOf q) (846)) (countLit q [-1]) (countLit q [-3, -4]) (count845 q) 1 1 (meaningNeg1 q) (meaning843 q) (meaning846 q) hs
  change (! (valuationOf q 1)) = false ∨ valuationOf q 843 = false ∨ valuationOf q 846 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause872 (q : Snake 81) (h : Conditions q) : valuation q 1 = true ∨ valuation q 843 = false ∨ valuation q 846 = true := counterClause872 (baseVal q)

theorem counterClause873 (q : Nat → Bool) : valuationOf q 1 = true ∨ valuationOf q 844 = false ∨ valuationOf q 847 = true := by
  have hs : count845 q = (countLit q [-1]) + (countLit q [-3, -4]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-3, -4])
  have hm := merge_two (literal (valuationOf q) (-1)) (literal (valuationOf q) (844)) (literal (valuationOf q) (847)) (countLit q [-1]) (countLit q [-3, -4]) (count845 q) 1 2 (meaningNeg1 q) (meaning844 q) (meaning847 q) hs
  change (! (valuationOf q 1)) = false ∨ valuationOf q 844 = false ∨ valuationOf q 847 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause873 (q : Snake 81) (h : Conditions q) : valuation q 1 = true ∨ valuation q 844 = false ∨ valuation q 847 = true := counterClause873 (baseVal q)

theorem counterClause874 (q : Nat → Bool) : valuationOf q 5 = true ∨ valuationOf q 848 = true := by
  have hs : count848 q = (countLit q [-5]) + (countLit q [-8]) := List.countP_append (p := literal q) (l₁ := [-5]) (l₂ := [-8])
  have hm := merge_left (literal (valuationOf q) (-5)) (literal (valuationOf q) (848)) (countLit q [-5]) (countLit q [-8]) (count848 q) 1 (meaningNeg5 q) (meaning848 q) hs
  change (! (valuationOf q 5)) = false ∨ valuationOf q 848 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause874 (q : Snake 81) (h : Conditions q) : valuation q 5 = true ∨ valuation q 848 = true := counterClause874 (baseVal q)

theorem counterClause875 (q : Nat → Bool) : valuationOf q 12 = true ∨ valuationOf q 850 = true := by
  have hs : count850 q = (countLit q [-11]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-12])
  have hm := merge_right (literal (valuationOf q) (-12)) (literal (valuationOf q) (850)) (countLit q [-11]) (countLit q [-12]) (count850 q) 1 (meaningNeg12 q) (meaning850 q) hs
  change (! (valuationOf q 12)) = false ∨ valuationOf q 850 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause875 (q : Snake 81) (h : Conditions q) : valuation q 12 = true ∨ valuation q 850 = true := counterClause875 (baseVal q)

theorem counterClause876 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 850 = true := by
  have hs : count850 q = (countLit q [-11]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-12])
  have hm := merge_left (literal (valuationOf q) (-11)) (literal (valuationOf q) (850)) (countLit q [-11]) (countLit q [-12]) (count850 q) 1 (meaningNeg11 q) (meaning850 q) hs
  change (! (valuationOf q 11)) = false ∨ valuationOf q 850 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause876 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 850 = true := counterClause876 (baseVal q)

theorem counterClause877 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 12 = true ∨ valuationOf q 851 = true := by
  have hs : count850 q = (countLit q [-11]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-12])
  have hm := merge_two (literal (valuationOf q) (-11)) (literal (valuationOf q) (-12)) (literal (valuationOf q) (851)) (countLit q [-11]) (countLit q [-12]) (count850 q) 1 1 (meaningNeg11 q) (meaningNeg12 q) (meaning851 q) hs
  change (! (valuationOf q 11)) = false ∨ (! (valuationOf q 12)) = false ∨ valuationOf q 851 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause877 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 12 = true ∨ valuation q 851 = true := counterClause877 (baseVal q)

theorem counterClause878 (q : Nat → Bool) : valuationOf q 850 = false ∨ valuationOf q 852 = true := by
  have hs : count852 q = (countLit q [-5, -8]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-5, -8]) (l₂ := [-11, -12])
  have hm := merge_right (literal (valuationOf q) (850)) (literal (valuationOf q) (852)) (countLit q [-5, -8]) (countLit q [-11, -12]) (count852 q) 1 (meaning850 q) (meaning852 q) hs
  change valuationOf q 850 = false ∨ valuationOf q 852 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause878 (q : Snake 81) (h : Conditions q) : valuation q 850 = false ∨ valuation q 852 = true := counterClause878 (baseVal q)

theorem counterClause879 (q : Nat → Bool) : valuationOf q 851 = false ∨ valuationOf q 853 = true := by
  have hs : count852 q = (countLit q [-5, -8]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-5, -8]) (l₂ := [-11, -12])
  have hm := merge_right (literal (valuationOf q) (851)) (literal (valuationOf q) (853)) (countLit q [-5, -8]) (countLit q [-11, -12]) (count852 q) 2 (meaning851 q) (meaning853 q) hs
  change valuationOf q 851 = false ∨ valuationOf q 853 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause879 (q : Snake 81) (h : Conditions q) : valuation q 851 = false ∨ valuation q 853 = true := counterClause879 (baseVal q)

theorem counterClause880 (q : Nat → Bool) : valuationOf q 848 = false ∨ valuationOf q 852 = true := by
  have hs : count852 q = (countLit q [-5, -8]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-5, -8]) (l₂ := [-11, -12])
  have hm := merge_left (literal (valuationOf q) (848)) (literal (valuationOf q) (852)) (countLit q [-5, -8]) (countLit q [-11, -12]) (count852 q) 1 (meaning848 q) (meaning852 q) hs
  change valuationOf q 848 = false ∨ valuationOf q 852 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause880 (q : Snake 81) (h : Conditions q) : valuation q 848 = false ∨ valuation q 852 = true := counterClause880 (baseVal q)

theorem counterClause881 (q : Nat → Bool) : valuationOf q 848 = false ∨ valuationOf q 850 = false ∨ valuationOf q 853 = true := by
  have hs : count852 q = (countLit q [-5, -8]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-5, -8]) (l₂ := [-11, -12])
  have hm := merge_two (literal (valuationOf q) (848)) (literal (valuationOf q) (850)) (literal (valuationOf q) (853)) (countLit q [-5, -8]) (countLit q [-11, -12]) (count852 q) 1 1 (meaning848 q) (meaning850 q) (meaning853 q) hs
  change valuationOf q 848 = false ∨ valuationOf q 850 = false ∨ valuationOf q 853 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause881 (q : Snake 81) (h : Conditions q) : valuation q 848 = false ∨ valuation q 850 = false ∨ valuation q 853 = true := counterClause881 (baseVal q)

theorem counterClause882 (q : Nat → Bool) : valuationOf q 848 = false ∨ valuationOf q 851 = false ∨ valuationOf q 854 = true := by
  have hs : count852 q = (countLit q [-5, -8]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-5, -8]) (l₂ := [-11, -12])
  have hm := merge_two (literal (valuationOf q) (848)) (literal (valuationOf q) (851)) (literal (valuationOf q) (854)) (countLit q [-5, -8]) (countLit q [-11, -12]) (count852 q) 1 2 (meaning848 q) (meaning851 q) (meaning854 q) hs
  change valuationOf q 848 = false ∨ valuationOf q 851 = false ∨ valuationOf q 854 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause882 (q : Snake 81) (h : Conditions q) : valuation q 848 = false ∨ valuation q 851 = false ∨ valuation q 854 = true := counterClause882 (baseVal q)

theorem counterClause883 (q : Nat → Bool) : valuationOf q 845 = false ∨ valuationOf q 852 = false ∨ valuationOf q 857 = true := by
  have hs : count856 q = (countLit q [-1, -3, -4]) + (countLit q [-5, -8, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4]) (l₂ := [-5, -8, -11, -12])
  have hm := merge_two (literal (valuationOf q) (845)) (literal (valuationOf q) (852)) (literal (valuationOf q) (857)) (countLit q [-1, -3, -4]) (countLit q [-5, -8, -11, -12]) (count856 q) 1 1 (meaning845 q) (meaning852 q) (meaning857 q) hs
  change valuationOf q 845 = false ∨ valuationOf q 852 = false ∨ valuationOf q 857 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause883 (q : Snake 81) (h : Conditions q) : valuation q 845 = false ∨ valuation q 852 = false ∨ valuation q 857 = true := counterClause883 (baseVal q)

theorem counterClause884 (q : Nat → Bool) : valuationOf q 845 = false ∨ valuationOf q 853 = false ∨ valuationOf q 858 = true := by
  have hs : count856 q = (countLit q [-1, -3, -4]) + (countLit q [-5, -8, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4]) (l₂ := [-5, -8, -11, -12])
  have hm := merge_two (literal (valuationOf q) (845)) (literal (valuationOf q) (853)) (literal (valuationOf q) (858)) (countLit q [-1, -3, -4]) (countLit q [-5, -8, -11, -12]) (count856 q) 1 2 (meaning845 q) (meaning853 q) (meaning858 q) hs
  change valuationOf q 845 = false ∨ valuationOf q 853 = false ∨ valuationOf q 858 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause884 (q : Snake 81) (h : Conditions q) : valuation q 845 = false ∨ valuation q 853 = false ∨ valuation q 858 = true := counterClause884 (baseVal q)

theorem counterClause885 (q : Nat → Bool) : valuationOf q 845 = false ∨ valuationOf q 854 = false ∨ valuationOf q 859 = true := by
  have hs : count856 q = (countLit q [-1, -3, -4]) + (countLit q [-5, -8, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4]) (l₂ := [-5, -8, -11, -12])
  have hm := merge_two (literal (valuationOf q) (845)) (literal (valuationOf q) (854)) (literal (valuationOf q) (859)) (countLit q [-1, -3, -4]) (countLit q [-5, -8, -11, -12]) (count856 q) 1 3 (meaning845 q) (meaning854 q) (meaning859 q) hs
  change valuationOf q 845 = false ∨ valuationOf q 854 = false ∨ valuationOf q 859 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause885 (q : Snake 81) (h : Conditions q) : valuation q 845 = false ∨ valuation q 854 = false ∨ valuation q 859 = true := counterClause885 (baseVal q)

theorem counterClause886 (q : Nat → Bool) : valuationOf q 846 = false ∨ valuationOf q 857 = true := by
  have hs : count856 q = (countLit q [-1, -3, -4]) + (countLit q [-5, -8, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4]) (l₂ := [-5, -8, -11, -12])
  have hm := merge_left (literal (valuationOf q) (846)) (literal (valuationOf q) (857)) (countLit q [-1, -3, -4]) (countLit q [-5, -8, -11, -12]) (count856 q) 2 (meaning846 q) (meaning857 q) hs
  change valuationOf q 846 = false ∨ valuationOf q 857 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause886 (q : Snake 81) (h : Conditions q) : valuation q 846 = false ∨ valuation q 857 = true := counterClause886 (baseVal q)

theorem counterClause887 (q : Nat → Bool) : valuationOf q 846 = false ∨ valuationOf q 852 = false ∨ valuationOf q 858 = true := by
  have hs : count856 q = (countLit q [-1, -3, -4]) + (countLit q [-5, -8, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4]) (l₂ := [-5, -8, -11, -12])
  have hm := merge_two (literal (valuationOf q) (846)) (literal (valuationOf q) (852)) (literal (valuationOf q) (858)) (countLit q [-1, -3, -4]) (countLit q [-5, -8, -11, -12]) (count856 q) 2 1 (meaning846 q) (meaning852 q) (meaning858 q) hs
  change valuationOf q 846 = false ∨ valuationOf q 852 = false ∨ valuationOf q 858 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause887 (q : Snake 81) (h : Conditions q) : valuation q 846 = false ∨ valuation q 852 = false ∨ valuation q 858 = true := counterClause887 (baseVal q)

theorem counterClause888 (q : Nat → Bool) : valuationOf q 846 = false ∨ valuationOf q 853 = false ∨ valuationOf q 859 = true := by
  have hs : count856 q = (countLit q [-1, -3, -4]) + (countLit q [-5, -8, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4]) (l₂ := [-5, -8, -11, -12])
  have hm := merge_two (literal (valuationOf q) (846)) (literal (valuationOf q) (853)) (literal (valuationOf q) (859)) (countLit q [-1, -3, -4]) (countLit q [-5, -8, -11, -12]) (count856 q) 2 2 (meaning846 q) (meaning853 q) (meaning859 q) hs
  change valuationOf q 846 = false ∨ valuationOf q 853 = false ∨ valuationOf q 859 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause888 (q : Snake 81) (h : Conditions q) : valuation q 846 = false ∨ valuation q 853 = false ∨ valuation q 859 = true := counterClause888 (baseVal q)

theorem counterClause889 (q : Nat → Bool) : valuationOf q 846 = false ∨ valuationOf q 854 = false ∨ valuationOf q 860 = true := by
  have hs : count856 q = (countLit q [-1, -3, -4]) + (countLit q [-5, -8, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4]) (l₂ := [-5, -8, -11, -12])
  have hm := merge_two (literal (valuationOf q) (846)) (literal (valuationOf q) (854)) (literal (valuationOf q) (860)) (countLit q [-1, -3, -4]) (countLit q [-5, -8, -11, -12]) (count856 q) 2 3 (meaning846 q) (meaning854 q) (meaning860 q) hs
  change valuationOf q 846 = false ∨ valuationOf q 854 = false ∨ valuationOf q 860 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause889 (q : Snake 81) (h : Conditions q) : valuation q 846 = false ∨ valuation q 854 = false ∨ valuation q 860 = true := counterClause889 (baseVal q)

theorem counterClause890 (q : Nat → Bool) : valuationOf q 847 = false ∨ valuationOf q 858 = true := by
  have hs : count856 q = (countLit q [-1, -3, -4]) + (countLit q [-5, -8, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4]) (l₂ := [-5, -8, -11, -12])
  have hm := merge_left (literal (valuationOf q) (847)) (literal (valuationOf q) (858)) (countLit q [-1, -3, -4]) (countLit q [-5, -8, -11, -12]) (count856 q) 3 (meaning847 q) (meaning858 q) hs
  change valuationOf q 847 = false ∨ valuationOf q 858 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause890 (q : Snake 81) (h : Conditions q) : valuation q 847 = false ∨ valuation q 858 = true := counterClause890 (baseVal q)

theorem counterClause891 (q : Nat → Bool) : valuationOf q 847 = false ∨ valuationOf q 852 = false ∨ valuationOf q 859 = true := by
  have hs : count856 q = (countLit q [-1, -3, -4]) + (countLit q [-5, -8, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4]) (l₂ := [-5, -8, -11, -12])
  have hm := merge_two (literal (valuationOf q) (847)) (literal (valuationOf q) (852)) (literal (valuationOf q) (859)) (countLit q [-1, -3, -4]) (countLit q [-5, -8, -11, -12]) (count856 q) 3 1 (meaning847 q) (meaning852 q) (meaning859 q) hs
  change valuationOf q 847 = false ∨ valuationOf q 852 = false ∨ valuationOf q 859 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause891 (q : Snake 81) (h : Conditions q) : valuation q 847 = false ∨ valuation q 852 = false ∨ valuation q 859 = true := counterClause891 (baseVal q)

theorem counterClause892 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 863 = true := by
  have hs : count863 q = (countLit q [-14]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-18])
  have hm := merge_right (literal (valuationOf q) (-18)) (literal (valuationOf q) (863)) (countLit q [-14]) (countLit q [-18]) (count863 q) 1 (meaningNeg18 q) (meaning863 q) hs
  change (! (valuationOf q 18)) = false ∨ valuationOf q 863 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause892 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 863 = true := counterClause892 (baseVal q)

theorem counterClause893 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 863 = true := by
  have hs : count863 q = (countLit q [-14]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-18])
  have hm := merge_left (literal (valuationOf q) (-14)) (literal (valuationOf q) (863)) (countLit q [-14]) (countLit q [-18]) (count863 q) 1 (meaningNeg14 q) (meaning863 q) hs
  change (! (valuationOf q 14)) = false ∨ valuationOf q 863 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause893 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 863 = true := counterClause893 (baseVal q)

theorem counterClause894 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 18 = true ∨ valuationOf q 864 = true := by
  have hs : count863 q = (countLit q [-14]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-18])
  have hm := merge_two (literal (valuationOf q) (-14)) (literal (valuationOf q) (-18)) (literal (valuationOf q) (864)) (countLit q [-14]) (countLit q [-18]) (count863 q) 1 1 (meaningNeg14 q) (meaningNeg18 q) (meaning864 q) hs
  change (! (valuationOf q 14)) = false ∨ (! (valuationOf q 18)) = false ∨ valuationOf q 864 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause894 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 18 = true ∨ valuation q 864 = true := counterClause894 (baseVal q)

theorem counterClause895 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 865 = true := by
  have hs : count865 q = (countLit q [-20]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-21])
  have hm := merge_right (literal (valuationOf q) (-21)) (literal (valuationOf q) (865)) (countLit q [-20]) (countLit q [-21]) (count865 q) 1 (meaningNeg21 q) (meaning865 q) hs
  change (! (valuationOf q 21)) = false ∨ valuationOf q 865 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause895 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 865 = true := counterClause895 (baseVal q)

theorem counterClause896 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 865 = true := by
  have hs : count865 q = (countLit q [-20]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-21])
  have hm := merge_left (literal (valuationOf q) (-20)) (literal (valuationOf q) (865)) (countLit q [-20]) (countLit q [-21]) (count865 q) 1 (meaningNeg20 q) (meaning865 q) hs
  change (! (valuationOf q 20)) = false ∨ valuationOf q 865 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause896 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 865 = true := counterClause896 (baseVal q)

theorem block27 (q : Snake 81) (h : Conditions q) : B112E153.Block27 (valuation q) :=
  ⟨clause865 q h, clause866 q h, clause867 q h, clause868 q h, clause869 q h, clause870 q h, clause871 q h, clause872 q h, clause873 q h, clause874 q h, clause875 q h, clause876 q h, clause877 q h, clause878 q h, clause879 q h, clause880 q h, clause881 q h, clause882 q h, clause883 q h, clause884 q h, clause885 q h, clause886 q h, clause887 q h, clause888 q h, clause889 q h, clause890 q h, clause891 q h, clause892 q h, clause893 q h, clause894 q h, clause895 q h, clause896 q h⟩

end
end Snake9.Regrowth.E112153
