import E112115Semantics
import B112E115Inputs
namespace Snake9.Regrowth.E112115
noncomputable section
local instance blockDec26 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause833 (q : Nat → Bool) : valuationOf q 813 = false ∨ valuationOf q 834 = false ∨ valuationOf q 845 = true := by
  have hs : count837 q = (countLit q [-1, -4, -7, -9, -11, -13, -14]) + (countLit q [-16, -18, -19, -21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14]) (l₂ := [-16, -18, -19, -21, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (813)) (literal (valuationOf q) (834)) (literal (valuationOf q) (845)) (countLit q [-1, -4, -7, -9, -11, -13, -14]) (countLit q [-16, -18, -19, -21, -22, -24, -25]) (count837 q) 4 5 (meaning813 q) (meaning834 q) (meaning845 q) hs
  change valuationOf q 813 = false ∨ valuationOf q 834 = false ∨ valuationOf q 845 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause833 (q : Snake 81) (h : Conditions q) : valuation q 813 = false ∨ valuation q 834 = false ∨ valuation q 845 = true := counterClause833 (baseVal q)

theorem counterClause834 (q : Nat → Bool) : valuationOf q 814 = false ∨ valuationOf q 841 = true := by
  have hs : count837 q = (countLit q [-1, -4, -7, -9, -11, -13, -14]) + (countLit q [-16, -18, -19, -21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14]) (l₂ := [-16, -18, -19, -21, -22, -24, -25])
  have hm := merge_left (literal (valuationOf q) (814)) (literal (valuationOf q) (841)) (countLit q [-1, -4, -7, -9, -11, -13, -14]) (countLit q [-16, -18, -19, -21, -22, -24, -25]) (count837 q) 5 (meaning814 q) (meaning841 q) hs
  change valuationOf q 814 = false ∨ valuationOf q 841 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause834 (q : Snake 81) (h : Conditions q) : valuation q 814 = false ∨ valuation q 841 = true := counterClause834 (baseVal q)

theorem counterClause835 (q : Nat → Bool) : valuationOf q 814 = false ∨ valuationOf q 830 = false ∨ valuationOf q 842 = true := by
  have hs : count837 q = (countLit q [-1, -4, -7, -9, -11, -13, -14]) + (countLit q [-16, -18, -19, -21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14]) (l₂ := [-16, -18, -19, -21, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (814)) (literal (valuationOf q) (830)) (literal (valuationOf q) (842)) (countLit q [-1, -4, -7, -9, -11, -13, -14]) (countLit q [-16, -18, -19, -21, -22, -24, -25]) (count837 q) 5 1 (meaning814 q) (meaning830 q) (meaning842 q) hs
  change valuationOf q 814 = false ∨ valuationOf q 830 = false ∨ valuationOf q 842 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause835 (q : Snake 81) (h : Conditions q) : valuation q 814 = false ∨ valuation q 830 = false ∨ valuation q 842 = true := counterClause835 (baseVal q)

theorem counterClause836 (q : Nat → Bool) : valuationOf q 814 = false ∨ valuationOf q 831 = false ∨ valuationOf q 843 = true := by
  have hs : count837 q = (countLit q [-1, -4, -7, -9, -11, -13, -14]) + (countLit q [-16, -18, -19, -21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14]) (l₂ := [-16, -18, -19, -21, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (814)) (literal (valuationOf q) (831)) (literal (valuationOf q) (843)) (countLit q [-1, -4, -7, -9, -11, -13, -14]) (countLit q [-16, -18, -19, -21, -22, -24, -25]) (count837 q) 5 2 (meaning814 q) (meaning831 q) (meaning843 q) hs
  change valuationOf q 814 = false ∨ valuationOf q 831 = false ∨ valuationOf q 843 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause836 (q : Snake 81) (h : Conditions q) : valuation q 814 = false ∨ valuation q 831 = false ∨ valuation q 843 = true := counterClause836 (baseVal q)

theorem counterClause837 (q : Nat → Bool) : valuationOf q 814 = false ∨ valuationOf q 832 = false ∨ valuationOf q 844 = true := by
  have hs : count837 q = (countLit q [-1, -4, -7, -9, -11, -13, -14]) + (countLit q [-16, -18, -19, -21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14]) (l₂ := [-16, -18, -19, -21, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (814)) (literal (valuationOf q) (832)) (literal (valuationOf q) (844)) (countLit q [-1, -4, -7, -9, -11, -13, -14]) (countLit q [-16, -18, -19, -21, -22, -24, -25]) (count837 q) 5 3 (meaning814 q) (meaning832 q) (meaning844 q) hs
  change valuationOf q 814 = false ∨ valuationOf q 832 = false ∨ valuationOf q 844 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause837 (q : Snake 81) (h : Conditions q) : valuation q 814 = false ∨ valuation q 832 = false ∨ valuation q 844 = true := counterClause837 (baseVal q)

theorem counterClause838 (q : Nat → Bool) : valuationOf q 814 = false ∨ valuationOf q 833 = false ∨ valuationOf q 845 = true := by
  have hs : count837 q = (countLit q [-1, -4, -7, -9, -11, -13, -14]) + (countLit q [-16, -18, -19, -21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14]) (l₂ := [-16, -18, -19, -21, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (814)) (literal (valuationOf q) (833)) (literal (valuationOf q) (845)) (countLit q [-1, -4, -7, -9, -11, -13, -14]) (countLit q [-16, -18, -19, -21, -22, -24, -25]) (count837 q) 5 4 (meaning814 q) (meaning833 q) (meaning845 q) hs
  change valuationOf q 814 = false ∨ valuationOf q 833 = false ∨ valuationOf q 845 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause838 (q : Snake 81) (h : Conditions q) : valuation q 814 = false ∨ valuation q 833 = false ∨ valuation q 845 = true := counterClause838 (baseVal q)

theorem counterClause839 (q : Nat → Bool) : valuationOf q 814 = false ∨ valuationOf q 834 = false ∨ valuationOf q 846 = true := by
  have hs : count837 q = (countLit q [-1, -4, -7, -9, -11, -13, -14]) + (countLit q [-16, -18, -19, -21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14]) (l₂ := [-16, -18, -19, -21, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (814)) (literal (valuationOf q) (834)) (literal (valuationOf q) (846)) (countLit q [-1, -4, -7, -9, -11, -13, -14]) (countLit q [-16, -18, -19, -21, -22, -24, -25]) (count837 q) 5 5 (meaning814 q) (meaning834 q) (meaning846 q) hs
  change valuationOf q 814 = false ∨ valuationOf q 834 = false ∨ valuationOf q 846 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause839 (q : Snake 81) (h : Conditions q) : valuation q 814 = false ∨ valuation q 834 = false ∨ valuation q 846 = true := counterClause839 (baseVal q)

theorem counterClause840 (q : Nat → Bool) : valuationOf q 815 = false ∨ valuationOf q 830 = false ∨ valuationOf q 843 = true := by
  have hs : count837 q = (countLit q [-1, -4, -7, -9, -11, -13, -14]) + (countLit q [-16, -18, -19, -21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14]) (l₂ := [-16, -18, -19, -21, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (815)) (literal (valuationOf q) (830)) (literal (valuationOf q) (843)) (countLit q [-1, -4, -7, -9, -11, -13, -14]) (countLit q [-16, -18, -19, -21, -22, -24, -25]) (count837 q) 6 1 (meaning815 q) (meaning830 q) (meaning843 q) hs
  change valuationOf q 815 = false ∨ valuationOf q 830 = false ∨ valuationOf q 843 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause840 (q : Snake 81) (h : Conditions q) : valuation q 815 = false ∨ valuation q 830 = false ∨ valuation q 843 = true := counterClause840 (baseVal q)

theorem counterClause841 (q : Nat → Bool) : valuationOf q 815 = false ∨ valuationOf q 831 = false ∨ valuationOf q 844 = true := by
  have hs : count837 q = (countLit q [-1, -4, -7, -9, -11, -13, -14]) + (countLit q [-16, -18, -19, -21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14]) (l₂ := [-16, -18, -19, -21, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (815)) (literal (valuationOf q) (831)) (literal (valuationOf q) (844)) (countLit q [-1, -4, -7, -9, -11, -13, -14]) (countLit q [-16, -18, -19, -21, -22, -24, -25]) (count837 q) 6 2 (meaning815 q) (meaning831 q) (meaning844 q) hs
  change valuationOf q 815 = false ∨ valuationOf q 831 = false ∨ valuationOf q 844 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause841 (q : Snake 81) (h : Conditions q) : valuation q 815 = false ∨ valuation q 831 = false ∨ valuation q 844 = true := counterClause841 (baseVal q)

theorem counterClause842 (q : Nat → Bool) : valuationOf q 815 = false ∨ valuationOf q 832 = false ∨ valuationOf q 845 = true := by
  have hs : count837 q = (countLit q [-1, -4, -7, -9, -11, -13, -14]) + (countLit q [-16, -18, -19, -21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14]) (l₂ := [-16, -18, -19, -21, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (815)) (literal (valuationOf q) (832)) (literal (valuationOf q) (845)) (countLit q [-1, -4, -7, -9, -11, -13, -14]) (countLit q [-16, -18, -19, -21, -22, -24, -25]) (count837 q) 6 3 (meaning815 q) (meaning832 q) (meaning845 q) hs
  change valuationOf q 815 = false ∨ valuationOf q 832 = false ∨ valuationOf q 845 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause842 (q : Snake 81) (h : Conditions q) : valuation q 815 = false ∨ valuation q 832 = false ∨ valuation q 845 = true := counterClause842 (baseVal q)

theorem counterClause843 (q : Nat → Bool) : valuationOf q 815 = false ∨ valuationOf q 833 = false ∨ valuationOf q 846 = true := by
  have hs : count837 q = (countLit q [-1, -4, -7, -9, -11, -13, -14]) + (countLit q [-16, -18, -19, -21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14]) (l₂ := [-16, -18, -19, -21, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (815)) (literal (valuationOf q) (833)) (literal (valuationOf q) (846)) (countLit q [-1, -4, -7, -9, -11, -13, -14]) (countLit q [-16, -18, -19, -21, -22, -24, -25]) (count837 q) 6 4 (meaning815 q) (meaning833 q) (meaning846 q) hs
  change valuationOf q 815 = false ∨ valuationOf q 833 = false ∨ valuationOf q 846 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause843 (q : Snake 81) (h : Conditions q) : valuation q 815 = false ∨ valuation q 833 = false ∨ valuation q 846 = true := counterClause843 (baseVal q)

theorem counterClause844 (q : Nat → Bool) : valuationOf q 815 = false ∨ valuationOf q 834 = false ∨ valuationOf q 847 = true := by
  have hs : count837 q = (countLit q [-1, -4, -7, -9, -11, -13, -14]) + (countLit q [-16, -18, -19, -21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14]) (l₂ := [-16, -18, -19, -21, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (815)) (literal (valuationOf q) (834)) (literal (valuationOf q) (847)) (countLit q [-1, -4, -7, -9, -11, -13, -14]) (countLit q [-16, -18, -19, -21, -22, -24, -25]) (count837 q) 6 5 (meaning815 q) (meaning834 q) (meaning847 q) hs
  change valuationOf q 815 = false ∨ valuationOf q 834 = false ∨ valuationOf q 847 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause844 (q : Snake 81) (h : Conditions q) : valuation q 815 = false ∨ valuation q 834 = false ∨ valuation q 847 = true := counterClause844 (baseVal q)

theorem counterClause845 (q : Nat → Bool) : valuationOf q 816 = false ∨ valuationOf q 833 = false ∨ valuationOf q 847 = true := by
  have hs : count837 q = (countLit q [-1, -4, -7, -9, -11, -13, -14]) + (countLit q [-16, -18, -19, -21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14]) (l₂ := [-16, -18, -19, -21, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (816)) (literal (valuationOf q) (833)) (literal (valuationOf q) (847)) (countLit q [-1, -4, -7, -9, -11, -13, -14]) (countLit q [-16, -18, -19, -21, -22, -24, -25]) (count837 q) 7 4 (meaning816 q) (meaning833 q) (meaning847 q) hs
  change valuationOf q 816 = false ∨ valuationOf q 833 = false ∨ valuationOf q 847 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause845 (q : Snake 81) (h : Conditions q) : valuation q 816 = false ∨ valuation q 833 = false ∨ valuation q 847 = true := counterClause845 (baseVal q)

theorem counterClause846 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 851 = true := by
  have hs : count851 q = (countLit q [-30]) + (countLit q [-32]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-32])
  have hm := merge_right (literal (valuationOf q) (-32)) (literal (valuationOf q) (851)) (countLit q [-30]) (countLit q [-32]) (count851 q) 1 (meaningNeg32 q) (meaning851 q) hs
  change (! (valuationOf q 32)) = false ∨ valuationOf q 851 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause846 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 851 = true := counterClause846 (baseVal q)

theorem counterClause847 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 851 = true := by
  have hs : count851 q = (countLit q [-30]) + (countLit q [-32]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-32])
  have hm := merge_left (literal (valuationOf q) (-30)) (literal (valuationOf q) (851)) (countLit q [-30]) (countLit q [-32]) (count851 q) 1 (meaningNeg30 q) (meaning851 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 851 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause847 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 851 = true := counterClause847 (baseVal q)

theorem counterClause848 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 32 = true ∨ valuationOf q 852 = true := by
  have hs : count851 q = (countLit q [-30]) + (countLit q [-32]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-32])
  have hm := merge_two (literal (valuationOf q) (-30)) (literal (valuationOf q) (-32)) (literal (valuationOf q) (852)) (countLit q [-30]) (countLit q [-32]) (count851 q) 1 1 (meaningNeg30 q) (meaningNeg32 q) (meaning852 q) hs
  change (! (valuationOf q 30)) = false ∨ (! (valuationOf q 32)) = false ∨ valuationOf q 852 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause848 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 32 = true ∨ valuation q 852 = true := counterClause848 (baseVal q)

theorem counterClause849 (q : Nat → Bool) : valuationOf q 851 = false ∨ valuationOf q 853 = true := by
  have hs : count853 q = (countLit q [-28]) + (countLit q [-30, -32]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-30, -32])
  have hm := merge_right (literal (valuationOf q) (851)) (literal (valuationOf q) (853)) (countLit q [-28]) (countLit q [-30, -32]) (count853 q) 1 (meaning851 q) (meaning853 q) hs
  change valuationOf q 851 = false ∨ valuationOf q 853 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause849 (q : Snake 81) (h : Conditions q) : valuation q 851 = false ∨ valuation q 853 = true := counterClause849 (baseVal q)

theorem counterClause850 (q : Nat → Bool) : valuationOf q 852 = false ∨ valuationOf q 854 = true := by
  have hs : count853 q = (countLit q [-28]) + (countLit q [-30, -32]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-30, -32])
  have hm := merge_right (literal (valuationOf q) (852)) (literal (valuationOf q) (854)) (countLit q [-28]) (countLit q [-30, -32]) (count853 q) 2 (meaning852 q) (meaning854 q) hs
  change valuationOf q 852 = false ∨ valuationOf q 854 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause850 (q : Snake 81) (h : Conditions q) : valuation q 852 = false ∨ valuation q 854 = true := counterClause850 (baseVal q)

theorem counterClause851 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 853 = true := by
  have hs : count853 q = (countLit q [-28]) + (countLit q [-30, -32]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-30, -32])
  have hm := merge_left (literal (valuationOf q) (-28)) (literal (valuationOf q) (853)) (countLit q [-28]) (countLit q [-30, -32]) (count853 q) 1 (meaningNeg28 q) (meaning853 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 853 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause851 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 853 = true := counterClause851 (baseVal q)

theorem counterClause852 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 851 = false ∨ valuationOf q 854 = true := by
  have hs : count853 q = (countLit q [-28]) + (countLit q [-30, -32]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-30, -32])
  have hm := merge_two (literal (valuationOf q) (-28)) (literal (valuationOf q) (851)) (literal (valuationOf q) (854)) (countLit q [-28]) (countLit q [-30, -32]) (count853 q) 1 1 (meaningNeg28 q) (meaning851 q) (meaning854 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 851 = false ∨ valuationOf q 854 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause852 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 851 = false ∨ valuation q 854 = true := counterClause852 (baseVal q)

theorem counterClause853 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 852 = false ∨ valuationOf q 855 = true := by
  have hs : count853 q = (countLit q [-28]) + (countLit q [-30, -32]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-30, -32])
  have hm := merge_two (literal (valuationOf q) (-28)) (literal (valuationOf q) (852)) (literal (valuationOf q) (855)) (countLit q [-28]) (countLit q [-30, -32]) (count853 q) 1 2 (meaningNeg28 q) (meaning852 q) (meaning855 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 852 = false ∨ valuationOf q 855 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause853 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 852 = false ∨ valuation q 855 = true := counterClause853 (baseVal q)

theorem counterClause854 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 856 = true := by
  have hs : count856 q = (countLit q [-33]) + (countLit q [-38]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-38])
  have hm := merge_right (literal (valuationOf q) (-38)) (literal (valuationOf q) (856)) (countLit q [-33]) (countLit q [-38]) (count856 q) 1 (meaningNeg38 q) (meaning856 q) hs
  change (! (valuationOf q 38)) = false ∨ valuationOf q 856 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause854 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 856 = true := counterClause854 (baseVal q)

theorem counterClause855 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 856 = true := by
  have hs : count856 q = (countLit q [-33]) + (countLit q [-38]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-38])
  have hm := merge_left (literal (valuationOf q) (-33)) (literal (valuationOf q) (856)) (countLit q [-33]) (countLit q [-38]) (count856 q) 1 (meaningNeg33 q) (meaning856 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 856 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause855 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 856 = true := counterClause855 (baseVal q)

theorem counterClause856 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 38 = true ∨ valuationOf q 857 = true := by
  have hs : count856 q = (countLit q [-33]) + (countLit q [-38]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-38])
  have hm := merge_two (literal (valuationOf q) (-33)) (literal (valuationOf q) (-38)) (literal (valuationOf q) (857)) (countLit q [-33]) (countLit q [-38]) (count856 q) 1 1 (meaningNeg33 q) (meaningNeg38 q) (meaning857 q) hs
  change (! (valuationOf q 33)) = false ∨ (! (valuationOf q 38)) = false ∨ valuationOf q 857 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause856 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 38 = true ∨ valuation q 857 = true := counterClause856 (baseVal q)

theorem counterClause857 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 858 = true := by
  have hs : count858 q = (countLit q [-39]) + (countLit q [-40]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-40])
  have hm := merge_right (literal (valuationOf q) (-40)) (literal (valuationOf q) (858)) (countLit q [-39]) (countLit q [-40]) (count858 q) 1 (meaningNeg40 q) (meaning858 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 858 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause857 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 858 = true := counterClause857 (baseVal q)

theorem counterClause858 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 858 = true := by
  have hs : count858 q = (countLit q [-39]) + (countLit q [-40]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-40])
  have hm := merge_left (literal (valuationOf q) (-39)) (literal (valuationOf q) (858)) (countLit q [-39]) (countLit q [-40]) (count858 q) 1 (meaningNeg39 q) (meaning858 q) hs
  change (! (valuationOf q 39)) = false ∨ valuationOf q 858 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause858 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 858 = true := counterClause858 (baseVal q)

theorem counterClause859 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 40 = true ∨ valuationOf q 859 = true := by
  have hs : count858 q = (countLit q [-39]) + (countLit q [-40]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-40])
  have hm := merge_two (literal (valuationOf q) (-39)) (literal (valuationOf q) (-40)) (literal (valuationOf q) (859)) (countLit q [-39]) (countLit q [-40]) (count858 q) 1 1 (meaningNeg39 q) (meaningNeg40 q) (meaning859 q) hs
  change (! (valuationOf q 39)) = false ∨ (! (valuationOf q 40)) = false ∨ valuationOf q 859 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause859 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 40 = true ∨ valuation q 859 = true := counterClause859 (baseVal q)

theorem counterClause860 (q : Nat → Bool) : valuationOf q 858 = false ∨ valuationOf q 860 = true := by
  have hs : count860 q = (countLit q [-33, -38]) + (countLit q [-39, -40]) := List.countP_append (p := literal q) (l₁ := [-33, -38]) (l₂ := [-39, -40])
  have hm := merge_right (literal (valuationOf q) (858)) (literal (valuationOf q) (860)) (countLit q [-33, -38]) (countLit q [-39, -40]) (count860 q) 1 (meaning858 q) (meaning860 q) hs
  change valuationOf q 858 = false ∨ valuationOf q 860 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause860 (q : Snake 81) (h : Conditions q) : valuation q 858 = false ∨ valuation q 860 = true := counterClause860 (baseVal q)

theorem counterClause861 (q : Nat → Bool) : valuationOf q 859 = false ∨ valuationOf q 861 = true := by
  have hs : count860 q = (countLit q [-33, -38]) + (countLit q [-39, -40]) := List.countP_append (p := literal q) (l₁ := [-33, -38]) (l₂ := [-39, -40])
  have hm := merge_right (literal (valuationOf q) (859)) (literal (valuationOf q) (861)) (countLit q [-33, -38]) (countLit q [-39, -40]) (count860 q) 2 (meaning859 q) (meaning861 q) hs
  change valuationOf q 859 = false ∨ valuationOf q 861 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause861 (q : Snake 81) (h : Conditions q) : valuation q 859 = false ∨ valuation q 861 = true := counterClause861 (baseVal q)

theorem counterClause862 (q : Nat → Bool) : valuationOf q 856 = false ∨ valuationOf q 860 = true := by
  have hs : count860 q = (countLit q [-33, -38]) + (countLit q [-39, -40]) := List.countP_append (p := literal q) (l₁ := [-33, -38]) (l₂ := [-39, -40])
  have hm := merge_left (literal (valuationOf q) (856)) (literal (valuationOf q) (860)) (countLit q [-33, -38]) (countLit q [-39, -40]) (count860 q) 1 (meaning856 q) (meaning860 q) hs
  change valuationOf q 856 = false ∨ valuationOf q 860 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause862 (q : Snake 81) (h : Conditions q) : valuation q 856 = false ∨ valuation q 860 = true := counterClause862 (baseVal q)

theorem counterClause863 (q : Nat → Bool) : valuationOf q 856 = false ∨ valuationOf q 858 = false ∨ valuationOf q 861 = true := by
  have hs : count860 q = (countLit q [-33, -38]) + (countLit q [-39, -40]) := List.countP_append (p := literal q) (l₁ := [-33, -38]) (l₂ := [-39, -40])
  have hm := merge_two (literal (valuationOf q) (856)) (literal (valuationOf q) (858)) (literal (valuationOf q) (861)) (countLit q [-33, -38]) (countLit q [-39, -40]) (count860 q) 1 1 (meaning856 q) (meaning858 q) (meaning861 q) hs
  change valuationOf q 856 = false ∨ valuationOf q 858 = false ∨ valuationOf q 861 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause863 (q : Snake 81) (h : Conditions q) : valuation q 856 = false ∨ valuation q 858 = false ∨ valuation q 861 = true := counterClause863 (baseVal q)

theorem counterClause864 (q : Nat → Bool) : valuationOf q 856 = false ∨ valuationOf q 859 = false ∨ valuationOf q 862 = true := by
  have hs : count860 q = (countLit q [-33, -38]) + (countLit q [-39, -40]) := List.countP_append (p := literal q) (l₁ := [-33, -38]) (l₂ := [-39, -40])
  have hm := merge_two (literal (valuationOf q) (856)) (literal (valuationOf q) (859)) (literal (valuationOf q) (862)) (countLit q [-33, -38]) (countLit q [-39, -40]) (count860 q) 1 2 (meaning856 q) (meaning859 q) (meaning862 q) hs
  change valuationOf q 856 = false ∨ valuationOf q 859 = false ∨ valuationOf q 862 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause864 (q : Snake 81) (h : Conditions q) : valuation q 856 = false ∨ valuation q 859 = false ∨ valuation q 862 = true := counterClause864 (baseVal q)

theorem block26 (q : Snake 81) (h : Conditions q) : B112E115.Block26 (valuation q) :=
  ⟨clause833 q h, clause834 q h, clause835 q h, clause836 q h, clause837 q h, clause838 q h, clause839 q h, clause840 q h, clause841 q h, clause842 q h, clause843 q h, clause844 q h, clause845 q h, clause846 q h, clause847 q h, clause848 q h, clause849 q h, clause850 q h, clause851 q h, clause852 q h, clause853 q h, clause854 q h, clause855 q h, clause856 q h, clause857 q h, clause858 q h, clause859 q h, clause860 q h, clause861 q h, clause862 q h, clause863 q h, clause864 q h⟩

end
end Snake9.Regrowth.E112115
