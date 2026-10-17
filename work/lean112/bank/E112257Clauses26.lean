import E112257Semantics
import B112E257Inputs
namespace Snake9.Regrowth.E112257
noncomputable section
local instance blockDec26 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause833 (q : Nat → Bool) : valuationOf q 790 = false ∨ valuationOf q 796 = false ∨ valuationOf q 802 = true := by
  have hs : count800 q = (countLit q [-1, -2, -4]) + (countLit q [-6, -7, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4]) (l₂ := [-6, -7, -11, -12])
  have hm := merge_two (literal (valuationOf q) (790)) (literal (valuationOf q) (796)) (literal (valuationOf q) (802)) (countLit q [-1, -2, -4]) (countLit q [-6, -7, -11, -12]) (count800 q) 2 1 (meaning790 q) (meaning796 q) (meaning802 q) hs
  change valuationOf q 790 = false ∨ valuationOf q 796 = false ∨ valuationOf q 802 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause833 (q : Snake 81) (h : Conditions q) : valuation q 790 = false ∨ valuation q 796 = false ∨ valuation q 802 = true := counterClause833 (baseVal q)

theorem counterClause834 (q : Nat → Bool) : valuationOf q 790 = false ∨ valuationOf q 797 = false ∨ valuationOf q 803 = true := by
  have hs : count800 q = (countLit q [-1, -2, -4]) + (countLit q [-6, -7, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4]) (l₂ := [-6, -7, -11, -12])
  have hm := merge_two (literal (valuationOf q) (790)) (literal (valuationOf q) (797)) (literal (valuationOf q) (803)) (countLit q [-1, -2, -4]) (countLit q [-6, -7, -11, -12]) (count800 q) 2 2 (meaning790 q) (meaning797 q) (meaning803 q) hs
  change valuationOf q 790 = false ∨ valuationOf q 797 = false ∨ valuationOf q 803 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause834 (q : Snake 81) (h : Conditions q) : valuation q 790 = false ∨ valuation q 797 = false ∨ valuation q 803 = true := counterClause834 (baseVal q)

theorem counterClause835 (q : Nat → Bool) : valuationOf q 790 = false ∨ valuationOf q 798 = false ∨ valuationOf q 804 = true := by
  have hs : count800 q = (countLit q [-1, -2, -4]) + (countLit q [-6, -7, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4]) (l₂ := [-6, -7, -11, -12])
  have hm := merge_two (literal (valuationOf q) (790)) (literal (valuationOf q) (798)) (literal (valuationOf q) (804)) (countLit q [-1, -2, -4]) (countLit q [-6, -7, -11, -12]) (count800 q) 2 3 (meaning790 q) (meaning798 q) (meaning804 q) hs
  change valuationOf q 790 = false ∨ valuationOf q 798 = false ∨ valuationOf q 804 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause835 (q : Snake 81) (h : Conditions q) : valuation q 790 = false ∨ valuation q 798 = false ∨ valuation q 804 = true := counterClause835 (baseVal q)

theorem counterClause836 (q : Nat → Bool) : valuationOf q 790 = false ∨ valuationOf q 799 = false ∨ valuationOf q 805 = true := by
  have hs : count800 q = (countLit q [-1, -2, -4]) + (countLit q [-6, -7, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4]) (l₂ := [-6, -7, -11, -12])
  have hm := merge_two (literal (valuationOf q) (790)) (literal (valuationOf q) (799)) (literal (valuationOf q) (805)) (countLit q [-1, -2, -4]) (countLit q [-6, -7, -11, -12]) (count800 q) 2 4 (meaning790 q) (meaning799 q) (meaning805 q) hs
  change valuationOf q 790 = false ∨ valuationOf q 799 = false ∨ valuationOf q 805 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause836 (q : Snake 81) (h : Conditions q) : valuation q 790 = false ∨ valuation q 799 = false ∨ valuation q 805 = true := counterClause836 (baseVal q)

theorem counterClause837 (q : Nat → Bool) : valuationOf q 791 = false ∨ valuationOf q 802 = true := by
  have hs : count800 q = (countLit q [-1, -2, -4]) + (countLit q [-6, -7, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4]) (l₂ := [-6, -7, -11, -12])
  have hm := merge_left (literal (valuationOf q) (791)) (literal (valuationOf q) (802)) (countLit q [-1, -2, -4]) (countLit q [-6, -7, -11, -12]) (count800 q) 3 (meaning791 q) (meaning802 q) hs
  change valuationOf q 791 = false ∨ valuationOf q 802 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause837 (q : Snake 81) (h : Conditions q) : valuation q 791 = false ∨ valuation q 802 = true := counterClause837 (baseVal q)

theorem counterClause838 (q : Nat → Bool) : valuationOf q 791 = false ∨ valuationOf q 796 = false ∨ valuationOf q 803 = true := by
  have hs : count800 q = (countLit q [-1, -2, -4]) + (countLit q [-6, -7, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4]) (l₂ := [-6, -7, -11, -12])
  have hm := merge_two (literal (valuationOf q) (791)) (literal (valuationOf q) (796)) (literal (valuationOf q) (803)) (countLit q [-1, -2, -4]) (countLit q [-6, -7, -11, -12]) (count800 q) 3 1 (meaning791 q) (meaning796 q) (meaning803 q) hs
  change valuationOf q 791 = false ∨ valuationOf q 796 = false ∨ valuationOf q 803 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause838 (q : Snake 81) (h : Conditions q) : valuation q 791 = false ∨ valuation q 796 = false ∨ valuation q 803 = true := counterClause838 (baseVal q)

theorem counterClause839 (q : Nat → Bool) : valuationOf q 791 = false ∨ valuationOf q 797 = false ∨ valuationOf q 804 = true := by
  have hs : count800 q = (countLit q [-1, -2, -4]) + (countLit q [-6, -7, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4]) (l₂ := [-6, -7, -11, -12])
  have hm := merge_two (literal (valuationOf q) (791)) (literal (valuationOf q) (797)) (literal (valuationOf q) (804)) (countLit q [-1, -2, -4]) (countLit q [-6, -7, -11, -12]) (count800 q) 3 2 (meaning791 q) (meaning797 q) (meaning804 q) hs
  change valuationOf q 791 = false ∨ valuationOf q 797 = false ∨ valuationOf q 804 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause839 (q : Snake 81) (h : Conditions q) : valuation q 791 = false ∨ valuation q 797 = false ∨ valuation q 804 = true := counterClause839 (baseVal q)

theorem counterClause840 (q : Nat → Bool) : valuationOf q 791 = false ∨ valuationOf q 798 = false ∨ valuationOf q 805 = true := by
  have hs : count800 q = (countLit q [-1, -2, -4]) + (countLit q [-6, -7, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4]) (l₂ := [-6, -7, -11, -12])
  have hm := merge_two (literal (valuationOf q) (791)) (literal (valuationOf q) (798)) (literal (valuationOf q) (805)) (countLit q [-1, -2, -4]) (countLit q [-6, -7, -11, -12]) (count800 q) 3 3 (meaning791 q) (meaning798 q) (meaning805 q) hs
  change valuationOf q 791 = false ∨ valuationOf q 798 = false ∨ valuationOf q 805 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause840 (q : Snake 81) (h : Conditions q) : valuation q 791 = false ∨ valuation q 798 = false ∨ valuation q 805 = true := counterClause840 (baseVal q)

theorem counterClause841 (q : Nat → Bool) : valuationOf q 19 = true ∨ valuationOf q 807 = true := by
  have hs : count807 q = (countLit q [-16]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-19])
  have hm := merge_right (literal (valuationOf q) (-19)) (literal (valuationOf q) (807)) (countLit q [-16]) (countLit q [-19]) (count807 q) 1 (meaningNeg19 q) (meaning807 q) hs
  change (! (valuationOf q 19)) = false ∨ valuationOf q 807 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause841 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 807 = true := counterClause841 (baseVal q)

theorem counterClause842 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 807 = true := by
  have hs : count807 q = (countLit q [-16]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-19])
  have hm := merge_left (literal (valuationOf q) (-16)) (literal (valuationOf q) (807)) (countLit q [-16]) (countLit q [-19]) (count807 q) 1 (meaningNeg16 q) (meaning807 q) hs
  change (! (valuationOf q 16)) = false ∨ valuationOf q 807 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause842 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 807 = true := counterClause842 (baseVal q)

theorem counterClause843 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 19 = true ∨ valuationOf q 808 = true := by
  have hs : count807 q = (countLit q [-16]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-19])
  have hm := merge_two (literal (valuationOf q) (-16)) (literal (valuationOf q) (-19)) (literal (valuationOf q) (808)) (countLit q [-16]) (countLit q [-19]) (count807 q) 1 1 (meaningNeg16 q) (meaningNeg19 q) (meaning808 q) hs
  change (! (valuationOf q 16)) = false ∨ (! (valuationOf q 19)) = false ∨ valuationOf q 808 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause843 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 19 = true ∨ valuation q 808 = true := counterClause843 (baseVal q)

theorem counterClause844 (q : Nat → Bool) : valuationOf q 807 = false ∨ valuationOf q 809 = true := by
  have hs : count809 q = (countLit q [-15]) + (countLit q [-16, -19]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-16, -19])
  have hm := merge_right (literal (valuationOf q) (807)) (literal (valuationOf q) (809)) (countLit q [-15]) (countLit q [-16, -19]) (count809 q) 1 (meaning807 q) (meaning809 q) hs
  change valuationOf q 807 = false ∨ valuationOf q 809 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause844 (q : Snake 81) (h : Conditions q) : valuation q 807 = false ∨ valuation q 809 = true := counterClause844 (baseVal q)

theorem counterClause845 (q : Nat → Bool) : valuationOf q 808 = false ∨ valuationOf q 810 = true := by
  have hs : count809 q = (countLit q [-15]) + (countLit q [-16, -19]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-16, -19])
  have hm := merge_right (literal (valuationOf q) (808)) (literal (valuationOf q) (810)) (countLit q [-15]) (countLit q [-16, -19]) (count809 q) 2 (meaning808 q) (meaning810 q) hs
  change valuationOf q 808 = false ∨ valuationOf q 810 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause845 (q : Snake 81) (h : Conditions q) : valuation q 808 = false ∨ valuation q 810 = true := counterClause845 (baseVal q)

theorem counterClause846 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 809 = true := by
  have hs : count809 q = (countLit q [-15]) + (countLit q [-16, -19]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-16, -19])
  have hm := merge_left (literal (valuationOf q) (-15)) (literal (valuationOf q) (809)) (countLit q [-15]) (countLit q [-16, -19]) (count809 q) 1 (meaningNeg15 q) (meaning809 q) hs
  change (! (valuationOf q 15)) = false ∨ valuationOf q 809 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause846 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 809 = true := counterClause846 (baseVal q)

theorem counterClause847 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 807 = false ∨ valuationOf q 810 = true := by
  have hs : count809 q = (countLit q [-15]) + (countLit q [-16, -19]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-16, -19])
  have hm := merge_two (literal (valuationOf q) (-15)) (literal (valuationOf q) (807)) (literal (valuationOf q) (810)) (countLit q [-15]) (countLit q [-16, -19]) (count809 q) 1 1 (meaningNeg15 q) (meaning807 q) (meaning810 q) hs
  change (! (valuationOf q 15)) = false ∨ valuationOf q 807 = false ∨ valuationOf q 810 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause847 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 807 = false ∨ valuation q 810 = true := counterClause847 (baseVal q)

theorem counterClause848 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 808 = false ∨ valuationOf q 811 = true := by
  have hs : count809 q = (countLit q [-15]) + (countLit q [-16, -19]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-16, -19])
  have hm := merge_two (literal (valuationOf q) (-15)) (literal (valuationOf q) (808)) (literal (valuationOf q) (811)) (countLit q [-15]) (countLit q [-16, -19]) (count809 q) 1 2 (meaningNeg15 q) (meaning808 q) (meaning811 q) hs
  change (! (valuationOf q 15)) = false ∨ valuationOf q 808 = false ∨ valuationOf q 811 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause848 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 808 = false ∨ valuation q 811 = true := counterClause848 (baseVal q)

theorem counterClause849 (q : Nat → Bool) : valuationOf q 23 = true ∨ valuationOf q 812 = true := by
  have hs : count812 q = (countLit q [-21]) + (countLit q [-23]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-23])
  have hm := merge_right (literal (valuationOf q) (-23)) (literal (valuationOf q) (812)) (countLit q [-21]) (countLit q [-23]) (count812 q) 1 (meaningNeg23 q) (meaning812 q) hs
  change (! (valuationOf q 23)) = false ∨ valuationOf q 812 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause849 (q : Snake 81) (h : Conditions q) : valuation q 23 = true ∨ valuation q 812 = true := counterClause849 (baseVal q)

theorem counterClause850 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 812 = true := by
  have hs : count812 q = (countLit q [-21]) + (countLit q [-23]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-23])
  have hm := merge_left (literal (valuationOf q) (-21)) (literal (valuationOf q) (812)) (countLit q [-21]) (countLit q [-23]) (count812 q) 1 (meaningNeg21 q) (meaning812 q) hs
  change (! (valuationOf q 21)) = false ∨ valuationOf q 812 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause850 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 812 = true := counterClause850 (baseVal q)

theorem counterClause851 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 23 = true ∨ valuationOf q 813 = true := by
  have hs : count812 q = (countLit q [-21]) + (countLit q [-23]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-23])
  have hm := merge_two (literal (valuationOf q) (-21)) (literal (valuationOf q) (-23)) (literal (valuationOf q) (813)) (countLit q [-21]) (countLit q [-23]) (count812 q) 1 1 (meaningNeg21 q) (meaningNeg23 q) (meaning813 q) hs
  change (! (valuationOf q 21)) = false ∨ (! (valuationOf q 23)) = false ∨ valuationOf q 813 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause851 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 23 = true ∨ valuation q 813 = true := counterClause851 (baseVal q)

theorem counterClause852 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 814 = true := by
  have hs : count814 q = (countLit q [-26]) + (countLit q [-28]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-28])
  have hm := merge_right (literal (valuationOf q) (-28)) (literal (valuationOf q) (814)) (countLit q [-26]) (countLit q [-28]) (count814 q) 1 (meaningNeg28 q) (meaning814 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 814 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause852 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 814 = true := counterClause852 (baseVal q)

theorem counterClause853 (q : Nat → Bool) : valuationOf q 26 = true ∨ valuationOf q 814 = true := by
  have hs : count814 q = (countLit q [-26]) + (countLit q [-28]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-28])
  have hm := merge_left (literal (valuationOf q) (-26)) (literal (valuationOf q) (814)) (countLit q [-26]) (countLit q [-28]) (count814 q) 1 (meaningNeg26 q) (meaning814 q) hs
  change (! (valuationOf q 26)) = false ∨ valuationOf q 814 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause853 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 814 = true := counterClause853 (baseVal q)

theorem counterClause854 (q : Nat → Bool) : valuationOf q 26 = true ∨ valuationOf q 28 = true ∨ valuationOf q 815 = true := by
  have hs : count814 q = (countLit q [-26]) + (countLit q [-28]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-28])
  have hm := merge_two (literal (valuationOf q) (-26)) (literal (valuationOf q) (-28)) (literal (valuationOf q) (815)) (countLit q [-26]) (countLit q [-28]) (count814 q) 1 1 (meaningNeg26 q) (meaningNeg28 q) (meaning815 q) hs
  change (! (valuationOf q 26)) = false ∨ (! (valuationOf q 28)) = false ∨ valuationOf q 815 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause854 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 28 = true ∨ valuation q 815 = true := counterClause854 (baseVal q)

theorem counterClause855 (q : Nat → Bool) : valuationOf q 814 = false ∨ valuationOf q 816 = true := by
  have hs : count816 q = (countLit q [-21, -23]) + (countLit q [-26, -28]) := List.countP_append (p := literal q) (l₁ := [-21, -23]) (l₂ := [-26, -28])
  have hm := merge_right (literal (valuationOf q) (814)) (literal (valuationOf q) (816)) (countLit q [-21, -23]) (countLit q [-26, -28]) (count816 q) 1 (meaning814 q) (meaning816 q) hs
  change valuationOf q 814 = false ∨ valuationOf q 816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause855 (q : Snake 81) (h : Conditions q) : valuation q 814 = false ∨ valuation q 816 = true := counterClause855 (baseVal q)

theorem counterClause856 (q : Nat → Bool) : valuationOf q 815 = false ∨ valuationOf q 817 = true := by
  have hs : count816 q = (countLit q [-21, -23]) + (countLit q [-26, -28]) := List.countP_append (p := literal q) (l₁ := [-21, -23]) (l₂ := [-26, -28])
  have hm := merge_right (literal (valuationOf q) (815)) (literal (valuationOf q) (817)) (countLit q [-21, -23]) (countLit q [-26, -28]) (count816 q) 2 (meaning815 q) (meaning817 q) hs
  change valuationOf q 815 = false ∨ valuationOf q 817 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause856 (q : Snake 81) (h : Conditions q) : valuation q 815 = false ∨ valuation q 817 = true := counterClause856 (baseVal q)

theorem counterClause857 (q : Nat → Bool) : valuationOf q 812 = false ∨ valuationOf q 816 = true := by
  have hs : count816 q = (countLit q [-21, -23]) + (countLit q [-26, -28]) := List.countP_append (p := literal q) (l₁ := [-21, -23]) (l₂ := [-26, -28])
  have hm := merge_left (literal (valuationOf q) (812)) (literal (valuationOf q) (816)) (countLit q [-21, -23]) (countLit q [-26, -28]) (count816 q) 1 (meaning812 q) (meaning816 q) hs
  change valuationOf q 812 = false ∨ valuationOf q 816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause857 (q : Snake 81) (h : Conditions q) : valuation q 812 = false ∨ valuation q 816 = true := counterClause857 (baseVal q)

theorem counterClause858 (q : Nat → Bool) : valuationOf q 812 = false ∨ valuationOf q 814 = false ∨ valuationOf q 817 = true := by
  have hs : count816 q = (countLit q [-21, -23]) + (countLit q [-26, -28]) := List.countP_append (p := literal q) (l₁ := [-21, -23]) (l₂ := [-26, -28])
  have hm := merge_two (literal (valuationOf q) (812)) (literal (valuationOf q) (814)) (literal (valuationOf q) (817)) (countLit q [-21, -23]) (countLit q [-26, -28]) (count816 q) 1 1 (meaning812 q) (meaning814 q) (meaning817 q) hs
  change valuationOf q 812 = false ∨ valuationOf q 814 = false ∨ valuationOf q 817 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause858 (q : Snake 81) (h : Conditions q) : valuation q 812 = false ∨ valuation q 814 = false ∨ valuation q 817 = true := counterClause858 (baseVal q)

theorem counterClause859 (q : Nat → Bool) : valuationOf q 812 = false ∨ valuationOf q 815 = false ∨ valuationOf q 818 = true := by
  have hs : count816 q = (countLit q [-21, -23]) + (countLit q [-26, -28]) := List.countP_append (p := literal q) (l₁ := [-21, -23]) (l₂ := [-26, -28])
  have hm := merge_two (literal (valuationOf q) (812)) (literal (valuationOf q) (815)) (literal (valuationOf q) (818)) (countLit q [-21, -23]) (countLit q [-26, -28]) (count816 q) 1 2 (meaning812 q) (meaning815 q) (meaning818 q) hs
  change valuationOf q 812 = false ∨ valuationOf q 815 = false ∨ valuationOf q 818 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause859 (q : Snake 81) (h : Conditions q) : valuation q 812 = false ∨ valuation q 815 = false ∨ valuation q 818 = true := counterClause859 (baseVal q)

theorem counterClause860 (q : Nat → Bool) : valuationOf q 813 = false ∨ valuationOf q 817 = true := by
  have hs : count816 q = (countLit q [-21, -23]) + (countLit q [-26, -28]) := List.countP_append (p := literal q) (l₁ := [-21, -23]) (l₂ := [-26, -28])
  have hm := merge_left (literal (valuationOf q) (813)) (literal (valuationOf q) (817)) (countLit q [-21, -23]) (countLit q [-26, -28]) (count816 q) 2 (meaning813 q) (meaning817 q) hs
  change valuationOf q 813 = false ∨ valuationOf q 817 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause860 (q : Snake 81) (h : Conditions q) : valuation q 813 = false ∨ valuation q 817 = true := counterClause860 (baseVal q)

theorem counterClause861 (q : Nat → Bool) : valuationOf q 813 = false ∨ valuationOf q 814 = false ∨ valuationOf q 818 = true := by
  have hs : count816 q = (countLit q [-21, -23]) + (countLit q [-26, -28]) := List.countP_append (p := literal q) (l₁ := [-21, -23]) (l₂ := [-26, -28])
  have hm := merge_two (literal (valuationOf q) (813)) (literal (valuationOf q) (814)) (literal (valuationOf q) (818)) (countLit q [-21, -23]) (countLit q [-26, -28]) (count816 q) 2 1 (meaning813 q) (meaning814 q) (meaning818 q) hs
  change valuationOf q 813 = false ∨ valuationOf q 814 = false ∨ valuationOf q 818 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause861 (q : Snake 81) (h : Conditions q) : valuation q 813 = false ∨ valuation q 814 = false ∨ valuation q 818 = true := counterClause861 (baseVal q)

theorem counterClause862 (q : Nat → Bool) : valuationOf q 813 = false ∨ valuationOf q 815 = false ∨ valuationOf q 819 = true := by
  have hs : count816 q = (countLit q [-21, -23]) + (countLit q [-26, -28]) := List.countP_append (p := literal q) (l₁ := [-21, -23]) (l₂ := [-26, -28])
  have hm := merge_two (literal (valuationOf q) (813)) (literal (valuationOf q) (815)) (literal (valuationOf q) (819)) (countLit q [-21, -23]) (countLit q [-26, -28]) (count816 q) 2 2 (meaning813 q) (meaning815 q) (meaning819 q) hs
  change valuationOf q 813 = false ∨ valuationOf q 815 = false ∨ valuationOf q 819 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause862 (q : Snake 81) (h : Conditions q) : valuation q 813 = false ∨ valuation q 815 = false ∨ valuation q 819 = true := counterClause862 (baseVal q)

theorem counterClause863 (q : Nat → Bool) : valuationOf q 816 = false ∨ valuationOf q 820 = true := by
  have hs : count820 q = (countLit q [-15, -16, -19]) + (countLit q [-21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -19]) (l₂ := [-21, -23, -26, -28])
  have hm := merge_right (literal (valuationOf q) (816)) (literal (valuationOf q) (820)) (countLit q [-15, -16, -19]) (countLit q [-21, -23, -26, -28]) (count820 q) 1 (meaning816 q) (meaning820 q) hs
  change valuationOf q 816 = false ∨ valuationOf q 820 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause863 (q : Snake 81) (h : Conditions q) : valuation q 816 = false ∨ valuation q 820 = true := counterClause863 (baseVal q)

theorem counterClause864 (q : Nat → Bool) : valuationOf q 817 = false ∨ valuationOf q 821 = true := by
  have hs : count820 q = (countLit q [-15, -16, -19]) + (countLit q [-21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -19]) (l₂ := [-21, -23, -26, -28])
  have hm := merge_right (literal (valuationOf q) (817)) (literal (valuationOf q) (821)) (countLit q [-15, -16, -19]) (countLit q [-21, -23, -26, -28]) (count820 q) 2 (meaning817 q) (meaning821 q) hs
  change valuationOf q 817 = false ∨ valuationOf q 821 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause864 (q : Snake 81) (h : Conditions q) : valuation q 817 = false ∨ valuation q 821 = true := counterClause864 (baseVal q)

theorem block26 (q : Snake 81) (h : Conditions q) : B112E257.Block26 (valuation q) :=
  ⟨clause833 q h, clause834 q h, clause835 q h, clause836 q h, clause837 q h, clause838 q h, clause839 q h, clause840 q h, clause841 q h, clause842 q h, clause843 q h, clause844 q h, clause845 q h, clause846 q h, clause847 q h, clause848 q h, clause849 q h, clause850 q h, clause851 q h, clause852 q h, clause853 q h, clause854 q h, clause855 q h, clause856 q h, clause857 q h, clause858 q h, clause859 q h, clause860 q h, clause861 q h, clause862 q h, clause863 q h, clause864 q h⟩

end
end Snake9.Regrowth.E112257
