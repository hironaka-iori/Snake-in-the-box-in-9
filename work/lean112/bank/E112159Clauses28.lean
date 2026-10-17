import E112159Semantics
import B112E159Inputs
namespace Snake9.Regrowth.E112159
noncomputable section
local instance blockDec28 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause897 (q : Nat → Bool) : valuationOf q 106 = true ∨ valuationOf q 108 = true ∨ valuationOf q 1015 = true := by
  have hs : count1014 q = (countLit q [-106]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-106]) (l₂ := [-108])
  have hm := merge_two (literal (valuationOf q) (-106)) (literal (valuationOf q) (-108)) (literal (valuationOf q) (1015)) (countLit q [-106]) (countLit q [-108]) (count1014 q) 1 1 (meaningNeg106 q) (meaningNeg108 q) (meaning1015 q) hs
  change (! (valuationOf q 106)) = false ∨ (! (valuationOf q 108)) = false ∨ valuationOf q 1015 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause897 (q : Snake 81) (h : Conditions q) : valuation q 106 = true ∨ valuation q 108 = true ∨ valuation q 1015 = true := counterClause897 (baseVal q)

theorem counterClause898 (q : Nat → Bool) : valuationOf q 1014 = false ∨ valuationOf q 1016 = true := by
  have hs : count1016 q = (countLit q [-104, -105]) + (countLit q [-106, -108]) := List.countP_append (p := literal q) (l₁ := [-104, -105]) (l₂ := [-106, -108])
  have hm := merge_right (literal (valuationOf q) (1014)) (literal (valuationOf q) (1016)) (countLit q [-104, -105]) (countLit q [-106, -108]) (count1016 q) 1 (meaning1014 q) (meaning1016 q) hs
  change valuationOf q 1014 = false ∨ valuationOf q 1016 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause898 (q : Snake 81) (h : Conditions q) : valuation q 1014 = false ∨ valuation q 1016 = true := counterClause898 (baseVal q)

theorem counterClause899 (q : Nat → Bool) : valuationOf q 1015 = false ∨ valuationOf q 1017 = true := by
  have hs : count1016 q = (countLit q [-104, -105]) + (countLit q [-106, -108]) := List.countP_append (p := literal q) (l₁ := [-104, -105]) (l₂ := [-106, -108])
  have hm := merge_right (literal (valuationOf q) (1015)) (literal (valuationOf q) (1017)) (countLit q [-104, -105]) (countLit q [-106, -108]) (count1016 q) 2 (meaning1015 q) (meaning1017 q) hs
  change valuationOf q 1015 = false ∨ valuationOf q 1017 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause899 (q : Snake 81) (h : Conditions q) : valuation q 1015 = false ∨ valuation q 1017 = true := counterClause899 (baseVal q)

theorem counterClause900 (q : Nat → Bool) : valuationOf q 1012 = false ∨ valuationOf q 1016 = true := by
  have hs : count1016 q = (countLit q [-104, -105]) + (countLit q [-106, -108]) := List.countP_append (p := literal q) (l₁ := [-104, -105]) (l₂ := [-106, -108])
  have hm := merge_left (literal (valuationOf q) (1012)) (literal (valuationOf q) (1016)) (countLit q [-104, -105]) (countLit q [-106, -108]) (count1016 q) 1 (meaning1012 q) (meaning1016 q) hs
  change valuationOf q 1012 = false ∨ valuationOf q 1016 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause900 (q : Snake 81) (h : Conditions q) : valuation q 1012 = false ∨ valuation q 1016 = true := counterClause900 (baseVal q)

theorem counterClause901 (q : Nat → Bool) : valuationOf q 1012 = false ∨ valuationOf q 1014 = false ∨ valuationOf q 1017 = true := by
  have hs : count1016 q = (countLit q [-104, -105]) + (countLit q [-106, -108]) := List.countP_append (p := literal q) (l₁ := [-104, -105]) (l₂ := [-106, -108])
  have hm := merge_two (literal (valuationOf q) (1012)) (literal (valuationOf q) (1014)) (literal (valuationOf q) (1017)) (countLit q [-104, -105]) (countLit q [-106, -108]) (count1016 q) 1 1 (meaning1012 q) (meaning1014 q) (meaning1017 q) hs
  change valuationOf q 1012 = false ∨ valuationOf q 1014 = false ∨ valuationOf q 1017 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause901 (q : Snake 81) (h : Conditions q) : valuation q 1012 = false ∨ valuation q 1014 = false ∨ valuation q 1017 = true := counterClause901 (baseVal q)

theorem counterClause902 (q : Nat → Bool) : valuationOf q 1012 = false ∨ valuationOf q 1015 = false ∨ valuationOf q 1018 = true := by
  have hs : count1016 q = (countLit q [-104, -105]) + (countLit q [-106, -108]) := List.countP_append (p := literal q) (l₁ := [-104, -105]) (l₂ := [-106, -108])
  have hm := merge_two (literal (valuationOf q) (1012)) (literal (valuationOf q) (1015)) (literal (valuationOf q) (1018)) (countLit q [-104, -105]) (countLit q [-106, -108]) (count1016 q) 1 2 (meaning1012 q) (meaning1015 q) (meaning1018 q) hs
  change valuationOf q 1012 = false ∨ valuationOf q 1015 = false ∨ valuationOf q 1018 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause902 (q : Snake 81) (h : Conditions q) : valuation q 1012 = false ∨ valuation q 1015 = false ∨ valuation q 1018 = true := counterClause902 (baseVal q)

theorem counterClause903 (q : Nat → Bool) : valuationOf q 1013 = false ∨ valuationOf q 1017 = true := by
  have hs : count1016 q = (countLit q [-104, -105]) + (countLit q [-106, -108]) := List.countP_append (p := literal q) (l₁ := [-104, -105]) (l₂ := [-106, -108])
  have hm := merge_left (literal (valuationOf q) (1013)) (literal (valuationOf q) (1017)) (countLit q [-104, -105]) (countLit q [-106, -108]) (count1016 q) 2 (meaning1013 q) (meaning1017 q) hs
  change valuationOf q 1013 = false ∨ valuationOf q 1017 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause903 (q : Snake 81) (h : Conditions q) : valuation q 1013 = false ∨ valuation q 1017 = true := counterClause903 (baseVal q)

theorem counterClause904 (q : Nat → Bool) : valuationOf q 1013 = false ∨ valuationOf q 1014 = false ∨ valuationOf q 1018 = true := by
  have hs : count1016 q = (countLit q [-104, -105]) + (countLit q [-106, -108]) := List.countP_append (p := literal q) (l₁ := [-104, -105]) (l₂ := [-106, -108])
  have hm := merge_two (literal (valuationOf q) (1013)) (literal (valuationOf q) (1014)) (literal (valuationOf q) (1018)) (countLit q [-104, -105]) (countLit q [-106, -108]) (count1016 q) 2 1 (meaning1013 q) (meaning1014 q) (meaning1018 q) hs
  change valuationOf q 1013 = false ∨ valuationOf q 1014 = false ∨ valuationOf q 1018 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause904 (q : Snake 81) (h : Conditions q) : valuation q 1013 = false ∨ valuation q 1014 = false ∨ valuation q 1018 = true := counterClause904 (baseVal q)

theorem counterClause905 (q : Nat → Bool) : valuationOf q 113 = true ∨ valuationOf q 1020 = true := by
  have hs : count1020 q = (countLit q [-111]) + (countLit q [-113]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-113])
  have hm := merge_right (literal (valuationOf q) (-113)) (literal (valuationOf q) (1020)) (countLit q [-111]) (countLit q [-113]) (count1020 q) 1 (meaningNeg113 q) (meaning1020 q) hs
  change (! (valuationOf q 113)) = false ∨ valuationOf q 1020 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause905 (q : Snake 81) (h : Conditions q) : valuation q 113 = true ∨ valuation q 1020 = true := counterClause905 (baseVal q)

theorem counterClause906 (q : Nat → Bool) : valuationOf q 111 = true ∨ valuationOf q 1020 = true := by
  have hs : count1020 q = (countLit q [-111]) + (countLit q [-113]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-113])
  have hm := merge_left (literal (valuationOf q) (-111)) (literal (valuationOf q) (1020)) (countLit q [-111]) (countLit q [-113]) (count1020 q) 1 (meaningNeg111 q) (meaning1020 q) hs
  change (! (valuationOf q 111)) = false ∨ valuationOf q 1020 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause906 (q : Snake 81) (h : Conditions q) : valuation q 111 = true ∨ valuation q 1020 = true := counterClause906 (baseVal q)

theorem counterClause907 (q : Nat → Bool) : valuationOf q 111 = true ∨ valuationOf q 113 = true ∨ valuationOf q 1021 = true := by
  have hs : count1020 q = (countLit q [-111]) + (countLit q [-113]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-113])
  have hm := merge_two (literal (valuationOf q) (-111)) (literal (valuationOf q) (-113)) (literal (valuationOf q) (1021)) (countLit q [-111]) (countLit q [-113]) (count1020 q) 1 1 (meaningNeg111 q) (meaningNeg113 q) (meaning1021 q) hs
  change (! (valuationOf q 111)) = false ∨ (! (valuationOf q 113)) = false ∨ valuationOf q 1021 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause907 (q : Snake 81) (h : Conditions q) : valuation q 111 = true ∨ valuation q 113 = true ∨ valuation q 1021 = true := counterClause907 (baseVal q)

theorem counterClause908 (q : Nat → Bool) : valuationOf q 117 = true ∨ valuationOf q 1022 = true := by
  have hs : count1022 q = (countLit q [-115]) + (countLit q [-117]) := List.countP_append (p := literal q) (l₁ := [-115]) (l₂ := [-117])
  have hm := merge_right (literal (valuationOf q) (-117)) (literal (valuationOf q) (1022)) (countLit q [-115]) (countLit q [-117]) (count1022 q) 1 (meaningNeg117 q) (meaning1022 q) hs
  change (! (valuationOf q 117)) = false ∨ valuationOf q 1022 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause908 (q : Snake 81) (h : Conditions q) : valuation q 117 = true ∨ valuation q 1022 = true := counterClause908 (baseVal q)

theorem counterClause909 (q : Nat → Bool) : valuationOf q 115 = true ∨ valuationOf q 1022 = true := by
  have hs : count1022 q = (countLit q [-115]) + (countLit q [-117]) := List.countP_append (p := literal q) (l₁ := [-115]) (l₂ := [-117])
  have hm := merge_left (literal (valuationOf q) (-115)) (literal (valuationOf q) (1022)) (countLit q [-115]) (countLit q [-117]) (count1022 q) 1 (meaningNeg115 q) (meaning1022 q) hs
  change (! (valuationOf q 115)) = false ∨ valuationOf q 1022 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause909 (q : Snake 81) (h : Conditions q) : valuation q 115 = true ∨ valuation q 1022 = true := counterClause909 (baseVal q)

theorem counterClause910 (q : Nat → Bool) : valuationOf q 115 = true ∨ valuationOf q 117 = true ∨ valuationOf q 1023 = true := by
  have hs : count1022 q = (countLit q [-115]) + (countLit q [-117]) := List.countP_append (p := literal q) (l₁ := [-115]) (l₂ := [-117])
  have hm := merge_two (literal (valuationOf q) (-115)) (literal (valuationOf q) (-117)) (literal (valuationOf q) (1023)) (countLit q [-115]) (countLit q [-117]) (count1022 q) 1 1 (meaningNeg115 q) (meaningNeg117 q) (meaning1023 q) hs
  change (! (valuationOf q 115)) = false ∨ (! (valuationOf q 117)) = false ∨ valuationOf q 1023 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause910 (q : Snake 81) (h : Conditions q) : valuation q 115 = true ∨ valuation q 117 = true ∨ valuation q 1023 = true := counterClause910 (baseVal q)

theorem counterClause911 (q : Nat → Bool) : valuationOf q 1022 = false ∨ valuationOf q 1024 = true := by
  have hs : count1024 q = (countLit q [-111, -113]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-111, -113]) (l₂ := [-115, -117])
  have hm := merge_right (literal (valuationOf q) (1022)) (literal (valuationOf q) (1024)) (countLit q [-111, -113]) (countLit q [-115, -117]) (count1024 q) 1 (meaning1022 q) (meaning1024 q) hs
  change valuationOf q 1022 = false ∨ valuationOf q 1024 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause911 (q : Snake 81) (h : Conditions q) : valuation q 1022 = false ∨ valuation q 1024 = true := counterClause911 (baseVal q)

theorem counterClause912 (q : Nat → Bool) : valuationOf q 1023 = false ∨ valuationOf q 1025 = true := by
  have hs : count1024 q = (countLit q [-111, -113]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-111, -113]) (l₂ := [-115, -117])
  have hm := merge_right (literal (valuationOf q) (1023)) (literal (valuationOf q) (1025)) (countLit q [-111, -113]) (countLit q [-115, -117]) (count1024 q) 2 (meaning1023 q) (meaning1025 q) hs
  change valuationOf q 1023 = false ∨ valuationOf q 1025 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause912 (q : Snake 81) (h : Conditions q) : valuation q 1023 = false ∨ valuation q 1025 = true := counterClause912 (baseVal q)

theorem counterClause913 (q : Nat → Bool) : valuationOf q 1020 = false ∨ valuationOf q 1024 = true := by
  have hs : count1024 q = (countLit q [-111, -113]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-111, -113]) (l₂ := [-115, -117])
  have hm := merge_left (literal (valuationOf q) (1020)) (literal (valuationOf q) (1024)) (countLit q [-111, -113]) (countLit q [-115, -117]) (count1024 q) 1 (meaning1020 q) (meaning1024 q) hs
  change valuationOf q 1020 = false ∨ valuationOf q 1024 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause913 (q : Snake 81) (h : Conditions q) : valuation q 1020 = false ∨ valuation q 1024 = true := counterClause913 (baseVal q)

theorem counterClause914 (q : Nat → Bool) : valuationOf q 1020 = false ∨ valuationOf q 1022 = false ∨ valuationOf q 1025 = true := by
  have hs : count1024 q = (countLit q [-111, -113]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-111, -113]) (l₂ := [-115, -117])
  have hm := merge_two (literal (valuationOf q) (1020)) (literal (valuationOf q) (1022)) (literal (valuationOf q) (1025)) (countLit q [-111, -113]) (countLit q [-115, -117]) (count1024 q) 1 1 (meaning1020 q) (meaning1022 q) (meaning1025 q) hs
  change valuationOf q 1020 = false ∨ valuationOf q 1022 = false ∨ valuationOf q 1025 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause914 (q : Snake 81) (h : Conditions q) : valuation q 1020 = false ∨ valuation q 1022 = false ∨ valuation q 1025 = true := counterClause914 (baseVal q)

theorem counterClause915 (q : Nat → Bool) : valuationOf q 1020 = false ∨ valuationOf q 1023 = false ∨ valuationOf q 1026 = true := by
  have hs : count1024 q = (countLit q [-111, -113]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-111, -113]) (l₂ := [-115, -117])
  have hm := merge_two (literal (valuationOf q) (1020)) (literal (valuationOf q) (1023)) (literal (valuationOf q) (1026)) (countLit q [-111, -113]) (countLit q [-115, -117]) (count1024 q) 1 2 (meaning1020 q) (meaning1023 q) (meaning1026 q) hs
  change valuationOf q 1020 = false ∨ valuationOf q 1023 = false ∨ valuationOf q 1026 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause915 (q : Snake 81) (h : Conditions q) : valuation q 1020 = false ∨ valuation q 1023 = false ∨ valuation q 1026 = true := counterClause915 (baseVal q)

theorem counterClause916 (q : Nat → Bool) : valuationOf q 1021 = false ∨ valuationOf q 1025 = true := by
  have hs : count1024 q = (countLit q [-111, -113]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-111, -113]) (l₂ := [-115, -117])
  have hm := merge_left (literal (valuationOf q) (1021)) (literal (valuationOf q) (1025)) (countLit q [-111, -113]) (countLit q [-115, -117]) (count1024 q) 2 (meaning1021 q) (meaning1025 q) hs
  change valuationOf q 1021 = false ∨ valuationOf q 1025 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause916 (q : Snake 81) (h : Conditions q) : valuation q 1021 = false ∨ valuation q 1025 = true := counterClause916 (baseVal q)

theorem counterClause917 (q : Nat → Bool) : valuationOf q 1021 = false ∨ valuationOf q 1022 = false ∨ valuationOf q 1026 = true := by
  have hs : count1024 q = (countLit q [-111, -113]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-111, -113]) (l₂ := [-115, -117])
  have hm := merge_two (literal (valuationOf q) (1021)) (literal (valuationOf q) (1022)) (literal (valuationOf q) (1026)) (countLit q [-111, -113]) (countLit q [-115, -117]) (count1024 q) 2 1 (meaning1021 q) (meaning1022 q) (meaning1026 q) hs
  change valuationOf q 1021 = false ∨ valuationOf q 1022 = false ∨ valuationOf q 1026 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause917 (q : Snake 81) (h : Conditions q) : valuation q 1021 = false ∨ valuation q 1022 = false ∨ valuation q 1026 = true := counterClause917 (baseVal q)

theorem counterClause918 (q : Nat → Bool) : valuationOf q 1024 = false ∨ valuationOf q 1028 = true := by
  have hs : count1028 q = (countLit q [-104, -105, -106, -108]) + (countLit q [-111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -105, -106, -108]) (l₂ := [-111, -113, -115, -117])
  have hm := merge_right (literal (valuationOf q) (1024)) (literal (valuationOf q) (1028)) (countLit q [-104, -105, -106, -108]) (countLit q [-111, -113, -115, -117]) (count1028 q) 1 (meaning1024 q) (meaning1028 q) hs
  change valuationOf q 1024 = false ∨ valuationOf q 1028 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause918 (q : Snake 81) (h : Conditions q) : valuation q 1024 = false ∨ valuation q 1028 = true := counterClause918 (baseVal q)

theorem counterClause919 (q : Nat → Bool) : valuationOf q 1025 = false ∨ valuationOf q 1029 = true := by
  have hs : count1028 q = (countLit q [-104, -105, -106, -108]) + (countLit q [-111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -105, -106, -108]) (l₂ := [-111, -113, -115, -117])
  have hm := merge_right (literal (valuationOf q) (1025)) (literal (valuationOf q) (1029)) (countLit q [-104, -105, -106, -108]) (countLit q [-111, -113, -115, -117]) (count1028 q) 2 (meaning1025 q) (meaning1029 q) hs
  change valuationOf q 1025 = false ∨ valuationOf q 1029 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause919 (q : Snake 81) (h : Conditions q) : valuation q 1025 = false ∨ valuation q 1029 = true := counterClause919 (baseVal q)

theorem counterClause920 (q : Nat → Bool) : valuationOf q 1016 = false ∨ valuationOf q 1028 = true := by
  have hs : count1028 q = (countLit q [-104, -105, -106, -108]) + (countLit q [-111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -105, -106, -108]) (l₂ := [-111, -113, -115, -117])
  have hm := merge_left (literal (valuationOf q) (1016)) (literal (valuationOf q) (1028)) (countLit q [-104, -105, -106, -108]) (countLit q [-111, -113, -115, -117]) (count1028 q) 1 (meaning1016 q) (meaning1028 q) hs
  change valuationOf q 1016 = false ∨ valuationOf q 1028 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause920 (q : Snake 81) (h : Conditions q) : valuation q 1016 = false ∨ valuation q 1028 = true := counterClause920 (baseVal q)

theorem counterClause921 (q : Nat → Bool) : valuationOf q 1016 = false ∨ valuationOf q 1024 = false ∨ valuationOf q 1029 = true := by
  have hs : count1028 q = (countLit q [-104, -105, -106, -108]) + (countLit q [-111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -105, -106, -108]) (l₂ := [-111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1016)) (literal (valuationOf q) (1024)) (literal (valuationOf q) (1029)) (countLit q [-104, -105, -106, -108]) (countLit q [-111, -113, -115, -117]) (count1028 q) 1 1 (meaning1016 q) (meaning1024 q) (meaning1029 q) hs
  change valuationOf q 1016 = false ∨ valuationOf q 1024 = false ∨ valuationOf q 1029 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause921 (q : Snake 81) (h : Conditions q) : valuation q 1016 = false ∨ valuation q 1024 = false ∨ valuation q 1029 = true := counterClause921 (baseVal q)

theorem counterClause922 (q : Nat → Bool) : valuationOf q 1016 = false ∨ valuationOf q 1025 = false ∨ valuationOf q 1030 = true := by
  have hs : count1028 q = (countLit q [-104, -105, -106, -108]) + (countLit q [-111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -105, -106, -108]) (l₂ := [-111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1016)) (literal (valuationOf q) (1025)) (literal (valuationOf q) (1030)) (countLit q [-104, -105, -106, -108]) (countLit q [-111, -113, -115, -117]) (count1028 q) 1 2 (meaning1016 q) (meaning1025 q) (meaning1030 q) hs
  change valuationOf q 1016 = false ∨ valuationOf q 1025 = false ∨ valuationOf q 1030 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause922 (q : Snake 81) (h : Conditions q) : valuation q 1016 = false ∨ valuation q 1025 = false ∨ valuation q 1030 = true := counterClause922 (baseVal q)

theorem counterClause923 (q : Nat → Bool) : valuationOf q 1016 = false ∨ valuationOf q 1026 = false ∨ valuationOf q 1031 = true := by
  have hs : count1028 q = (countLit q [-104, -105, -106, -108]) + (countLit q [-111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -105, -106, -108]) (l₂ := [-111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1016)) (literal (valuationOf q) (1026)) (literal (valuationOf q) (1031)) (countLit q [-104, -105, -106, -108]) (countLit q [-111, -113, -115, -117]) (count1028 q) 1 3 (meaning1016 q) (meaning1026 q) (meaning1031 q) hs
  change valuationOf q 1016 = false ∨ valuationOf q 1026 = false ∨ valuationOf q 1031 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause923 (q : Snake 81) (h : Conditions q) : valuation q 1016 = false ∨ valuation q 1026 = false ∨ valuation q 1031 = true := counterClause923 (baseVal q)

theorem counterClause924 (q : Nat → Bool) : valuationOf q 1017 = false ∨ valuationOf q 1029 = true := by
  have hs : count1028 q = (countLit q [-104, -105, -106, -108]) + (countLit q [-111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -105, -106, -108]) (l₂ := [-111, -113, -115, -117])
  have hm := merge_left (literal (valuationOf q) (1017)) (literal (valuationOf q) (1029)) (countLit q [-104, -105, -106, -108]) (countLit q [-111, -113, -115, -117]) (count1028 q) 2 (meaning1017 q) (meaning1029 q) hs
  change valuationOf q 1017 = false ∨ valuationOf q 1029 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause924 (q : Snake 81) (h : Conditions q) : valuation q 1017 = false ∨ valuation q 1029 = true := counterClause924 (baseVal q)

theorem counterClause925 (q : Nat → Bool) : valuationOf q 1017 = false ∨ valuationOf q 1024 = false ∨ valuationOf q 1030 = true := by
  have hs : count1028 q = (countLit q [-104, -105, -106, -108]) + (countLit q [-111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -105, -106, -108]) (l₂ := [-111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1017)) (literal (valuationOf q) (1024)) (literal (valuationOf q) (1030)) (countLit q [-104, -105, -106, -108]) (countLit q [-111, -113, -115, -117]) (count1028 q) 2 1 (meaning1017 q) (meaning1024 q) (meaning1030 q) hs
  change valuationOf q 1017 = false ∨ valuationOf q 1024 = false ∨ valuationOf q 1030 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause925 (q : Snake 81) (h : Conditions q) : valuation q 1017 = false ∨ valuation q 1024 = false ∨ valuation q 1030 = true := counterClause925 (baseVal q)

theorem counterClause926 (q : Nat → Bool) : valuationOf q 1017 = false ∨ valuationOf q 1025 = false ∨ valuationOf q 1031 = true := by
  have hs : count1028 q = (countLit q [-104, -105, -106, -108]) + (countLit q [-111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -105, -106, -108]) (l₂ := [-111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1017)) (literal (valuationOf q) (1025)) (literal (valuationOf q) (1031)) (countLit q [-104, -105, -106, -108]) (countLit q [-111, -113, -115, -117]) (count1028 q) 2 2 (meaning1017 q) (meaning1025 q) (meaning1031 q) hs
  change valuationOf q 1017 = false ∨ valuationOf q 1025 = false ∨ valuationOf q 1031 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause926 (q : Snake 81) (h : Conditions q) : valuation q 1017 = false ∨ valuation q 1025 = false ∨ valuation q 1031 = true := counterClause926 (baseVal q)

theorem counterClause927 (q : Nat → Bool) : valuationOf q 1017 = false ∨ valuationOf q 1026 = false ∨ valuationOf q 1032 = true := by
  have hs : count1028 q = (countLit q [-104, -105, -106, -108]) + (countLit q [-111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -105, -106, -108]) (l₂ := [-111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1017)) (literal (valuationOf q) (1026)) (literal (valuationOf q) (1032)) (countLit q [-104, -105, -106, -108]) (countLit q [-111, -113, -115, -117]) (count1028 q) 2 3 (meaning1017 q) (meaning1026 q) (meaning1032 q) hs
  change valuationOf q 1017 = false ∨ valuationOf q 1026 = false ∨ valuationOf q 1032 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause927 (q : Snake 81) (h : Conditions q) : valuation q 1017 = false ∨ valuation q 1026 = false ∨ valuation q 1032 = true := counterClause927 (baseVal q)

theorem counterClause928 (q : Nat → Bool) : valuationOf q 1018 = false ∨ valuationOf q 1024 = false ∨ valuationOf q 1031 = true := by
  have hs : count1028 q = (countLit q [-104, -105, -106, -108]) + (countLit q [-111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -105, -106, -108]) (l₂ := [-111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1018)) (literal (valuationOf q) (1024)) (literal (valuationOf q) (1031)) (countLit q [-104, -105, -106, -108]) (countLit q [-111, -113, -115, -117]) (count1028 q) 3 1 (meaning1018 q) (meaning1024 q) (meaning1031 q) hs
  change valuationOf q 1018 = false ∨ valuationOf q 1024 = false ∨ valuationOf q 1031 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause928 (q : Snake 81) (h : Conditions q) : valuation q 1018 = false ∨ valuation q 1024 = false ∨ valuation q 1031 = true := counterClause928 (baseVal q)

theorem block28 (q : Snake 81) (h : Conditions q) : B112E159.Block28 (valuation q) :=
  ⟨clause897 q h, clause898 q h, clause899 q h, clause900 q h, clause901 q h, clause902 q h, clause903 q h, clause904 q h, clause905 q h, clause906 q h, clause907 q h, clause908 q h, clause909 q h, clause910 q h, clause911 q h, clause912 q h, clause913 q h, clause914 q h, clause915 q h, clause916 q h, clause917 q h, clause918 q h, clause919 q h, clause920 q h, clause921 q h, clause922 q h, clause923 q h, clause924 q h, clause925 q h, clause926 q h, clause927 q h, clause928 q h⟩

end
end Snake9.Regrowth.E112159
