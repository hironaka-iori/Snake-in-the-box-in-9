import E112051Semantics
import B112E051Inputs
namespace Snake9.Regrowth.E112051
noncomputable section
local instance blockDec21 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause673 (q : Nat → Bool) : valuationOf q 934 = false ∨ valuationOf q 936 = true := by
  have hs : count935 q = (countLit q [-76, -78]) + (countLit q [-80, -81]) := List.countP_append (p := literal q) (l₁ := [-76, -78]) (l₂ := [-80, -81])
  have hm := merge_right (literal (valuationOf q) (934)) (literal (valuationOf q) (936)) (countLit q [-76, -78]) (countLit q [-80, -81]) (count935 q) 2 (meaning934 q) (meaning936 q) hs
  change valuationOf q 934 = false ∨ valuationOf q 936 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause673 (q : Snake 81) (h : Conditions q) : valuation q 934 = false ∨ valuation q 936 = true := counterClause673 (baseVal q)

theorem counterClause674 (q : Nat → Bool) : valuationOf q 931 = false ∨ valuationOf q 935 = true := by
  have hs : count935 q = (countLit q [-76, -78]) + (countLit q [-80, -81]) := List.countP_append (p := literal q) (l₁ := [-76, -78]) (l₂ := [-80, -81])
  have hm := merge_left (literal (valuationOf q) (931)) (literal (valuationOf q) (935)) (countLit q [-76, -78]) (countLit q [-80, -81]) (count935 q) 1 (meaning931 q) (meaning935 q) hs
  change valuationOf q 931 = false ∨ valuationOf q 935 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause674 (q : Snake 81) (h : Conditions q) : valuation q 931 = false ∨ valuation q 935 = true := counterClause674 (baseVal q)

theorem counterClause675 (q : Nat → Bool) : valuationOf q 931 = false ∨ valuationOf q 933 = false ∨ valuationOf q 936 = true := by
  have hs : count935 q = (countLit q [-76, -78]) + (countLit q [-80, -81]) := List.countP_append (p := literal q) (l₁ := [-76, -78]) (l₂ := [-80, -81])
  have hm := merge_two (literal (valuationOf q) (931)) (literal (valuationOf q) (933)) (literal (valuationOf q) (936)) (countLit q [-76, -78]) (countLit q [-80, -81]) (count935 q) 1 1 (meaning931 q) (meaning933 q) (meaning936 q) hs
  change valuationOf q 931 = false ∨ valuationOf q 933 = false ∨ valuationOf q 936 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause675 (q : Snake 81) (h : Conditions q) : valuation q 931 = false ∨ valuation q 933 = false ∨ valuation q 936 = true := counterClause675 (baseVal q)

theorem counterClause676 (q : Nat → Bool) : valuationOf q 931 = false ∨ valuationOf q 934 = false ∨ valuationOf q 937 = true := by
  have hs : count935 q = (countLit q [-76, -78]) + (countLit q [-80, -81]) := List.countP_append (p := literal q) (l₁ := [-76, -78]) (l₂ := [-80, -81])
  have hm := merge_two (literal (valuationOf q) (931)) (literal (valuationOf q) (934)) (literal (valuationOf q) (937)) (countLit q [-76, -78]) (countLit q [-80, -81]) (count935 q) 1 2 (meaning931 q) (meaning934 q) (meaning937 q) hs
  change valuationOf q 931 = false ∨ valuationOf q 934 = false ∨ valuationOf q 937 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause676 (q : Snake 81) (h : Conditions q) : valuation q 931 = false ∨ valuation q 934 = false ∨ valuation q 937 = true := counterClause676 (baseVal q)

theorem counterClause677 (q : Nat → Bool) : valuationOf q 932 = false ∨ valuationOf q 936 = true := by
  have hs : count935 q = (countLit q [-76, -78]) + (countLit q [-80, -81]) := List.countP_append (p := literal q) (l₁ := [-76, -78]) (l₂ := [-80, -81])
  have hm := merge_left (literal (valuationOf q) (932)) (literal (valuationOf q) (936)) (countLit q [-76, -78]) (countLit q [-80, -81]) (count935 q) 2 (meaning932 q) (meaning936 q) hs
  change valuationOf q 932 = false ∨ valuationOf q 936 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause677 (q : Snake 81) (h : Conditions q) : valuation q 932 = false ∨ valuation q 936 = true := counterClause677 (baseVal q)

theorem counterClause678 (q : Nat → Bool) : valuationOf q 935 = false ∨ valuationOf q 939 = true := by
  have hs : count939 q = (countLit q [-72, -73, -74]) + (countLit q [-76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -74]) (l₂ := [-76, -78, -80, -81])
  have hm := merge_right (literal (valuationOf q) (935)) (literal (valuationOf q) (939)) (countLit q [-72, -73, -74]) (countLit q [-76, -78, -80, -81]) (count939 q) 1 (meaning935 q) (meaning939 q) hs
  change valuationOf q 935 = false ∨ valuationOf q 939 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause678 (q : Snake 81) (h : Conditions q) : valuation q 935 = false ∨ valuation q 939 = true := counterClause678 (baseVal q)

theorem counterClause679 (q : Nat → Bool) : valuationOf q 936 = false ∨ valuationOf q 940 = true := by
  have hs : count939 q = (countLit q [-72, -73, -74]) + (countLit q [-76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -74]) (l₂ := [-76, -78, -80, -81])
  have hm := merge_right (literal (valuationOf q) (936)) (literal (valuationOf q) (940)) (countLit q [-72, -73, -74]) (countLit q [-76, -78, -80, -81]) (count939 q) 2 (meaning936 q) (meaning940 q) hs
  change valuationOf q 936 = false ∨ valuationOf q 940 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause679 (q : Snake 81) (h : Conditions q) : valuation q 936 = false ∨ valuation q 940 = true := counterClause679 (baseVal q)

theorem counterClause680 (q : Nat → Bool) : valuationOf q 937 = false ∨ valuationOf q 941 = true := by
  have hs : count939 q = (countLit q [-72, -73, -74]) + (countLit q [-76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -74]) (l₂ := [-76, -78, -80, -81])
  have hm := merge_right (literal (valuationOf q) (937)) (literal (valuationOf q) (941)) (countLit q [-72, -73, -74]) (countLit q [-76, -78, -80, -81]) (count939 q) 3 (meaning937 q) (meaning941 q) hs
  change valuationOf q 937 = false ∨ valuationOf q 941 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause680 (q : Snake 81) (h : Conditions q) : valuation q 937 = false ∨ valuation q 941 = true := counterClause680 (baseVal q)

theorem counterClause681 (q : Nat → Bool) : valuationOf q 928 = false ∨ valuationOf q 935 = false ∨ valuationOf q 940 = true := by
  have hs : count939 q = (countLit q [-72, -73, -74]) + (countLit q [-76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -74]) (l₂ := [-76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (928)) (literal (valuationOf q) (935)) (literal (valuationOf q) (940)) (countLit q [-72, -73, -74]) (countLit q [-76, -78, -80, -81]) (count939 q) 1 1 (meaning928 q) (meaning935 q) (meaning940 q) hs
  change valuationOf q 928 = false ∨ valuationOf q 935 = false ∨ valuationOf q 940 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause681 (q : Snake 81) (h : Conditions q) : valuation q 928 = false ∨ valuation q 935 = false ∨ valuation q 940 = true := counterClause681 (baseVal q)

theorem counterClause682 (q : Nat → Bool) : valuationOf q 928 = false ∨ valuationOf q 936 = false ∨ valuationOf q 941 = true := by
  have hs : count939 q = (countLit q [-72, -73, -74]) + (countLit q [-76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -74]) (l₂ := [-76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (928)) (literal (valuationOf q) (936)) (literal (valuationOf q) (941)) (countLit q [-72, -73, -74]) (countLit q [-76, -78, -80, -81]) (count939 q) 1 2 (meaning928 q) (meaning936 q) (meaning941 q) hs
  change valuationOf q 928 = false ∨ valuationOf q 936 = false ∨ valuationOf q 941 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause682 (q : Snake 81) (h : Conditions q) : valuation q 928 = false ∨ valuation q 936 = false ∨ valuation q 941 = true := counterClause682 (baseVal q)

theorem counterClause683 (q : Nat → Bool) : valuationOf q 928 = false ∨ valuationOf q 937 = false ∨ valuationOf q 942 = true := by
  have hs : count939 q = (countLit q [-72, -73, -74]) + (countLit q [-76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -74]) (l₂ := [-76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (928)) (literal (valuationOf q) (937)) (literal (valuationOf q) (942)) (countLit q [-72, -73, -74]) (countLit q [-76, -78, -80, -81]) (count939 q) 1 3 (meaning928 q) (meaning937 q) (meaning942 q) hs
  change valuationOf q 928 = false ∨ valuationOf q 937 = false ∨ valuationOf q 942 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause683 (q : Snake 81) (h : Conditions q) : valuation q 928 = false ∨ valuation q 937 = false ∨ valuation q 942 = true := counterClause683 (baseVal q)

theorem counterClause684 (q : Nat → Bool) : valuationOf q 929 = false ∨ valuationOf q 935 = false ∨ valuationOf q 941 = true := by
  have hs : count939 q = (countLit q [-72, -73, -74]) + (countLit q [-76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -74]) (l₂ := [-76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (929)) (literal (valuationOf q) (935)) (literal (valuationOf q) (941)) (countLit q [-72, -73, -74]) (countLit q [-76, -78, -80, -81]) (count939 q) 2 1 (meaning929 q) (meaning935 q) (meaning941 q) hs
  change valuationOf q 929 = false ∨ valuationOf q 935 = false ∨ valuationOf q 941 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause684 (q : Snake 81) (h : Conditions q) : valuation q 929 = false ∨ valuation q 935 = false ∨ valuation q 941 = true := counterClause684 (baseVal q)

theorem counterClause685 (q : Nat → Bool) : valuationOf q 929 = false ∨ valuationOf q 936 = false ∨ valuationOf q 942 = true := by
  have hs : count939 q = (countLit q [-72, -73, -74]) + (countLit q [-76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -74]) (l₂ := [-76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (929)) (literal (valuationOf q) (936)) (literal (valuationOf q) (942)) (countLit q [-72, -73, -74]) (countLit q [-76, -78, -80, -81]) (count939 q) 2 2 (meaning929 q) (meaning936 q) (meaning942 q) hs
  change valuationOf q 929 = false ∨ valuationOf q 936 = false ∨ valuationOf q 942 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause685 (q : Snake 81) (h : Conditions q) : valuation q 929 = false ∨ valuation q 936 = false ∨ valuation q 942 = true := counterClause685 (baseVal q)

theorem counterClause686 (q : Nat → Bool) : valuationOf q 930 = false ∨ valuationOf q 935 = false ∨ valuationOf q 942 = true := by
  have hs : count939 q = (countLit q [-72, -73, -74]) + (countLit q [-76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -74]) (l₂ := [-76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (930)) (literal (valuationOf q) (935)) (literal (valuationOf q) (942)) (countLit q [-72, -73, -74]) (countLit q [-76, -78, -80, -81]) (count939 q) 3 1 (meaning930 q) (meaning935 q) (meaning942 q) hs
  change valuationOf q 930 = false ∨ valuationOf q 935 = false ∨ valuationOf q 942 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause686 (q : Snake 81) (h : Conditions q) : valuation q 930 = false ∨ valuation q 935 = false ∨ valuation q 942 = true := counterClause686 (baseVal q)

theorem counterClause687 (q : Nat → Bool) : valuationOf q 930 = false ∨ valuationOf q 936 = false ∨ valuationOf q 943 = true := by
  have hs : count939 q = (countLit q [-72, -73, -74]) + (countLit q [-76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -74]) (l₂ := [-76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (930)) (literal (valuationOf q) (936)) (literal (valuationOf q) (943)) (countLit q [-72, -73, -74]) (countLit q [-76, -78, -80, -81]) (count939 q) 3 2 (meaning930 q) (meaning936 q) (meaning943 q) hs
  change valuationOf q 930 = false ∨ valuationOf q 936 = false ∨ valuationOf q 943 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause687 (q : Snake 81) (h : Conditions q) : valuation q 930 = false ∨ valuation q 936 = false ∨ valuation q 943 = true := counterClause687 (baseVal q)

theorem counterClause688 (q : Nat → Bool) : valuationOf q 919 = false ∨ valuationOf q 941 = false ∨ valuationOf q 949 = true := by
  have hs : count946 q = (countLit q [-57, -58, -59, -64, -65, -67, -70]) + (countLit q [-72, -73, -74, -76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -59, -64, -65, -67, -70]) (l₂ := [-72, -73, -74, -76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (919)) (literal (valuationOf q) (941)) (literal (valuationOf q) (949)) (countLit q [-57, -58, -59, -64, -65, -67, -70]) (countLit q [-72, -73, -74, -76, -78, -80, -81]) (count946 q) 1 3 (meaning919 q) (meaning941 q) (meaning949 q) hs
  change valuationOf q 919 = false ∨ valuationOf q 941 = false ∨ valuationOf q 949 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause688 (q : Snake 81) (h : Conditions q) : valuation q 919 = false ∨ valuation q 941 = false ∨ valuation q 949 = true := counterClause688 (baseVal q)

theorem counterClause689 (q : Nat → Bool) : valuationOf q 919 = false ∨ valuationOf q 942 = false ∨ valuationOf q 950 = true := by
  have hs : count946 q = (countLit q [-57, -58, -59, -64, -65, -67, -70]) + (countLit q [-72, -73, -74, -76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -59, -64, -65, -67, -70]) (l₂ := [-72, -73, -74, -76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (919)) (literal (valuationOf q) (942)) (literal (valuationOf q) (950)) (countLit q [-57, -58, -59, -64, -65, -67, -70]) (countLit q [-72, -73, -74, -76, -78, -80, -81]) (count946 q) 1 4 (meaning919 q) (meaning942 q) (meaning950 q) hs
  change valuationOf q 919 = false ∨ valuationOf q 942 = false ∨ valuationOf q 950 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause689 (q : Snake 81) (h : Conditions q) : valuation q 919 = false ∨ valuation q 942 = false ∨ valuation q 950 = true := counterClause689 (baseVal q)

theorem counterClause690 (q : Nat → Bool) : valuationOf q 920 = false ∨ valuationOf q 940 = false ∨ valuationOf q 949 = true := by
  have hs : count946 q = (countLit q [-57, -58, -59, -64, -65, -67, -70]) + (countLit q [-72, -73, -74, -76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -59, -64, -65, -67, -70]) (l₂ := [-72, -73, -74, -76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (920)) (literal (valuationOf q) (940)) (literal (valuationOf q) (949)) (countLit q [-57, -58, -59, -64, -65, -67, -70]) (countLit q [-72, -73, -74, -76, -78, -80, -81]) (count946 q) 2 2 (meaning920 q) (meaning940 q) (meaning949 q) hs
  change valuationOf q 920 = false ∨ valuationOf q 940 = false ∨ valuationOf q 949 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause690 (q : Snake 81) (h : Conditions q) : valuation q 920 = false ∨ valuation q 940 = false ∨ valuation q 949 = true := counterClause690 (baseVal q)

theorem counterClause691 (q : Nat → Bool) : valuationOf q 920 = false ∨ valuationOf q 941 = false ∨ valuationOf q 950 = true := by
  have hs : count946 q = (countLit q [-57, -58, -59, -64, -65, -67, -70]) + (countLit q [-72, -73, -74, -76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -59, -64, -65, -67, -70]) (l₂ := [-72, -73, -74, -76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (920)) (literal (valuationOf q) (941)) (literal (valuationOf q) (950)) (countLit q [-57, -58, -59, -64, -65, -67, -70]) (countLit q [-72, -73, -74, -76, -78, -80, -81]) (count946 q) 2 3 (meaning920 q) (meaning941 q) (meaning950 q) hs
  change valuationOf q 920 = false ∨ valuationOf q 941 = false ∨ valuationOf q 950 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause691 (q : Snake 81) (h : Conditions q) : valuation q 920 = false ∨ valuation q 941 = false ∨ valuation q 950 = true := counterClause691 (baseVal q)

theorem counterClause692 (q : Nat → Bool) : valuationOf q 920 = false ∨ valuationOf q 942 = false ∨ valuationOf q 951 = true := by
  have hs : count946 q = (countLit q [-57, -58, -59, -64, -65, -67, -70]) + (countLit q [-72, -73, -74, -76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -59, -64, -65, -67, -70]) (l₂ := [-72, -73, -74, -76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (920)) (literal (valuationOf q) (942)) (literal (valuationOf q) (951)) (countLit q [-57, -58, -59, -64, -65, -67, -70]) (countLit q [-72, -73, -74, -76, -78, -80, -81]) (count946 q) 2 4 (meaning920 q) (meaning942 q) (meaning951 q) hs
  change valuationOf q 920 = false ∨ valuationOf q 942 = false ∨ valuationOf q 951 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause692 (q : Snake 81) (h : Conditions q) : valuation q 920 = false ∨ valuation q 942 = false ∨ valuation q 951 = true := counterClause692 (baseVal q)

theorem counterClause693 (q : Nat → Bool) : valuationOf q 920 = false ∨ valuationOf q 943 = false ∨ valuationOf q 952 = true := by
  have hs : count946 q = (countLit q [-57, -58, -59, -64, -65, -67, -70]) + (countLit q [-72, -73, -74, -76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -59, -64, -65, -67, -70]) (l₂ := [-72, -73, -74, -76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (920)) (literal (valuationOf q) (943)) (literal (valuationOf q) (952)) (countLit q [-57, -58, -59, -64, -65, -67, -70]) (countLit q [-72, -73, -74, -76, -78, -80, -81]) (count946 q) 2 5 (meaning920 q) (meaning943 q) (meaning952 q) hs
  change valuationOf q 920 = false ∨ valuationOf q 943 = false ∨ valuationOf q 952 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause693 (q : Snake 81) (h : Conditions q) : valuation q 920 = false ∨ valuation q 943 = false ∨ valuation q 952 = true := counterClause693 (baseVal q)

theorem counterClause694 (q : Nat → Bool) : valuationOf q 921 = false ∨ valuationOf q 939 = false ∨ valuationOf q 949 = true := by
  have hs : count946 q = (countLit q [-57, -58, -59, -64, -65, -67, -70]) + (countLit q [-72, -73, -74, -76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -59, -64, -65, -67, -70]) (l₂ := [-72, -73, -74, -76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (921)) (literal (valuationOf q) (939)) (literal (valuationOf q) (949)) (countLit q [-57, -58, -59, -64, -65, -67, -70]) (countLit q [-72, -73, -74, -76, -78, -80, -81]) (count946 q) 3 1 (meaning921 q) (meaning939 q) (meaning949 q) hs
  change valuationOf q 921 = false ∨ valuationOf q 939 = false ∨ valuationOf q 949 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause694 (q : Snake 81) (h : Conditions q) : valuation q 921 = false ∨ valuation q 939 = false ∨ valuation q 949 = true := counterClause694 (baseVal q)

theorem counterClause695 (q : Nat → Bool) : valuationOf q 921 = false ∨ valuationOf q 940 = false ∨ valuationOf q 950 = true := by
  have hs : count946 q = (countLit q [-57, -58, -59, -64, -65, -67, -70]) + (countLit q [-72, -73, -74, -76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -59, -64, -65, -67, -70]) (l₂ := [-72, -73, -74, -76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (921)) (literal (valuationOf q) (940)) (literal (valuationOf q) (950)) (countLit q [-57, -58, -59, -64, -65, -67, -70]) (countLit q [-72, -73, -74, -76, -78, -80, -81]) (count946 q) 3 2 (meaning921 q) (meaning940 q) (meaning950 q) hs
  change valuationOf q 921 = false ∨ valuationOf q 940 = false ∨ valuationOf q 950 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause695 (q : Snake 81) (h : Conditions q) : valuation q 921 = false ∨ valuation q 940 = false ∨ valuation q 950 = true := counterClause695 (baseVal q)

theorem counterClause696 (q : Nat → Bool) : valuationOf q 921 = false ∨ valuationOf q 941 = false ∨ valuationOf q 951 = true := by
  have hs : count946 q = (countLit q [-57, -58, -59, -64, -65, -67, -70]) + (countLit q [-72, -73, -74, -76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -59, -64, -65, -67, -70]) (l₂ := [-72, -73, -74, -76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (921)) (literal (valuationOf q) (941)) (literal (valuationOf q) (951)) (countLit q [-57, -58, -59, -64, -65, -67, -70]) (countLit q [-72, -73, -74, -76, -78, -80, -81]) (count946 q) 3 3 (meaning921 q) (meaning941 q) (meaning951 q) hs
  change valuationOf q 921 = false ∨ valuationOf q 941 = false ∨ valuationOf q 951 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause696 (q : Snake 81) (h : Conditions q) : valuation q 921 = false ∨ valuation q 941 = false ∨ valuation q 951 = true := counterClause696 (baseVal q)

theorem counterClause697 (q : Nat → Bool) : valuationOf q 921 = false ∨ valuationOf q 942 = false ∨ valuationOf q 952 = true := by
  have hs : count946 q = (countLit q [-57, -58, -59, -64, -65, -67, -70]) + (countLit q [-72, -73, -74, -76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -59, -64, -65, -67, -70]) (l₂ := [-72, -73, -74, -76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (921)) (literal (valuationOf q) (942)) (literal (valuationOf q) (952)) (countLit q [-57, -58, -59, -64, -65, -67, -70]) (countLit q [-72, -73, -74, -76, -78, -80, -81]) (count946 q) 3 4 (meaning921 q) (meaning942 q) (meaning952 q) hs
  change valuationOf q 921 = false ∨ valuationOf q 942 = false ∨ valuationOf q 952 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause697 (q : Snake 81) (h : Conditions q) : valuation q 921 = false ∨ valuation q 942 = false ∨ valuation q 952 = true := counterClause697 (baseVal q)

theorem counterClause698 (q : Nat → Bool) : valuationOf q 922 = false ∨ valuationOf q 939 = false ∨ valuationOf q 950 = true := by
  have hs : count946 q = (countLit q [-57, -58, -59, -64, -65, -67, -70]) + (countLit q [-72, -73, -74, -76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -59, -64, -65, -67, -70]) (l₂ := [-72, -73, -74, -76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (922)) (literal (valuationOf q) (939)) (literal (valuationOf q) (950)) (countLit q [-57, -58, -59, -64, -65, -67, -70]) (countLit q [-72, -73, -74, -76, -78, -80, -81]) (count946 q) 4 1 (meaning922 q) (meaning939 q) (meaning950 q) hs
  change valuationOf q 922 = false ∨ valuationOf q 939 = false ∨ valuationOf q 950 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause698 (q : Snake 81) (h : Conditions q) : valuation q 922 = false ∨ valuation q 939 = false ∨ valuation q 950 = true := counterClause698 (baseVal q)

theorem counterClause699 (q : Nat → Bool) : valuationOf q 922 = false ∨ valuationOf q 940 = false ∨ valuationOf q 951 = true := by
  have hs : count946 q = (countLit q [-57, -58, -59, -64, -65, -67, -70]) + (countLit q [-72, -73, -74, -76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -59, -64, -65, -67, -70]) (l₂ := [-72, -73, -74, -76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (922)) (literal (valuationOf q) (940)) (literal (valuationOf q) (951)) (countLit q [-57, -58, -59, -64, -65, -67, -70]) (countLit q [-72, -73, -74, -76, -78, -80, -81]) (count946 q) 4 2 (meaning922 q) (meaning940 q) (meaning951 q) hs
  change valuationOf q 922 = false ∨ valuationOf q 940 = false ∨ valuationOf q 951 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause699 (q : Snake 81) (h : Conditions q) : valuation q 922 = false ∨ valuation q 940 = false ∨ valuation q 951 = true := counterClause699 (baseVal q)

theorem counterClause700 (q : Nat → Bool) : valuationOf q 922 = false ∨ valuationOf q 941 = false ∨ valuationOf q 952 = true := by
  have hs : count946 q = (countLit q [-57, -58, -59, -64, -65, -67, -70]) + (countLit q [-72, -73, -74, -76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -59, -64, -65, -67, -70]) (l₂ := [-72, -73, -74, -76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (922)) (literal (valuationOf q) (941)) (literal (valuationOf q) (952)) (countLit q [-57, -58, -59, -64, -65, -67, -70]) (countLit q [-72, -73, -74, -76, -78, -80, -81]) (count946 q) 4 3 (meaning922 q) (meaning941 q) (meaning952 q) hs
  change valuationOf q 922 = false ∨ valuationOf q 941 = false ∨ valuationOf q 952 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause700 (q : Snake 81) (h : Conditions q) : valuation q 922 = false ∨ valuation q 941 = false ∨ valuation q 952 = true := counterClause700 (baseVal q)

theorem counterClause701 (q : Nat → Bool) : valuationOf q 923 = false ∨ valuationOf q 940 = false ∨ valuationOf q 952 = true := by
  have hs : count946 q = (countLit q [-57, -58, -59, -64, -65, -67, -70]) + (countLit q [-72, -73, -74, -76, -78, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -59, -64, -65, -67, -70]) (l₂ := [-72, -73, -74, -76, -78, -80, -81])
  have hm := merge_two (literal (valuationOf q) (923)) (literal (valuationOf q) (940)) (literal (valuationOf q) (952)) (countLit q [-57, -58, -59, -64, -65, -67, -70]) (countLit q [-72, -73, -74, -76, -78, -80, -81]) (count946 q) 5 2 (meaning923 q) (meaning940 q) (meaning952 q) hs
  change valuationOf q 923 = false ∨ valuationOf q 940 = false ∨ valuationOf q 952 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause701 (q : Snake 81) (h : Conditions q) : valuation q 923 = false ∨ valuation q 940 = false ∨ valuation q 952 = true := counterClause701 (baseVal q)

theorem counterClause702 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 960 = true := by
  have hs : count960 q = (countLit q [-86]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-90])
  have hm := merge_right (literal (valuationOf q) (-90)) (literal (valuationOf q) (960)) (countLit q [-86]) (countLit q [-90]) (count960 q) 1 (meaningNeg90 q) (meaning960 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 960 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause702 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 960 = true := counterClause702 (baseVal q)

theorem counterClause703 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 960 = true := by
  have hs : count960 q = (countLit q [-86]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-90])
  have hm := merge_left (literal (valuationOf q) (-86)) (literal (valuationOf q) (960)) (countLit q [-86]) (countLit q [-90]) (count960 q) 1 (meaningNeg86 q) (meaning960 q) hs
  change (! (valuationOf q 86)) = false ∨ valuationOf q 960 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause703 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 960 = true := counterClause703 (baseVal q)

theorem counterClause704 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 90 = true ∨ valuationOf q 961 = true := by
  have hs : count960 q = (countLit q [-86]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-90])
  have hm := merge_two (literal (valuationOf q) (-86)) (literal (valuationOf q) (-90)) (literal (valuationOf q) (961)) (countLit q [-86]) (countLit q [-90]) (count960 q) 1 1 (meaningNeg86 q) (meaningNeg90 q) (meaning961 q) hs
  change (! (valuationOf q 86)) = false ∨ (! (valuationOf q 90)) = false ∨ valuationOf q 961 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause704 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 90 = true ∨ valuation q 961 = true := counterClause704 (baseVal q)

theorem block21 (q : Snake 81) (h : Conditions q) : B112E051.Block21 (valuation q) :=
  ⟨clause673 q h, clause674 q h, clause675 q h, clause676 q h, clause677 q h, clause678 q h, clause679 q h, clause680 q h, clause681 q h, clause682 q h, clause683 q h, clause684 q h, clause685 q h, clause686 q h, clause687 q h, clause688 q h, clause689 q h, clause690 q h, clause691 q h, clause692 q h, clause693 q h, clause694 q h, clause695 q h, clause696 q h, clause697 q h, clause698 q h, clause699 q h, clause700 q h, clause701 q h, clause702 q h, clause703 q h, clause704 q h⟩

end
end Snake9.Regrowth.E112051
