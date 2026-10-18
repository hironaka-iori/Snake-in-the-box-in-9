import E112185Semantics
import B112E185Inputs
namespace Snake9.Regrowth.E112185
noncomputable section
local instance blockDec21 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause673 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 921 = true := by
  have hs : count921 q = (countLit q [-85]) + (countLit q [-86]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-86])
  have hm := merge_right (literal (valuationOf q) (-86)) (literal (valuationOf q) (921)) (countLit q [-85]) (countLit q [-86]) (count921 q) 1 (meaningNeg86 q) (meaning921 q) hs
  change (! (valuationOf q 86)) = false ∨ valuationOf q 921 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause673 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 921 = true := counterClause673 (baseVal q)

theorem counterClause674 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 86 = true ∨ valuationOf q 922 = true := by
  have hs : count921 q = (countLit q [-85]) + (countLit q [-86]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-86])
  have hm := merge_two (literal (valuationOf q) (-85)) (literal (valuationOf q) (-86)) (literal (valuationOf q) (922)) (countLit q [-85]) (countLit q [-86]) (count921 q) 1 1 (meaningNeg85 q) (meaningNeg86 q) (meaning922 q) hs
  change (! (valuationOf q 85)) = false ∨ (! (valuationOf q 86)) = false ∨ valuationOf q 922 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause674 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 86 = true ∨ valuation q 922 = true := counterClause674 (baseVal q)

theorem counterClause675 (q : Nat → Bool) : valuationOf q 921 = false ∨ valuationOf q 923 = true := by
  have hs : count923 q = (countLit q [-81]) + (countLit q [-85, -86]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-85, -86])
  have hm := merge_right (literal (valuationOf q) (921)) (literal (valuationOf q) (923)) (countLit q [-81]) (countLit q [-85, -86]) (count923 q) 1 (meaning921 q) (meaning923 q) hs
  change valuationOf q 921 = false ∨ valuationOf q 923 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause675 (q : Snake 81) (h : Conditions q) : valuation q 921 = false ∨ valuation q 923 = true := counterClause675 (baseVal q)

theorem counterClause676 (q : Nat → Bool) : valuationOf q 922 = false ∨ valuationOf q 924 = true := by
  have hs : count923 q = (countLit q [-81]) + (countLit q [-85, -86]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-85, -86])
  have hm := merge_right (literal (valuationOf q) (922)) (literal (valuationOf q) (924)) (countLit q [-81]) (countLit q [-85, -86]) (count923 q) 2 (meaning922 q) (meaning924 q) hs
  change valuationOf q 922 = false ∨ valuationOf q 924 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause676 (q : Snake 81) (h : Conditions q) : valuation q 922 = false ∨ valuation q 924 = true := counterClause676 (baseVal q)

theorem counterClause677 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 923 = true := by
  have hs : count923 q = (countLit q [-81]) + (countLit q [-85, -86]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-85, -86])
  have hm := merge_left (literal (valuationOf q) (-81)) (literal (valuationOf q) (923)) (countLit q [-81]) (countLit q [-85, -86]) (count923 q) 1 (meaningNeg81 q) (meaning923 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 923 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause677 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 923 = true := counterClause677 (baseVal q)

theorem counterClause678 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 921 = false ∨ valuationOf q 924 = true := by
  have hs : count923 q = (countLit q [-81]) + (countLit q [-85, -86]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-85, -86])
  have hm := merge_two (literal (valuationOf q) (-81)) (literal (valuationOf q) (921)) (literal (valuationOf q) (924)) (countLit q [-81]) (countLit q [-85, -86]) (count923 q) 1 1 (meaningNeg81 q) (meaning921 q) (meaning924 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 921 = false ∨ valuationOf q 924 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause678 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 921 = false ∨ valuation q 924 = true := counterClause678 (baseVal q)

theorem counterClause679 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 926 = true := by
  have hs : count926 q = (countLit q [-88]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-90])
  have hm := merge_right (literal (valuationOf q) (-90)) (literal (valuationOf q) (926)) (countLit q [-88]) (countLit q [-90]) (count926 q) 1 (meaningNeg90 q) (meaning926 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 926 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause679 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 926 = true := counterClause679 (baseVal q)

theorem counterClause680 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 90 = true ∨ valuationOf q 927 = true := by
  have hs : count926 q = (countLit q [-88]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-90])
  have hm := merge_two (literal (valuationOf q) (-88)) (literal (valuationOf q) (-90)) (literal (valuationOf q) (927)) (countLit q [-88]) (countLit q [-90]) (count926 q) 1 1 (meaningNeg88 q) (meaningNeg90 q) (meaning927 q) hs
  change (! (valuationOf q 88)) = false ∨ (! (valuationOf q 90)) = false ∨ valuationOf q 927 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause680 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 90 = true ∨ valuation q 927 = true := counterClause680 (baseVal q)

theorem counterClause681 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 928 = true := by
  have hs : count928 q = (countLit q [-92]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-93])
  have hm := merge_right (literal (valuationOf q) (-93)) (literal (valuationOf q) (928)) (countLit q [-92]) (countLit q [-93]) (count928 q) 1 (meaningNeg93 q) (meaning928 q) hs
  change (! (valuationOf q 93)) = false ∨ valuationOf q 928 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause681 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 928 = true := counterClause681 (baseVal q)

theorem counterClause682 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 928 = true := by
  have hs : count928 q = (countLit q [-92]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-93])
  have hm := merge_left (literal (valuationOf q) (-92)) (literal (valuationOf q) (928)) (countLit q [-92]) (countLit q [-93]) (count928 q) 1 (meaningNeg92 q) (meaning928 q) hs
  change (! (valuationOf q 92)) = false ∨ valuationOf q 928 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause682 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 928 = true := counterClause682 (baseVal q)

theorem counterClause683 (q : Nat → Bool) : valuationOf q 926 = false ∨ valuationOf q 930 = true := by
  have hs : count930 q = (countLit q [-88, -90]) + (countLit q [-92, -93]) := List.countP_append (p := literal q) (l₁ := [-88, -90]) (l₂ := [-92, -93])
  have hm := merge_left (literal (valuationOf q) (926)) (literal (valuationOf q) (930)) (countLit q [-88, -90]) (countLit q [-92, -93]) (count930 q) 1 (meaning926 q) (meaning930 q) hs
  change valuationOf q 926 = false ∨ valuationOf q 930 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause683 (q : Snake 81) (h : Conditions q) : valuation q 926 = false ∨ valuation q 930 = true := counterClause683 (baseVal q)

theorem counterClause684 (q : Nat → Bool) : valuationOf q 926 = false ∨ valuationOf q 928 = false ∨ valuationOf q 931 = true := by
  have hs : count930 q = (countLit q [-88, -90]) + (countLit q [-92, -93]) := List.countP_append (p := literal q) (l₁ := [-88, -90]) (l₂ := [-92, -93])
  have hm := merge_two (literal (valuationOf q) (926)) (literal (valuationOf q) (928)) (literal (valuationOf q) (931)) (countLit q [-88, -90]) (countLit q [-92, -93]) (count930 q) 1 1 (meaning926 q) (meaning928 q) (meaning931 q) hs
  change valuationOf q 926 = false ∨ valuationOf q 928 = false ∨ valuationOf q 931 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause684 (q : Snake 81) (h : Conditions q) : valuation q 926 = false ∨ valuation q 928 = false ∨ valuation q 931 = true := counterClause684 (baseVal q)

theorem counterClause685 (q : Nat → Bool) : valuationOf q 927 = false ∨ valuationOf q 931 = true := by
  have hs : count930 q = (countLit q [-88, -90]) + (countLit q [-92, -93]) := List.countP_append (p := literal q) (l₁ := [-88, -90]) (l₂ := [-92, -93])
  have hm := merge_left (literal (valuationOf q) (927)) (literal (valuationOf q) (931)) (countLit q [-88, -90]) (countLit q [-92, -93]) (count930 q) 2 (meaning927 q) (meaning931 q) hs
  change valuationOf q 927 = false ∨ valuationOf q 931 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause685 (q : Snake 81) (h : Conditions q) : valuation q 927 = false ∨ valuation q 931 = true := counterClause685 (baseVal q)

theorem counterClause686 (q : Nat → Bool) : valuationOf q 927 = false ∨ valuationOf q 928 = false ∨ valuationOf q 932 = true := by
  have hs : count930 q = (countLit q [-88, -90]) + (countLit q [-92, -93]) := List.countP_append (p := literal q) (l₁ := [-88, -90]) (l₂ := [-92, -93])
  have hm := merge_two (literal (valuationOf q) (927)) (literal (valuationOf q) (928)) (literal (valuationOf q) (932)) (countLit q [-88, -90]) (countLit q [-92, -93]) (count930 q) 2 1 (meaning927 q) (meaning928 q) (meaning932 q) hs
  change valuationOf q 927 = false ∨ valuationOf q 928 = false ∨ valuationOf q 932 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause686 (q : Snake 81) (h : Conditions q) : valuation q 927 = false ∨ valuation q 928 = false ∨ valuation q 932 = true := counterClause686 (baseVal q)

theorem counterClause687 (q : Nat → Bool) : valuationOf q 930 = false ∨ valuationOf q 934 = true := by
  have hs : count934 q = (countLit q [-81, -85, -86]) + (countLit q [-88, -90, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-81, -85, -86]) (l₂ := [-88, -90, -92, -93])
  have hm := merge_right (literal (valuationOf q) (930)) (literal (valuationOf q) (934)) (countLit q [-81, -85, -86]) (countLit q [-88, -90, -92, -93]) (count934 q) 1 (meaning930 q) (meaning934 q) hs
  change valuationOf q 930 = false ∨ valuationOf q 934 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause687 (q : Snake 81) (h : Conditions q) : valuation q 930 = false ∨ valuation q 934 = true := counterClause687 (baseVal q)

theorem counterClause688 (q : Nat → Bool) : valuationOf q 931 = false ∨ valuationOf q 935 = true := by
  have hs : count934 q = (countLit q [-81, -85, -86]) + (countLit q [-88, -90, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-81, -85, -86]) (l₂ := [-88, -90, -92, -93])
  have hm := merge_right (literal (valuationOf q) (931)) (literal (valuationOf q) (935)) (countLit q [-81, -85, -86]) (countLit q [-88, -90, -92, -93]) (count934 q) 2 (meaning931 q) (meaning935 q) hs
  change valuationOf q 931 = false ∨ valuationOf q 935 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause688 (q : Snake 81) (h : Conditions q) : valuation q 931 = false ∨ valuation q 935 = true := counterClause688 (baseVal q)

theorem counterClause689 (q : Nat → Bool) : valuationOf q 923 = false ∨ valuationOf q 930 = false ∨ valuationOf q 935 = true := by
  have hs : count934 q = (countLit q [-81, -85, -86]) + (countLit q [-88, -90, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-81, -85, -86]) (l₂ := [-88, -90, -92, -93])
  have hm := merge_two (literal (valuationOf q) (923)) (literal (valuationOf q) (930)) (literal (valuationOf q) (935)) (countLit q [-81, -85, -86]) (countLit q [-88, -90, -92, -93]) (count934 q) 1 1 (meaning923 q) (meaning930 q) (meaning935 q) hs
  change valuationOf q 923 = false ∨ valuationOf q 930 = false ∨ valuationOf q 935 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause689 (q : Snake 81) (h : Conditions q) : valuation q 923 = false ∨ valuation q 930 = false ∨ valuation q 935 = true := counterClause689 (baseVal q)

theorem counterClause690 (q : Nat → Bool) : valuationOf q 923 = false ∨ valuationOf q 931 = false ∨ valuationOf q 936 = true := by
  have hs : count934 q = (countLit q [-81, -85, -86]) + (countLit q [-88, -90, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-81, -85, -86]) (l₂ := [-88, -90, -92, -93])
  have hm := merge_two (literal (valuationOf q) (923)) (literal (valuationOf q) (931)) (literal (valuationOf q) (936)) (countLit q [-81, -85, -86]) (countLit q [-88, -90, -92, -93]) (count934 q) 1 2 (meaning923 q) (meaning931 q) (meaning936 q) hs
  change valuationOf q 923 = false ∨ valuationOf q 931 = false ∨ valuationOf q 936 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause690 (q : Snake 81) (h : Conditions q) : valuation q 923 = false ∨ valuation q 931 = false ∨ valuation q 936 = true := counterClause690 (baseVal q)

theorem counterClause691 (q : Nat → Bool) : valuationOf q 923 = false ∨ valuationOf q 932 = false ∨ valuationOf q 937 = true := by
  have hs : count934 q = (countLit q [-81, -85, -86]) + (countLit q [-88, -90, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-81, -85, -86]) (l₂ := [-88, -90, -92, -93])
  have hm := merge_two (literal (valuationOf q) (923)) (literal (valuationOf q) (932)) (literal (valuationOf q) (937)) (countLit q [-81, -85, -86]) (countLit q [-88, -90, -92, -93]) (count934 q) 1 3 (meaning923 q) (meaning932 q) (meaning937 q) hs
  change valuationOf q 923 = false ∨ valuationOf q 932 = false ∨ valuationOf q 937 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause691 (q : Snake 81) (h : Conditions q) : valuation q 923 = false ∨ valuation q 932 = false ∨ valuation q 937 = true := counterClause691 (baseVal q)

theorem counterClause692 (q : Nat → Bool) : valuationOf q 924 = false ∨ valuationOf q 930 = false ∨ valuationOf q 936 = true := by
  have hs : count934 q = (countLit q [-81, -85, -86]) + (countLit q [-88, -90, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-81, -85, -86]) (l₂ := [-88, -90, -92, -93])
  have hm := merge_two (literal (valuationOf q) (924)) (literal (valuationOf q) (930)) (literal (valuationOf q) (936)) (countLit q [-81, -85, -86]) (countLit q [-88, -90, -92, -93]) (count934 q) 2 1 (meaning924 q) (meaning930 q) (meaning936 q) hs
  change valuationOf q 924 = false ∨ valuationOf q 930 = false ∨ valuationOf q 936 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause692 (q : Snake 81) (h : Conditions q) : valuation q 924 = false ∨ valuation q 930 = false ∨ valuation q 936 = true := counterClause692 (baseVal q)

theorem counterClause693 (q : Nat → Bool) : valuationOf q 924 = false ∨ valuationOf q 931 = false ∨ valuationOf q 937 = true := by
  have hs : count934 q = (countLit q [-81, -85, -86]) + (countLit q [-88, -90, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-81, -85, -86]) (l₂ := [-88, -90, -92, -93])
  have hm := merge_two (literal (valuationOf q) (924)) (literal (valuationOf q) (931)) (literal (valuationOf q) (937)) (countLit q [-81, -85, -86]) (countLit q [-88, -90, -92, -93]) (count934 q) 2 2 (meaning924 q) (meaning931 q) (meaning937 q) hs
  change valuationOf q 924 = false ∨ valuationOf q 931 = false ∨ valuationOf q 937 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause693 (q : Snake 81) (h : Conditions q) : valuation q 924 = false ∨ valuation q 931 = false ∨ valuation q 937 = true := counterClause693 (baseVal q)

theorem counterClause694 (q : Nat → Bool) : valuationOf q 100 = true ∨ valuationOf q 941 = true := by
  have hs : count941 q = (countLit q [-98]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-100])
  have hm := merge_right (literal (valuationOf q) (-100)) (literal (valuationOf q) (941)) (countLit q [-98]) (countLit q [-100]) (count941 q) 1 (meaningNeg100 q) (meaning941 q) hs
  change (! (valuationOf q 100)) = false ∨ valuationOf q 941 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause694 (q : Snake 81) (h : Conditions q) : valuation q 100 = true ∨ valuation q 941 = true := counterClause694 (baseVal q)

theorem counterClause695 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 941 = true := by
  have hs : count941 q = (countLit q [-98]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-100])
  have hm := merge_left (literal (valuationOf q) (-98)) (literal (valuationOf q) (941)) (countLit q [-98]) (countLit q [-100]) (count941 q) 1 (meaningNeg98 q) (meaning941 q) hs
  change (! (valuationOf q 98)) = false ∨ valuationOf q 941 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause695 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 941 = true := counterClause695 (baseVal q)

theorem counterClause696 (q : Nat → Bool) : valuationOf q 941 = false ∨ valuationOf q 943 = true := by
  have hs : count943 q = (countLit q [-95]) + (countLit q [-98, -100]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-98, -100])
  have hm := merge_right (literal (valuationOf q) (941)) (literal (valuationOf q) (943)) (countLit q [-95]) (countLit q [-98, -100]) (count943 q) 1 (meaning941 q) (meaning943 q) hs
  change valuationOf q 941 = false ∨ valuationOf q 943 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause696 (q : Snake 81) (h : Conditions q) : valuation q 941 = false ∨ valuation q 943 = true := counterClause696 (baseVal q)

theorem counterClause697 (q : Nat → Bool) : valuationOf q 95 = true ∨ valuationOf q 943 = true := by
  have hs : count943 q = (countLit q [-95]) + (countLit q [-98, -100]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-98, -100])
  have hm := merge_left (literal (valuationOf q) (-95)) (literal (valuationOf q) (943)) (countLit q [-95]) (countLit q [-98, -100]) (count943 q) 1 (meaningNeg95 q) (meaning943 q) hs
  change (! (valuationOf q 95)) = false ∨ valuationOf q 943 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause697 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 943 = true := counterClause697 (baseVal q)

theorem counterClause698 (q : Nat → Bool) : valuationOf q 95 = true ∨ valuationOf q 941 = false ∨ valuationOf q 944 = true := by
  have hs : count943 q = (countLit q [-95]) + (countLit q [-98, -100]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-98, -100])
  have hm := merge_two (literal (valuationOf q) (-95)) (literal (valuationOf q) (941)) (literal (valuationOf q) (944)) (countLit q [-95]) (countLit q [-98, -100]) (count943 q) 1 1 (meaningNeg95 q) (meaning941 q) (meaning944 q) hs
  change (! (valuationOf q 95)) = false ∨ valuationOf q 941 = false ∨ valuationOf q 944 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause698 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 941 = false ∨ valuation q 944 = true := counterClause698 (baseVal q)

theorem counterClause699 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 946 = true := by
  have hs : count946 q = (countLit q [-101]) + (countLit q [-103]) := List.countP_append (p := literal q) (l₁ := [-101]) (l₂ := [-103])
  have hm := merge_right (literal (valuationOf q) (-103)) (literal (valuationOf q) (946)) (countLit q [-101]) (countLit q [-103]) (count946 q) 1 (meaningNeg103 q) (meaning946 q) hs
  change (! (valuationOf q 103)) = false ∨ valuationOf q 946 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause699 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 946 = true := counterClause699 (baseVal q)

theorem counterClause700 (q : Nat → Bool) : valuationOf q 101 = true ∨ valuationOf q 946 = true := by
  have hs : count946 q = (countLit q [-101]) + (countLit q [-103]) := List.countP_append (p := literal q) (l₁ := [-101]) (l₂ := [-103])
  have hm := merge_left (literal (valuationOf q) (-101)) (literal (valuationOf q) (946)) (countLit q [-101]) (countLit q [-103]) (count946 q) 1 (meaningNeg101 q) (meaning946 q) hs
  change (! (valuationOf q 101)) = false ∨ valuationOf q 946 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause700 (q : Snake 81) (h : Conditions q) : valuation q 101 = true ∨ valuation q 946 = true := counterClause700 (baseVal q)

theorem counterClause701 (q : Nat → Bool) : valuationOf q 101 = true ∨ valuationOf q 103 = true ∨ valuationOf q 947 = true := by
  have hs : count946 q = (countLit q [-101]) + (countLit q [-103]) := List.countP_append (p := literal q) (l₁ := [-101]) (l₂ := [-103])
  have hm := merge_two (literal (valuationOf q) (-101)) (literal (valuationOf q) (-103)) (literal (valuationOf q) (947)) (countLit q [-101]) (countLit q [-103]) (count946 q) 1 1 (meaningNeg101 q) (meaningNeg103 q) (meaning947 q) hs
  change (! (valuationOf q 101)) = false ∨ (! (valuationOf q 103)) = false ∨ valuationOf q 947 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause701 (q : Snake 81) (h : Conditions q) : valuation q 101 = true ∨ valuation q 103 = true ∨ valuation q 947 = true := counterClause701 (baseVal q)

theorem counterClause702 (q : Nat → Bool) : valuationOf q 108 = true ∨ valuationOf q 948 = true := by
  have hs : count948 q = (countLit q [-106]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-106]) (l₂ := [-108])
  have hm := merge_right (literal (valuationOf q) (-108)) (literal (valuationOf q) (948)) (countLit q [-106]) (countLit q [-108]) (count948 q) 1 (meaningNeg108 q) (meaning948 q) hs
  change (! (valuationOf q 108)) = false ∨ valuationOf q 948 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause702 (q : Snake 81) (h : Conditions q) : valuation q 108 = true ∨ valuation q 948 = true := counterClause702 (baseVal q)

theorem counterClause703 (q : Nat → Bool) : valuationOf q 106 = true ∨ valuationOf q 948 = true := by
  have hs : count948 q = (countLit q [-106]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-106]) (l₂ := [-108])
  have hm := merge_left (literal (valuationOf q) (-106)) (literal (valuationOf q) (948)) (countLit q [-106]) (countLit q [-108]) (count948 q) 1 (meaningNeg106 q) (meaning948 q) hs
  change (! (valuationOf q 106)) = false ∨ valuationOf q 948 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause703 (q : Snake 81) (h : Conditions q) : valuation q 106 = true ∨ valuation q 948 = true := counterClause703 (baseVal q)

theorem counterClause704 (q : Nat → Bool) : valuationOf q 948 = false ∨ valuationOf q 950 = true := by
  have hs : count950 q = (countLit q [-101, -103]) + (countLit q [-106, -108]) := List.countP_append (p := literal q) (l₁ := [-101, -103]) (l₂ := [-106, -108])
  have hm := merge_right (literal (valuationOf q) (948)) (literal (valuationOf q) (950)) (countLit q [-101, -103]) (countLit q [-106, -108]) (count950 q) 1 (meaning948 q) (meaning950 q) hs
  change valuationOf q 948 = false ∨ valuationOf q 950 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause704 (q : Snake 81) (h : Conditions q) : valuation q 948 = false ∨ valuation q 950 = true := counterClause704 (baseVal q)

theorem block21 (q : Snake 81) (h : Conditions q) : B112E185.Block21 (valuation q) :=
  ⟨clause673 q h, clause674 q h, clause675 q h, clause676 q h, clause677 q h, clause678 q h, clause679 q h, clause680 q h, clause681 q h, clause682 q h, clause683 q h, clause684 q h, clause685 q h, clause686 q h, clause687 q h, clause688 q h, clause689 q h, clause690 q h, clause691 q h, clause692 q h, clause693 q h, clause694 q h, clause695 q h, clause696 q h, clause697 q h, clause698 q h, clause699 q h, clause700 q h, clause701 q h, clause702 q h, clause703 q h, clause704 q h⟩

end
end Snake9.Regrowth.E112185
