import E112185Semantics
import B112E185Inputs
namespace Snake9.Regrowth.E112185
noncomputable section
local instance blockDec20 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause641 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 892 = true := by
  have hs : count892 q = (countLit q [-75]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-77])
  have hm := merge_right (literal (valuationOf q) (-77)) (literal (valuationOf q) (892)) (countLit q [-75]) (countLit q [-77]) (count892 q) 1 (meaningNeg77 q) (meaning892 q) hs
  change (! (valuationOf q 77)) = false ∨ valuationOf q 892 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause641 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 892 = true := counterClause641 (baseVal q)

theorem counterClause642 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 892 = true := by
  have hs : count892 q = (countLit q [-75]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-77])
  have hm := merge_left (literal (valuationOf q) (-75)) (literal (valuationOf q) (892)) (countLit q [-75]) (countLit q [-77]) (count892 q) 1 (meaningNeg75 q) (meaning892 q) hs
  change (! (valuationOf q 75)) = false ∨ valuationOf q 892 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause642 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 892 = true := counterClause642 (baseVal q)

theorem counterClause643 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 77 = true ∨ valuationOf q 893 = true := by
  have hs : count892 q = (countLit q [-75]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-77])
  have hm := merge_two (literal (valuationOf q) (-75)) (literal (valuationOf q) (-77)) (literal (valuationOf q) (893)) (countLit q [-75]) (countLit q [-77]) (count892 q) 1 1 (meaningNeg75 q) (meaningNeg77 q) (meaning893 q) hs
  change (! (valuationOf q 75)) = false ∨ (! (valuationOf q 77)) = false ∨ valuationOf q 893 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause643 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 77 = true ∨ valuation q 893 = true := counterClause643 (baseVal q)

theorem counterClause644 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 894 = true := by
  have hs : count894 q = (countLit q [-78]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-79])
  have hm := merge_left (literal (valuationOf q) (-78)) (literal (valuationOf q) (894)) (countLit q [-78]) (countLit q [-79]) (count894 q) 1 (meaningNeg78 q) (meaning894 q) hs
  change (! (valuationOf q 78)) = false ∨ valuationOf q 894 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause644 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 894 = true := counterClause644 (baseVal q)

theorem counterClause645 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 79 = true ∨ valuationOf q 895 = true := by
  have hs : count894 q = (countLit q [-78]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-79])
  have hm := merge_two (literal (valuationOf q) (-78)) (literal (valuationOf q) (-79)) (literal (valuationOf q) (895)) (countLit q [-78]) (countLit q [-79]) (count894 q) 1 1 (meaningNeg78 q) (meaningNeg79 q) (meaning895 q) hs
  change (! (valuationOf q 78)) = false ∨ (! (valuationOf q 79)) = false ∨ valuationOf q 895 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause645 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 79 = true ∨ valuation q 895 = true := counterClause645 (baseVal q)

theorem counterClause646 (q : Nat → Bool) : valuationOf q 894 = false ∨ valuationOf q 896 = true := by
  have hs : count896 q = (countLit q [-75, -77]) + (countLit q [-78, -79]) := List.countP_append (p := literal q) (l₁ := [-75, -77]) (l₂ := [-78, -79])
  have hm := merge_right (literal (valuationOf q) (894)) (literal (valuationOf q) (896)) (countLit q [-75, -77]) (countLit q [-78, -79]) (count896 q) 1 (meaning894 q) (meaning896 q) hs
  change valuationOf q 894 = false ∨ valuationOf q 896 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause646 (q : Snake 81) (h : Conditions q) : valuation q 894 = false ∨ valuation q 896 = true := counterClause646 (baseVal q)

theorem counterClause647 (q : Nat → Bool) : valuationOf q 895 = false ∨ valuationOf q 897 = true := by
  have hs : count896 q = (countLit q [-75, -77]) + (countLit q [-78, -79]) := List.countP_append (p := literal q) (l₁ := [-75, -77]) (l₂ := [-78, -79])
  have hm := merge_right (literal (valuationOf q) (895)) (literal (valuationOf q) (897)) (countLit q [-75, -77]) (countLit q [-78, -79]) (count896 q) 2 (meaning895 q) (meaning897 q) hs
  change valuationOf q 895 = false ∨ valuationOf q 897 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause647 (q : Snake 81) (h : Conditions q) : valuation q 895 = false ∨ valuation q 897 = true := counterClause647 (baseVal q)

theorem counterClause648 (q : Nat → Bool) : valuationOf q 892 = false ∨ valuationOf q 894 = false ∨ valuationOf q 897 = true := by
  have hs : count896 q = (countLit q [-75, -77]) + (countLit q [-78, -79]) := List.countP_append (p := literal q) (l₁ := [-75, -77]) (l₂ := [-78, -79])
  have hm := merge_two (literal (valuationOf q) (892)) (literal (valuationOf q) (894)) (literal (valuationOf q) (897)) (countLit q [-75, -77]) (countLit q [-78, -79]) (count896 q) 1 1 (meaning892 q) (meaning894 q) (meaning897 q) hs
  change valuationOf q 892 = false ∨ valuationOf q 894 = false ∨ valuationOf q 897 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause648 (q : Snake 81) (h : Conditions q) : valuation q 892 = false ∨ valuation q 894 = false ∨ valuation q 897 = true := counterClause648 (baseVal q)

theorem counterClause649 (q : Nat → Bool) : valuationOf q 892 = false ∨ valuationOf q 895 = false ∨ valuationOf q 898 = true := by
  have hs : count896 q = (countLit q [-75, -77]) + (countLit q [-78, -79]) := List.countP_append (p := literal q) (l₁ := [-75, -77]) (l₂ := [-78, -79])
  have hm := merge_two (literal (valuationOf q) (892)) (literal (valuationOf q) (895)) (literal (valuationOf q) (898)) (countLit q [-75, -77]) (countLit q [-78, -79]) (count896 q) 1 2 (meaning892 q) (meaning895 q) (meaning898 q) hs
  change valuationOf q 892 = false ∨ valuationOf q 895 = false ∨ valuationOf q 898 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause649 (q : Snake 81) (h : Conditions q) : valuation q 892 = false ∨ valuation q 895 = false ∨ valuation q 898 = true := counterClause649 (baseVal q)

theorem counterClause650 (q : Nat → Bool) : valuationOf q 893 = false ∨ valuationOf q 894 = false ∨ valuationOf q 898 = true := by
  have hs : count896 q = (countLit q [-75, -77]) + (countLit q [-78, -79]) := List.countP_append (p := literal q) (l₁ := [-75, -77]) (l₂ := [-78, -79])
  have hm := merge_two (literal (valuationOf q) (893)) (literal (valuationOf q) (894)) (literal (valuationOf q) (898)) (countLit q [-75, -77]) (countLit q [-78, -79]) (count896 q) 2 1 (meaning893 q) (meaning894 q) (meaning898 q) hs
  change valuationOf q 893 = false ∨ valuationOf q 894 = false ∨ valuationOf q 898 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause650 (q : Snake 81) (h : Conditions q) : valuation q 893 = false ∨ valuation q 894 = false ∨ valuation q 898 = true := counterClause650 (baseVal q)

theorem counterClause651 (q : Nat → Bool) : valuationOf q 896 = false ∨ valuationOf q 900 = true := by
  have hs : count900 q = (countLit q [-69, -70, -74]) + (countLit q [-75, -77, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-69, -70, -74]) (l₂ := [-75, -77, -78, -79])
  have hm := merge_right (literal (valuationOf q) (896)) (literal (valuationOf q) (900)) (countLit q [-69, -70, -74]) (countLit q [-75, -77, -78, -79]) (count900 q) 1 (meaning896 q) (meaning900 q) hs
  change valuationOf q 896 = false ∨ valuationOf q 900 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause651 (q : Snake 81) (h : Conditions q) : valuation q 896 = false ∨ valuation q 900 = true := counterClause651 (baseVal q)

theorem counterClause652 (q : Nat → Bool) : valuationOf q 897 = false ∨ valuationOf q 901 = true := by
  have hs : count900 q = (countLit q [-69, -70, -74]) + (countLit q [-75, -77, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-69, -70, -74]) (l₂ := [-75, -77, -78, -79])
  have hm := merge_right (literal (valuationOf q) (897)) (literal (valuationOf q) (901)) (countLit q [-69, -70, -74]) (countLit q [-75, -77, -78, -79]) (count900 q) 2 (meaning897 q) (meaning901 q) hs
  change valuationOf q 897 = false ∨ valuationOf q 901 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause652 (q : Snake 81) (h : Conditions q) : valuation q 897 = false ∨ valuation q 901 = true := counterClause652 (baseVal q)

theorem counterClause653 (q : Nat → Bool) : valuationOf q 898 = false ∨ valuationOf q 902 = true := by
  have hs : count900 q = (countLit q [-69, -70, -74]) + (countLit q [-75, -77, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-69, -70, -74]) (l₂ := [-75, -77, -78, -79])
  have hm := merge_right (literal (valuationOf q) (898)) (literal (valuationOf q) (902)) (countLit q [-69, -70, -74]) (countLit q [-75, -77, -78, -79]) (count900 q) 3 (meaning898 q) (meaning902 q) hs
  change valuationOf q 898 = false ∨ valuationOf q 902 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause653 (q : Snake 81) (h : Conditions q) : valuation q 898 = false ∨ valuation q 902 = true := counterClause653 (baseVal q)

theorem counterClause654 (q : Nat → Bool) : valuationOf q 889 = false ∨ valuationOf q 896 = false ∨ valuationOf q 901 = true := by
  have hs : count900 q = (countLit q [-69, -70, -74]) + (countLit q [-75, -77, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-69, -70, -74]) (l₂ := [-75, -77, -78, -79])
  have hm := merge_two (literal (valuationOf q) (889)) (literal (valuationOf q) (896)) (literal (valuationOf q) (901)) (countLit q [-69, -70, -74]) (countLit q [-75, -77, -78, -79]) (count900 q) 1 1 (meaning889 q) (meaning896 q) (meaning901 q) hs
  change valuationOf q 889 = false ∨ valuationOf q 896 = false ∨ valuationOf q 901 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause654 (q : Snake 81) (h : Conditions q) : valuation q 889 = false ∨ valuation q 896 = false ∨ valuation q 901 = true := counterClause654 (baseVal q)

theorem counterClause655 (q : Nat → Bool) : valuationOf q 889 = false ∨ valuationOf q 897 = false ∨ valuationOf q 902 = true := by
  have hs : count900 q = (countLit q [-69, -70, -74]) + (countLit q [-75, -77, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-69, -70, -74]) (l₂ := [-75, -77, -78, -79])
  have hm := merge_two (literal (valuationOf q) (889)) (literal (valuationOf q) (897)) (literal (valuationOf q) (902)) (countLit q [-69, -70, -74]) (countLit q [-75, -77, -78, -79]) (count900 q) 1 2 (meaning889 q) (meaning897 q) (meaning902 q) hs
  change valuationOf q 889 = false ∨ valuationOf q 897 = false ∨ valuationOf q 902 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause655 (q : Snake 81) (h : Conditions q) : valuation q 889 = false ∨ valuation q 897 = false ∨ valuation q 902 = true := counterClause655 (baseVal q)

theorem counterClause656 (q : Nat → Bool) : valuationOf q 889 = false ∨ valuationOf q 898 = false ∨ valuationOf q 903 = true := by
  have hs : count900 q = (countLit q [-69, -70, -74]) + (countLit q [-75, -77, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-69, -70, -74]) (l₂ := [-75, -77, -78, -79])
  have hm := merge_two (literal (valuationOf q) (889)) (literal (valuationOf q) (898)) (literal (valuationOf q) (903)) (countLit q [-69, -70, -74]) (countLit q [-75, -77, -78, -79]) (count900 q) 1 3 (meaning889 q) (meaning898 q) (meaning903 q) hs
  change valuationOf q 889 = false ∨ valuationOf q 898 = false ∨ valuationOf q 903 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause656 (q : Snake 81) (h : Conditions q) : valuation q 889 = false ∨ valuation q 898 = false ∨ valuation q 903 = true := counterClause656 (baseVal q)

theorem counterClause657 (q : Nat → Bool) : valuationOf q 890 = false ∨ valuationOf q 896 = false ∨ valuationOf q 902 = true := by
  have hs : count900 q = (countLit q [-69, -70, -74]) + (countLit q [-75, -77, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-69, -70, -74]) (l₂ := [-75, -77, -78, -79])
  have hm := merge_two (literal (valuationOf q) (890)) (literal (valuationOf q) (896)) (literal (valuationOf q) (902)) (countLit q [-69, -70, -74]) (countLit q [-75, -77, -78, -79]) (count900 q) 2 1 (meaning890 q) (meaning896 q) (meaning902 q) hs
  change valuationOf q 890 = false ∨ valuationOf q 896 = false ∨ valuationOf q 902 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause657 (q : Snake 81) (h : Conditions q) : valuation q 890 = false ∨ valuation q 896 = false ∨ valuation q 902 = true := counterClause657 (baseVal q)

theorem counterClause658 (q : Nat → Bool) : valuationOf q 890 = false ∨ valuationOf q 897 = false ∨ valuationOf q 903 = true := by
  have hs : count900 q = (countLit q [-69, -70, -74]) + (countLit q [-75, -77, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-69, -70, -74]) (l₂ := [-75, -77, -78, -79])
  have hm := merge_two (literal (valuationOf q) (890)) (literal (valuationOf q) (897)) (literal (valuationOf q) (903)) (countLit q [-69, -70, -74]) (countLit q [-75, -77, -78, -79]) (count900 q) 2 2 (meaning890 q) (meaning897 q) (meaning903 q) hs
  change valuationOf q 890 = false ∨ valuationOf q 897 = false ∨ valuationOf q 903 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause658 (q : Snake 81) (h : Conditions q) : valuation q 890 = false ∨ valuation q 897 = false ∨ valuation q 903 = true := counterClause658 (baseVal q)

theorem counterClause659 (q : Nat → Bool) : valuationOf q 891 = false ∨ valuationOf q 896 = false ∨ valuationOf q 903 = true := by
  have hs : count900 q = (countLit q [-69, -70, -74]) + (countLit q [-75, -77, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-69, -70, -74]) (l₂ := [-75, -77, -78, -79])
  have hm := merge_two (literal (valuationOf q) (891)) (literal (valuationOf q) (896)) (literal (valuationOf q) (903)) (countLit q [-69, -70, -74]) (countLit q [-75, -77, -78, -79]) (count900 q) 3 1 (meaning891 q) (meaning896 q) (meaning903 q) hs
  change valuationOf q 891 = false ∨ valuationOf q 896 = false ∨ valuationOf q 903 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause659 (q : Snake 81) (h : Conditions q) : valuation q 891 = false ∨ valuation q 896 = false ∨ valuation q 903 = true := counterClause659 (baseVal q)

theorem counterClause660 (q : Nat → Bool) : valuationOf q 900 = false ∨ valuationOf q 907 = true := by
  have hs : count907 q = (countLit q [-54, -56, -59, -61, -62, -64, -67]) + (countLit q [-69, -70, -74, -75, -77, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59, -61, -62, -64, -67]) (l₂ := [-69, -70, -74, -75, -77, -78, -79])
  have hm := merge_right (literal (valuationOf q) (900)) (literal (valuationOf q) (907)) (countLit q [-54, -56, -59, -61, -62, -64, -67]) (countLit q [-69, -70, -74, -75, -77, -78, -79]) (count907 q) 1 (meaning900 q) (meaning907 q) hs
  change valuationOf q 900 = false ∨ valuationOf q 907 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause660 (q : Snake 81) (h : Conditions q) : valuation q 900 = false ∨ valuation q 907 = true := counterClause660 (baseVal q)

theorem counterClause661 (q : Nat → Bool) : valuationOf q 880 = false ∨ valuationOf q 900 = false ∨ valuationOf q 908 = true := by
  have hs : count907 q = (countLit q [-54, -56, -59, -61, -62, -64, -67]) + (countLit q [-69, -70, -74, -75, -77, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59, -61, -62, -64, -67]) (l₂ := [-69, -70, -74, -75, -77, -78, -79])
  have hm := merge_two (literal (valuationOf q) (880)) (literal (valuationOf q) (900)) (literal (valuationOf q) (908)) (countLit q [-54, -56, -59, -61, -62, -64, -67]) (countLit q [-69, -70, -74, -75, -77, -78, -79]) (count907 q) 1 1 (meaning880 q) (meaning900 q) (meaning908 q) hs
  change valuationOf q 880 = false ∨ valuationOf q 900 = false ∨ valuationOf q 908 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause661 (q : Snake 81) (h : Conditions q) : valuation q 880 = false ∨ valuation q 900 = false ∨ valuation q 908 = true := counterClause661 (baseVal q)

theorem counterClause662 (q : Nat → Bool) : valuationOf q 880 = false ∨ valuationOf q 901 = false ∨ valuationOf q 909 = true := by
  have hs : count907 q = (countLit q [-54, -56, -59, -61, -62, -64, -67]) + (countLit q [-69, -70, -74, -75, -77, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59, -61, -62, -64, -67]) (l₂ := [-69, -70, -74, -75, -77, -78, -79])
  have hm := merge_two (literal (valuationOf q) (880)) (literal (valuationOf q) (901)) (literal (valuationOf q) (909)) (countLit q [-54, -56, -59, -61, -62, -64, -67]) (countLit q [-69, -70, -74, -75, -77, -78, -79]) (count907 q) 1 2 (meaning880 q) (meaning901 q) (meaning909 q) hs
  change valuationOf q 880 = false ∨ valuationOf q 901 = false ∨ valuationOf q 909 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause662 (q : Snake 81) (h : Conditions q) : valuation q 880 = false ∨ valuation q 901 = false ∨ valuation q 909 = true := counterClause662 (baseVal q)

theorem counterClause663 (q : Nat → Bool) : valuationOf q 880 = false ∨ valuationOf q 902 = false ∨ valuationOf q 910 = true := by
  have hs : count907 q = (countLit q [-54, -56, -59, -61, -62, -64, -67]) + (countLit q [-69, -70, -74, -75, -77, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59, -61, -62, -64, -67]) (l₂ := [-69, -70, -74, -75, -77, -78, -79])
  have hm := merge_two (literal (valuationOf q) (880)) (literal (valuationOf q) (902)) (literal (valuationOf q) (910)) (countLit q [-54, -56, -59, -61, -62, -64, -67]) (countLit q [-69, -70, -74, -75, -77, -78, -79]) (count907 q) 1 3 (meaning880 q) (meaning902 q) (meaning910 q) hs
  change valuationOf q 880 = false ∨ valuationOf q 902 = false ∨ valuationOf q 910 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause663 (q : Snake 81) (h : Conditions q) : valuation q 880 = false ∨ valuation q 902 = false ∨ valuation q 910 = true := counterClause663 (baseVal q)

theorem counterClause664 (q : Nat → Bool) : valuationOf q 881 = false ∨ valuationOf q 900 = false ∨ valuationOf q 909 = true := by
  have hs : count907 q = (countLit q [-54, -56, -59, -61, -62, -64, -67]) + (countLit q [-69, -70, -74, -75, -77, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59, -61, -62, -64, -67]) (l₂ := [-69, -70, -74, -75, -77, -78, -79])
  have hm := merge_two (literal (valuationOf q) (881)) (literal (valuationOf q) (900)) (literal (valuationOf q) (909)) (countLit q [-54, -56, -59, -61, -62, -64, -67]) (countLit q [-69, -70, -74, -75, -77, -78, -79]) (count907 q) 2 1 (meaning881 q) (meaning900 q) (meaning909 q) hs
  change valuationOf q 881 = false ∨ valuationOf q 900 = false ∨ valuationOf q 909 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause664 (q : Snake 81) (h : Conditions q) : valuation q 881 = false ∨ valuation q 900 = false ∨ valuation q 909 = true := counterClause664 (baseVal q)

theorem counterClause665 (q : Nat → Bool) : valuationOf q 881 = false ∨ valuationOf q 901 = false ∨ valuationOf q 910 = true := by
  have hs : count907 q = (countLit q [-54, -56, -59, -61, -62, -64, -67]) + (countLit q [-69, -70, -74, -75, -77, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59, -61, -62, -64, -67]) (l₂ := [-69, -70, -74, -75, -77, -78, -79])
  have hm := merge_two (literal (valuationOf q) (881)) (literal (valuationOf q) (901)) (literal (valuationOf q) (910)) (countLit q [-54, -56, -59, -61, -62, -64, -67]) (countLit q [-69, -70, -74, -75, -77, -78, -79]) (count907 q) 2 2 (meaning881 q) (meaning901 q) (meaning910 q) hs
  change valuationOf q 881 = false ∨ valuationOf q 901 = false ∨ valuationOf q 910 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause665 (q : Snake 81) (h : Conditions q) : valuation q 881 = false ∨ valuation q 901 = false ∨ valuation q 910 = true := counterClause665 (baseVal q)

theorem counterClause666 (q : Nat → Bool) : valuationOf q 881 = false ∨ valuationOf q 902 = false ∨ valuationOf q 911 = true := by
  have hs : count907 q = (countLit q [-54, -56, -59, -61, -62, -64, -67]) + (countLit q [-69, -70, -74, -75, -77, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59, -61, -62, -64, -67]) (l₂ := [-69, -70, -74, -75, -77, -78, -79])
  have hm := merge_two (literal (valuationOf q) (881)) (literal (valuationOf q) (902)) (literal (valuationOf q) (911)) (countLit q [-54, -56, -59, -61, -62, -64, -67]) (countLit q [-69, -70, -74, -75, -77, -78, -79]) (count907 q) 2 3 (meaning881 q) (meaning902 q) (meaning911 q) hs
  change valuationOf q 881 = false ∨ valuationOf q 902 = false ∨ valuationOf q 911 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause666 (q : Snake 81) (h : Conditions q) : valuation q 881 = false ∨ valuation q 902 = false ∨ valuation q 911 = true := counterClause666 (baseVal q)

theorem counterClause667 (q : Nat → Bool) : valuationOf q 881 = false ∨ valuationOf q 903 = false ∨ valuationOf q 912 = true := by
  have hs : count907 q = (countLit q [-54, -56, -59, -61, -62, -64, -67]) + (countLit q [-69, -70, -74, -75, -77, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59, -61, -62, -64, -67]) (l₂ := [-69, -70, -74, -75, -77, -78, -79])
  have hm := merge_two (literal (valuationOf q) (881)) (literal (valuationOf q) (903)) (literal (valuationOf q) (912)) (countLit q [-54, -56, -59, -61, -62, -64, -67]) (countLit q [-69, -70, -74, -75, -77, -78, -79]) (count907 q) 2 4 (meaning881 q) (meaning903 q) (meaning912 q) hs
  change valuationOf q 881 = false ∨ valuationOf q 903 = false ∨ valuationOf q 912 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause667 (q : Snake 81) (h : Conditions q) : valuation q 881 = false ∨ valuation q 903 = false ∨ valuation q 912 = true := counterClause667 (baseVal q)

theorem counterClause668 (q : Nat → Bool) : valuationOf q 882 = false ∨ valuationOf q 900 = false ∨ valuationOf q 910 = true := by
  have hs : count907 q = (countLit q [-54, -56, -59, -61, -62, -64, -67]) + (countLit q [-69, -70, -74, -75, -77, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59, -61, -62, -64, -67]) (l₂ := [-69, -70, -74, -75, -77, -78, -79])
  have hm := merge_two (literal (valuationOf q) (882)) (literal (valuationOf q) (900)) (literal (valuationOf q) (910)) (countLit q [-54, -56, -59, -61, -62, -64, -67]) (countLit q [-69, -70, -74, -75, -77, -78, -79]) (count907 q) 3 1 (meaning882 q) (meaning900 q) (meaning910 q) hs
  change valuationOf q 882 = false ∨ valuationOf q 900 = false ∨ valuationOf q 910 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause668 (q : Snake 81) (h : Conditions q) : valuation q 882 = false ∨ valuation q 900 = false ∨ valuation q 910 = true := counterClause668 (baseVal q)

theorem counterClause669 (q : Nat → Bool) : valuationOf q 882 = false ∨ valuationOf q 901 = false ∨ valuationOf q 911 = true := by
  have hs : count907 q = (countLit q [-54, -56, -59, -61, -62, -64, -67]) + (countLit q [-69, -70, -74, -75, -77, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59, -61, -62, -64, -67]) (l₂ := [-69, -70, -74, -75, -77, -78, -79])
  have hm := merge_two (literal (valuationOf q) (882)) (literal (valuationOf q) (901)) (literal (valuationOf q) (911)) (countLit q [-54, -56, -59, -61, -62, -64, -67]) (countLit q [-69, -70, -74, -75, -77, -78, -79]) (count907 q) 3 2 (meaning882 q) (meaning901 q) (meaning911 q) hs
  change valuationOf q 882 = false ∨ valuationOf q 901 = false ∨ valuationOf q 911 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause669 (q : Snake 81) (h : Conditions q) : valuation q 882 = false ∨ valuation q 901 = false ∨ valuation q 911 = true := counterClause669 (baseVal q)

theorem counterClause670 (q : Nat → Bool) : valuationOf q 882 = false ∨ valuationOf q 902 = false ∨ valuationOf q 912 = true := by
  have hs : count907 q = (countLit q [-54, -56, -59, -61, -62, -64, -67]) + (countLit q [-69, -70, -74, -75, -77, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59, -61, -62, -64, -67]) (l₂ := [-69, -70, -74, -75, -77, -78, -79])
  have hm := merge_two (literal (valuationOf q) (882)) (literal (valuationOf q) (902)) (literal (valuationOf q) (912)) (countLit q [-54, -56, -59, -61, -62, -64, -67]) (countLit q [-69, -70, -74, -75, -77, -78, -79]) (count907 q) 3 3 (meaning882 q) (meaning902 q) (meaning912 q) hs
  change valuationOf q 882 = false ∨ valuationOf q 902 = false ∨ valuationOf q 912 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause670 (q : Snake 81) (h : Conditions q) : valuation q 882 = false ∨ valuation q 902 = false ∨ valuation q 912 = true := counterClause670 (baseVal q)

theorem counterClause671 (q : Nat → Bool) : valuationOf q 883 = false ∨ valuationOf q 900 = false ∨ valuationOf q 911 = true := by
  have hs : count907 q = (countLit q [-54, -56, -59, -61, -62, -64, -67]) + (countLit q [-69, -70, -74, -75, -77, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59, -61, -62, -64, -67]) (l₂ := [-69, -70, -74, -75, -77, -78, -79])
  have hm := merge_two (literal (valuationOf q) (883)) (literal (valuationOf q) (900)) (literal (valuationOf q) (911)) (countLit q [-54, -56, -59, -61, -62, -64, -67]) (countLit q [-69, -70, -74, -75, -77, -78, -79]) (count907 q) 4 1 (meaning883 q) (meaning900 q) (meaning911 q) hs
  change valuationOf q 883 = false ∨ valuationOf q 900 = false ∨ valuationOf q 911 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause671 (q : Snake 81) (h : Conditions q) : valuation q 883 = false ∨ valuation q 900 = false ∨ valuation q 911 = true := counterClause671 (baseVal q)

theorem counterClause672 (q : Nat → Bool) : valuationOf q 883 = false ∨ valuationOf q 901 = false ∨ valuationOf q 912 = true := by
  have hs : count907 q = (countLit q [-54, -56, -59, -61, -62, -64, -67]) + (countLit q [-69, -70, -74, -75, -77, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59, -61, -62, -64, -67]) (l₂ := [-69, -70, -74, -75, -77, -78, -79])
  have hm := merge_two (literal (valuationOf q) (883)) (literal (valuationOf q) (901)) (literal (valuationOf q) (912)) (countLit q [-54, -56, -59, -61, -62, -64, -67]) (countLit q [-69, -70, -74, -75, -77, -78, -79]) (count907 q) 4 2 (meaning883 q) (meaning901 q) (meaning912 q) hs
  change valuationOf q 883 = false ∨ valuationOf q 901 = false ∨ valuationOf q 912 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause672 (q : Snake 81) (h : Conditions q) : valuation q 883 = false ∨ valuation q 901 = false ∨ valuation q 912 = true := counterClause672 (baseVal q)

theorem block20 (q : Snake 81) (h : Conditions q) : B112E185.Block20 (valuation q) :=
  ⟨clause641 q h, clause642 q h, clause643 q h, clause644 q h, clause645 q h, clause646 q h, clause647 q h, clause648 q h, clause649 q h, clause650 q h, clause651 q h, clause652 q h, clause653 q h, clause654 q h, clause655 q h, clause656 q h, clause657 q h, clause658 q h, clause659 q h, clause660 q h, clause661 q h, clause662 q h, clause663 q h, clause664 q h, clause665 q h, clause666 q h, clause667 q h, clause668 q h, clause669 q h, clause670 q h, clause671 q h, clause672 q h⟩

end
end Snake9.Regrowth.E112185
