import E112174Semantics
import B112E174Inputs
namespace Snake9.Regrowth.E112174
noncomputable section
local instance blockDec23 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause737 (q : Nat → Bool) : valuationOf q 857 = false ∨ valuationOf q 875 = false ∨ valuationOf q 885 = true := by
  have hs : count881 q = (countLit q [-81, -82, -84, -86, -88, -89]) + (countLit q [-91, -94, -96, -97, -99, -102, -104]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -84, -86, -88, -89]) (l₂ := [-91, -94, -96, -97, -99, -102, -104])
  have hm := merge_two (literal (valuationOf q) (857)) (literal (valuationOf q) (875)) (literal (valuationOf q) (885)) (countLit q [-81, -82, -84, -86, -88, -89]) (countLit q [-91, -94, -96, -97, -99, -102, -104]) (count881 q) 3 2 (meaning857 q) (meaning875 q) (meaning885 q) hs
  change valuationOf q 857 = false ∨ valuationOf q 875 = false ∨ valuationOf q 885 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause737 (q : Snake 81) (h : Conditions q) : valuation q 857 = false ∨ valuation q 875 = false ∨ valuation q 885 = true := counterClause737 (baseVal q)

theorem counterClause738 (q : Nat → Bool) : valuationOf q 882 = false ∨ valuationOf q 893 = true := by
  have hs : count892 q = (countLit q [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77]) + (countLit q [-81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77]) (l₂ := [-81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104])
  have hm := merge_right (literal (valuationOf q) (882)) (literal (valuationOf q) (893)) (countLit q [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77]) (countLit q [-81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104]) (count892 q) 2 (meaning882 q) (meaning893 q) hs
  change valuationOf q 882 = false ∨ valuationOf q 893 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause738 (q : Snake 81) (h : Conditions q) : valuation q 882 = false ∨ valuation q 893 = true := counterClause738 (baseVal q)

theorem counterClause739 (q : Nat → Bool) : valuationOf q 834 = false ∨ valuationOf q 882 = false ∨ valuationOf q 894 = true := by
  have hs : count892 q = (countLit q [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77]) + (countLit q [-81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77]) (l₂ := [-81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104])
  have hm := merge_two (literal (valuationOf q) (834)) (literal (valuationOf q) (882)) (literal (valuationOf q) (894)) (countLit q [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77]) (countLit q [-81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104]) (count892 q) 1 2 (meaning834 q) (meaning882 q) (meaning894 q) hs
  change valuationOf q 834 = false ∨ valuationOf q 882 = false ∨ valuationOf q 894 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause739 (q : Snake 81) (h : Conditions q) : valuation q 834 = false ∨ valuation q 882 = false ∨ valuation q 894 = true := counterClause739 (baseVal q)

theorem counterClause740 (q : Nat → Bool) : valuationOf q 835 = false ∨ valuationOf q 893 = true := by
  have hs : count892 q = (countLit q [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77]) + (countLit q [-81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77]) (l₂ := [-81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104])
  have hm := merge_left (literal (valuationOf q) (835)) (literal (valuationOf q) (893)) (countLit q [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77]) (countLit q [-81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104]) (count892 q) 2 (meaning835 q) (meaning893 q) hs
  change valuationOf q 835 = false ∨ valuationOf q 893 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause740 (q : Snake 81) (h : Conditions q) : valuation q 835 = false ∨ valuation q 893 = true := counterClause740 (baseVal q)

theorem counterClause741 (q : Nat → Bool) : valuationOf q 835 = false ∨ valuationOf q 881 = false ∨ valuationOf q 894 = true := by
  have hs : count892 q = (countLit q [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77]) + (countLit q [-81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77]) (l₂ := [-81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104])
  have hm := merge_two (literal (valuationOf q) (835)) (literal (valuationOf q) (881)) (literal (valuationOf q) (894)) (countLit q [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77]) (countLit q [-81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104]) (count892 q) 2 1 (meaning835 q) (meaning881 q) (meaning894 q) hs
  change valuationOf q 835 = false ∨ valuationOf q 881 = false ∨ valuationOf q 894 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause741 (q : Snake 81) (h : Conditions q) : valuation q 835 = false ∨ valuation q 881 = false ∨ valuation q 894 = true := counterClause741 (baseVal q)

theorem counterClause742 (q : Nat → Bool) : valuationOf q 835 = false ∨ valuationOf q 882 = false ∨ valuationOf q 895 = true := by
  have hs : count892 q = (countLit q [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77]) + (countLit q [-81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77]) (l₂ := [-81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104])
  have hm := merge_two (literal (valuationOf q) (835)) (literal (valuationOf q) (882)) (literal (valuationOf q) (895)) (countLit q [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77]) (countLit q [-81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104]) (count892 q) 2 2 (meaning835 q) (meaning882 q) (meaning895 q) hs
  change valuationOf q 835 = false ∨ valuationOf q 882 = false ∨ valuationOf q 895 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause742 (q : Snake 81) (h : Conditions q) : valuation q 835 = false ∨ valuation q 882 = false ∨ valuation q 895 = true := counterClause742 (baseVal q)

theorem counterClause743 (q : Nat → Bool) : valuationOf q 835 = false ∨ valuationOf q 884 = false ∨ valuationOf q 897 = true := by
  have hs : count892 q = (countLit q [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77]) + (countLit q [-81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77]) (l₂ := [-81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104])
  have hm := merge_two (literal (valuationOf q) (835)) (literal (valuationOf q) (884)) (literal (valuationOf q) (897)) (countLit q [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77]) (countLit q [-81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104]) (count892 q) 2 4 (meaning835 q) (meaning884 q) (meaning897 q) hs
  change valuationOf q 835 = false ∨ valuationOf q 884 = false ∨ valuationOf q 897 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause743 (q : Snake 81) (h : Conditions q) : valuation q 835 = false ∨ valuation q 884 = false ∨ valuation q 897 = true := counterClause743 (baseVal q)

theorem counterClause744 (q : Nat → Bool) : valuationOf q 835 = false ∨ valuationOf q 885 = false ∨ valuationOf q 898 = true := by
  have hs : count892 q = (countLit q [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77]) + (countLit q [-81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77]) (l₂ := [-81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104])
  have hm := merge_two (literal (valuationOf q) (835)) (literal (valuationOf q) (885)) (literal (valuationOf q) (898)) (countLit q [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77]) (countLit q [-81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104]) (count892 q) 2 5 (meaning835 q) (meaning885 q) (meaning898 q) hs
  change valuationOf q 835 = false ∨ valuationOf q 885 = false ∨ valuationOf q 898 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause744 (q : Snake 81) (h : Conditions q) : valuation q 835 = false ∨ valuation q 885 = false ∨ valuation q 898 = true := counterClause744 (baseVal q)

theorem counterClause745 (q : Nat → Bool) : valuationOf q 836 = false ∨ valuationOf q 881 = false ∨ valuationOf q 895 = true := by
  have hs : count892 q = (countLit q [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77]) + (countLit q [-81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77]) (l₂ := [-81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104])
  have hm := merge_two (literal (valuationOf q) (836)) (literal (valuationOf q) (881)) (literal (valuationOf q) (895)) (countLit q [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77]) (countLit q [-81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104]) (count892 q) 3 1 (meaning836 q) (meaning881 q) (meaning895 q) hs
  change valuationOf q 836 = false ∨ valuationOf q 881 = false ∨ valuationOf q 895 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause745 (q : Snake 81) (h : Conditions q) : valuation q 836 = false ∨ valuation q 881 = false ∨ valuation q 895 = true := counterClause745 (baseVal q)

theorem counterClause746 (q : Nat → Bool) : valuationOf q 836 = false ∨ valuationOf q 882 = false ∨ valuationOf q 896 = true := by
  have hs : count892 q = (countLit q [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77]) + (countLit q [-81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77]) (l₂ := [-81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104])
  have hm := merge_two (literal (valuationOf q) (836)) (literal (valuationOf q) (882)) (literal (valuationOf q) (896)) (countLit q [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77]) (countLit q [-81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104]) (count892 q) 3 2 (meaning836 q) (meaning882 q) (meaning896 q) hs
  change valuationOf q 836 = false ∨ valuationOf q 882 = false ∨ valuationOf q 896 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause746 (q : Snake 81) (h : Conditions q) : valuation q 836 = false ∨ valuation q 882 = false ∨ valuation q 896 = true := counterClause746 (baseVal q)

theorem counterClause747 (q : Nat → Bool) : valuationOf q 836 = false ∨ valuationOf q 883 = false ∨ valuationOf q 897 = true := by
  have hs : count892 q = (countLit q [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77]) + (countLit q [-81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77]) (l₂ := [-81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104])
  have hm := merge_two (literal (valuationOf q) (836)) (literal (valuationOf q) (883)) (literal (valuationOf q) (897)) (countLit q [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77]) (countLit q [-81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104]) (count892 q) 3 3 (meaning836 q) (meaning883 q) (meaning897 q) hs
  change valuationOf q 836 = false ∨ valuationOf q 883 = false ∨ valuationOf q 897 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause747 (q : Snake 81) (h : Conditions q) : valuation q 836 = false ∨ valuation q 883 = false ∨ valuation q 897 = true := counterClause747 (baseVal q)

theorem counterClause748 (q : Nat → Bool) : valuationOf q 836 = false ∨ valuationOf q 884 = false ∨ valuationOf q 898 = true := by
  have hs : count892 q = (countLit q [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77]) + (countLit q [-81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77]) (l₂ := [-81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104])
  have hm := merge_two (literal (valuationOf q) (836)) (literal (valuationOf q) (884)) (literal (valuationOf q) (898)) (countLit q [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77]) (countLit q [-81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104]) (count892 q) 3 4 (meaning836 q) (meaning884 q) (meaning898 q) hs
  change valuationOf q 836 = false ∨ valuationOf q 884 = false ∨ valuationOf q 898 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause748 (q : Snake 81) (h : Conditions q) : valuation q 836 = false ∨ valuation q 884 = false ∨ valuation q 898 = true := counterClause748 (baseVal q)

theorem counterClause749 (q : Nat → Bool) : valuationOf q 837 = false ∨ valuationOf q 882 = false ∨ valuationOf q 897 = true := by
  have hs : count892 q = (countLit q [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77]) + (countLit q [-81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77]) (l₂ := [-81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104])
  have hm := merge_two (literal (valuationOf q) (837)) (literal (valuationOf q) (882)) (literal (valuationOf q) (897)) (countLit q [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77]) (countLit q [-81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104]) (count892 q) 4 2 (meaning837 q) (meaning882 q) (meaning897 q) hs
  change valuationOf q 837 = false ∨ valuationOf q 882 = false ∨ valuationOf q 897 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause749 (q : Snake 81) (h : Conditions q) : valuation q 837 = false ∨ valuation q 882 = false ∨ valuation q 897 = true := counterClause749 (baseVal q)

theorem counterClause750 (q : Nat → Bool) : valuationOf q 837 = false ∨ valuationOf q 883 = false ∨ valuationOf q 898 = true := by
  have hs : count892 q = (countLit q [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77]) + (countLit q [-81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77]) (l₂ := [-81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104])
  have hm := merge_two (literal (valuationOf q) (837)) (literal (valuationOf q) (883)) (literal (valuationOf q) (898)) (countLit q [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77]) (countLit q [-81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104]) (count892 q) 4 3 (meaning837 q) (meaning883 q) (meaning898 q) hs
  change valuationOf q 837 = false ∨ valuationOf q 883 = false ∨ valuationOf q 898 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause750 (q : Snake 81) (h : Conditions q) : valuation q 837 = false ∨ valuation q 883 = false ∨ valuation q 898 = true := counterClause750 (baseVal q)

theorem counterClause751 (q : Nat → Bool) : valuationOf q 837 = false ∨ valuationOf q 884 = false ∨ valuationOf q 899 = true := by
  have hs : count892 q = (countLit q [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77]) + (countLit q [-81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77]) (l₂ := [-81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104])
  have hm := merge_two (literal (valuationOf q) (837)) (literal (valuationOf q) (884)) (literal (valuationOf q) (899)) (countLit q [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77]) (countLit q [-81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104]) (count892 q) 4 4 (meaning837 q) (meaning884 q) (meaning899 q) hs
  change valuationOf q 837 = false ∨ valuationOf q 884 = false ∨ valuationOf q 899 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause751 (q : Snake 81) (h : Conditions q) : valuation q 837 = false ∨ valuation q 884 = false ∨ valuation q 899 = true := counterClause751 (baseVal q)

theorem counterClause752 (q : Nat → Bool) : valuationOf q 838 = false ∨ valuationOf q 882 = false ∨ valuationOf q 898 = true := by
  have hs : count892 q = (countLit q [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77]) + (countLit q [-81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77]) (l₂ := [-81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104])
  have hm := merge_two (literal (valuationOf q) (838)) (literal (valuationOf q) (882)) (literal (valuationOf q) (898)) (countLit q [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77]) (countLit q [-81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104]) (count892 q) 5 2 (meaning838 q) (meaning882 q) (meaning898 q) hs
  change valuationOf q 838 = false ∨ valuationOf q 882 = false ∨ valuationOf q 898 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause752 (q : Snake 81) (h : Conditions q) : valuation q 838 = false ∨ valuation q 882 = false ∨ valuation q 898 = true := counterClause752 (baseVal q)

theorem counterClause753 (q : Nat → Bool) : valuationOf q 839 = false ∨ valuationOf q 897 = true := by
  have hs : count892 q = (countLit q [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77]) + (countLit q [-81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77]) (l₂ := [-81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104])
  have hm := merge_left (literal (valuationOf q) (839)) (literal (valuationOf q) (897)) (countLit q [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77]) (countLit q [-81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104]) (count892 q) 6 (meaning839 q) (meaning897 q) hs
  change valuationOf q 839 = false ∨ valuationOf q 897 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause753 (q : Snake 81) (h : Conditions q) : valuation q 839 = false ∨ valuation q 897 = true := counterClause753 (baseVal q)

theorem counterClause754 (q : Nat → Bool) : valuationOf q 839 = false ∨ valuationOf q 882 = false ∨ valuationOf q 899 = true := by
  have hs : count892 q = (countLit q [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77]) + (countLit q [-81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77]) (l₂ := [-81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104])
  have hm := merge_two (literal (valuationOf q) (839)) (literal (valuationOf q) (882)) (literal (valuationOf q) (899)) (countLit q [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77]) (countLit q [-81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104]) (count892 q) 6 2 (meaning839 q) (meaning882 q) (meaning899 q) hs
  change valuationOf q 839 = false ∨ valuationOf q 882 = false ∨ valuationOf q 899 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause754 (q : Snake 81) (h : Conditions q) : valuation q 839 = false ∨ valuation q 882 = false ∨ valuation q 899 = true := counterClause754 (baseVal q)

theorem counterClause755 (q : Nat → Bool) : valuationOf q 789 = false ∨ valuationOf q 899 = false ∨ valuationOf q 913 = true := by
  have hs : count903 q = (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25, -27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) + (countLit q [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77, -81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25, -27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) (l₂ := [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77, -81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104])
  have hm := merge_two (literal (valuationOf q) (789)) (literal (valuationOf q) (899)) (literal (valuationOf q) (913)) (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25, -27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) (countLit q [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77, -81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104]) (count903 q) 3 8 (meaning789 q) (meaning899 q) (meaning913 q) hs
  change valuationOf q 789 = false ∨ valuationOf q 899 = false ∨ valuationOf q 913 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause755 (q : Snake 81) (h : Conditions q) : valuation q 789 = false ∨ valuation q 899 = false ∨ valuation q 913 = true := counterClause755 (baseVal q)

theorem counterClause756 (q : Nat → Bool) : valuationOf q 790 = false ∨ valuationOf q 898 = false ∨ valuationOf q 913 = true := by
  have hs : count903 q = (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25, -27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) + (countLit q [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77, -81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25, -27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) (l₂ := [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77, -81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104])
  have hm := merge_two (literal (valuationOf q) (790)) (literal (valuationOf q) (898)) (literal (valuationOf q) (913)) (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25, -27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) (countLit q [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77, -81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104]) (count903 q) 4 7 (meaning790 q) (meaning898 q) (meaning913 q) hs
  change valuationOf q 790 = false ∨ valuationOf q 898 = false ∨ valuationOf q 913 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause756 (q : Snake 81) (h : Conditions q) : valuation q 790 = false ∨ valuation q 898 = false ∨ valuation q 913 = true := counterClause756 (baseVal q)

theorem counterClause757 (q : Nat → Bool) : valuationOf q 791 = false ∨ valuationOf q 897 = false ∨ valuationOf q 913 = true := by
  have hs : count903 q = (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25, -27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) + (countLit q [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77, -81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25, -27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) (l₂ := [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77, -81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104])
  have hm := merge_two (literal (valuationOf q) (791)) (literal (valuationOf q) (897)) (literal (valuationOf q) (913)) (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25, -27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) (countLit q [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77, -81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104]) (count903 q) 5 6 (meaning791 q) (meaning897 q) (meaning913 q) hs
  change valuationOf q 791 = false ∨ valuationOf q 897 = false ∨ valuationOf q 913 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause757 (q : Snake 81) (h : Conditions q) : valuation q 791 = false ∨ valuation q 897 = false ∨ valuation q 913 = true := counterClause757 (baseVal q)

theorem counterClause758 (q : Nat → Bool) : valuationOf q 792 = false ∨ valuationOf q 896 = false ∨ valuationOf q 913 = true := by
  have hs : count903 q = (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25, -27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) + (countLit q [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77, -81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25, -27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) (l₂ := [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77, -81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104])
  have hm := merge_two (literal (valuationOf q) (792)) (literal (valuationOf q) (896)) (literal (valuationOf q) (913)) (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25, -27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) (countLit q [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77, -81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104]) (count903 q) 6 5 (meaning792 q) (meaning896 q) (meaning913 q) hs
  change valuationOf q 792 = false ∨ valuationOf q 896 = false ∨ valuationOf q 913 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause758 (q : Snake 81) (h : Conditions q) : valuation q 792 = false ∨ valuation q 896 = false ∨ valuation q 913 = true := counterClause758 (baseVal q)

theorem counterClause759 (q : Nat → Bool) : valuationOf q 793 = false ∨ valuationOf q 895 = false ∨ valuationOf q 913 = true := by
  have hs : count903 q = (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25, -27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) + (countLit q [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77, -81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25, -27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) (l₂ := [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77, -81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104])
  have hm := merge_two (literal (valuationOf q) (793)) (literal (valuationOf q) (895)) (literal (valuationOf q) (913)) (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25, -27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) (countLit q [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77, -81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104]) (count903 q) 7 4 (meaning793 q) (meaning895 q) (meaning913 q) hs
  change valuationOf q 793 = false ∨ valuationOf q 895 = false ∨ valuationOf q 913 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause759 (q : Snake 81) (h : Conditions q) : valuation q 793 = false ∨ valuation q 895 = false ∨ valuation q 913 = true := counterClause759 (baseVal q)

theorem counterClause760 (q : Nat → Bool) : valuationOf q 794 = false ∨ valuationOf q 894 = false ∨ valuationOf q 913 = true := by
  have hs : count903 q = (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25, -27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) + (countLit q [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77, -81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25, -27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) (l₂ := [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77, -81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104])
  have hm := merge_two (literal (valuationOf q) (794)) (literal (valuationOf q) (894)) (literal (valuationOf q) (913)) (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25, -27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) (countLit q [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77, -81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104]) (count903 q) 8 3 (meaning794 q) (meaning894 q) (meaning913 q) hs
  change valuationOf q 794 = false ∨ valuationOf q 894 = false ∨ valuationOf q 913 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause760 (q : Snake 81) (h : Conditions q) : valuation q 794 = false ∨ valuation q 894 = false ∨ valuation q 913 = true := counterClause760 (baseVal q)

theorem counterClause761 (q : Nat → Bool) : valuationOf q 795 = false ∨ valuationOf q 893 = false ∨ valuationOf q 913 = true := by
  have hs : count903 q = (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25, -27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) + (countLit q [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77, -81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25, -27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) (l₂ := [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77, -81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104])
  have hm := merge_two (literal (valuationOf q) (795)) (literal (valuationOf q) (893)) (literal (valuationOf q) (913)) (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25, -27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) (countLit q [-53, -56, -58, -59, -61, -64, -66, -67, -69, -73, -74, -75, -77, -81, -82, -84, -86, -88, -89, -91, -94, -96, -97, -99, -102, -104]) (count903 q) 9 2 (meaning795 q) (meaning893 q) (meaning913 q) hs
  change valuationOf q 795 = false ∨ valuationOf q 893 = false ∨ valuationOf q 913 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause761 (q : Snake 81) (h : Conditions q) : valuation q 795 = false ∨ valuation q 893 = false ∨ valuation q 913 = true := counterClause761 (baseVal q)

theorem clause762 (q : Snake 81) (h : Conditions q) : valuation q 913 = false := by
  rw [value913]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count903 (baseVal q) = (evenSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_even_bound q h
  rw [evenSide_length] at hb
  rw [he]
  omega

theorem counterClause763 (q : Nat → Bool) : valuationOf q 5 = true ∨ valuationOf q 1210 = true := by
  have hs : count1210 q = (countLit q [-2]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-5])
  have hm := merge_right (literal (valuationOf q) (-5)) (literal (valuationOf q) (1210)) (countLit q [-2]) (countLit q [-5]) (count1210 q) 1 (meaningNeg5 q) (meaning1210 q) hs
  change (! (valuationOf q 5)) = false ∨ valuationOf q 1210 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause763 (q : Snake 81) (h : Conditions q) : valuation q 5 = true ∨ valuation q 1210 = true := counterClause763 (baseVal q)

theorem counterClause764 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1210 = true := by
  have hs : count1210 q = (countLit q [-2]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-5])
  have hm := merge_left (literal (valuationOf q) (-2)) (literal (valuationOf q) (1210)) (countLit q [-2]) (countLit q [-5]) (count1210 q) 1 (meaningNeg2 q) (meaning1210 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1210 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause764 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1210 = true := counterClause764 (baseVal q)

theorem counterClause765 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 5 = true ∨ valuationOf q 1211 = true := by
  have hs : count1210 q = (countLit q [-2]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-5])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (-5)) (literal (valuationOf q) (1211)) (countLit q [-2]) (countLit q [-5]) (count1210 q) 1 1 (meaningNeg2 q) (meaningNeg5 q) (meaning1211 q) hs
  change (! (valuationOf q 2)) = false ∨ (! (valuationOf q 5)) = false ∨ valuationOf q 1211 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause765 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 5 = true ∨ valuation q 1211 = true := counterClause765 (baseVal q)

theorem counterClause766 (q : Nat → Bool) : valuationOf q 1210 = false ∨ valuationOf q 1212 = true := by
  have hs : count1212 q = (countLit q [-1]) + (countLit q [-2, -5]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-2, -5])
  have hm := merge_right (literal (valuationOf q) (1210)) (literal (valuationOf q) (1212)) (countLit q [-1]) (countLit q [-2, -5]) (count1212 q) 1 (meaning1210 q) (meaning1212 q) hs
  change valuationOf q 1210 = false ∨ valuationOf q 1212 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause766 (q : Snake 81) (h : Conditions q) : valuation q 1210 = false ∨ valuation q 1212 = true := counterClause766 (baseVal q)

theorem counterClause767 (q : Nat → Bool) : valuationOf q 1211 = false ∨ valuationOf q 1213 = true := by
  have hs : count1212 q = (countLit q [-1]) + (countLit q [-2, -5]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-2, -5])
  have hm := merge_right (literal (valuationOf q) (1211)) (literal (valuationOf q) (1213)) (countLit q [-1]) (countLit q [-2, -5]) (count1212 q) 2 (meaning1211 q) (meaning1213 q) hs
  change valuationOf q 1211 = false ∨ valuationOf q 1213 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause767 (q : Snake 81) (h : Conditions q) : valuation q 1211 = false ∨ valuation q 1213 = true := counterClause767 (baseVal q)

theorem counterClause768 (q : Nat → Bool) : valuationOf q 1 = true ∨ valuationOf q 1212 = true := by
  have hs : count1212 q = (countLit q [-1]) + (countLit q [-2, -5]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-2, -5])
  have hm := merge_left (literal (valuationOf q) (-1)) (literal (valuationOf q) (1212)) (countLit q [-1]) (countLit q [-2, -5]) (count1212 q) 1 (meaningNeg1 q) (meaning1212 q) hs
  change (! (valuationOf q 1)) = false ∨ valuationOf q 1212 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause768 (q : Snake 81) (h : Conditions q) : valuation q 1 = true ∨ valuation q 1212 = true := counterClause768 (baseVal q)

theorem block23 (q : Snake 81) (h : Conditions q) : B112E174.Block23 (valuation q) :=
  ⟨clause737 q h, clause738 q h, clause739 q h, clause740 q h, clause741 q h, clause742 q h, clause743 q h, clause744 q h, clause745 q h, clause746 q h, clause747 q h, clause748 q h, clause749 q h, clause750 q h, clause751 q h, clause752 q h, clause753 q h, clause754 q h, clause755 q h, clause756 q h, clause757 q h, clause758 q h, clause759 q h, clause760 q h, clause761 q h, clause762 q h, clause763 q h, clause764 q h, clause765 q h, clause766 q h, clause767 q h, clause768 q h⟩

end
end Snake9.Regrowth.E112174
