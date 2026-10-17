import E112040Semantics
import B112E040Inputs
namespace Snake9.Regrowth.E112040
noncomputable section
local instance blockDec28 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause897 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 36 = true ∨ valuationOf q 869 = true := by
  have hs : count868 q = (countLit q [-35]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-36])
  have hm := merge_two (literal (valuationOf q) (-35)) (literal (valuationOf q) (-36)) (literal (valuationOf q) (869)) (countLit q [-35]) (countLit q [-36]) (count868 q) 1 1 (meaningNeg35 q) (meaningNeg36 q) (meaning869 q) hs
  change (! (valuationOf q 35)) = false ∨ (! (valuationOf q 36)) = false ∨ valuationOf q 869 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause897 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 36 = true ∨ valuation q 869 = true := counterClause897 (baseVal q)

theorem counterClause898 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 870 = true := by
  have hs : count870 q = (countLit q [-40]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-41])
  have hm := merge_left (literal (valuationOf q) (-40)) (literal (valuationOf q) (870)) (countLit q [-40]) (countLit q [-41]) (count870 q) 1 (meaningNeg40 q) (meaning870 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 870 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause898 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 870 = true := counterClause898 (baseVal q)

theorem counterClause899 (q : Nat → Bool) : valuationOf q 869 = false ∨ valuationOf q 870 = false ∨ valuationOf q 874 = true := by
  have hs : count872 q = (countLit q [-35, -36]) + (countLit q [-40, -41]) := List.countP_append (p := literal q) (l₁ := [-35, -36]) (l₂ := [-40, -41])
  have hm := merge_two (literal (valuationOf q) (869)) (literal (valuationOf q) (870)) (literal (valuationOf q) (874)) (countLit q [-35, -36]) (countLit q [-40, -41]) (count872 q) 2 1 (meaning869 q) (meaning870 q) (meaning874 q) hs
  change valuationOf q 869 = false ∨ valuationOf q 870 = false ∨ valuationOf q 874 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause899 (q : Snake 81) (h : Conditions q) : valuation q 869 = false ∨ valuation q 870 = false ∨ valuation q 874 = true := counterClause899 (baseVal q)

theorem counterClause900 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 874 = false ∨ valuationOf q 879 = true := by
  have hs : count876 q = (countLit q [-29, -31, -33]) + (countLit q [-35, -36, -40, -41]) := List.countP_append (p := literal q) (l₁ := [-29, -31, -33]) (l₂ := [-35, -36, -40, -41])
  have hm := merge_two (literal (valuationOf q) (865)) (literal (valuationOf q) (874)) (literal (valuationOf q) (879)) (countLit q [-29, -31, -33]) (countLit q [-35, -36, -40, -41]) (count876 q) 1 3 (meaning865 q) (meaning874 q) (meaning879 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 874 = false ∨ valuationOf q 879 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause900 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 874 = false ∨ valuation q 879 = true := counterClause900 (baseVal q)

theorem counterClause901 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 891 = true := by
  have hs : count891 q = (countLit q [-53]) + (countLit q [-55]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-55])
  have hm := merge_left (literal (valuationOf q) (-53)) (literal (valuationOf q) (891)) (countLit q [-53]) (countLit q [-55]) (count891 q) 1 (meaningNeg53 q) (meaning891 q) hs
  change (! (valuationOf q 53)) = false ∨ valuationOf q 891 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause901 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 891 = true := counterClause901 (baseVal q)

theorem counterClause902 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 893 = true := by
  have hs : count893 q = (countLit q [-57]) + (countLit q [-59]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-59])
  have hm := merge_left (literal (valuationOf q) (-57)) (literal (valuationOf q) (893)) (countLit q [-57]) (countLit q [-59]) (count893 q) 1 (meaningNeg57 q) (meaning893 q) hs
  change (! (valuationOf q 57)) = false ∨ valuationOf q 893 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause902 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 893 = true := counterClause902 (baseVal q)

theorem counterClause903 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 59 = true ∨ valuationOf q 894 = true := by
  have hs : count893 q = (countLit q [-57]) + (countLit q [-59]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-59])
  have hm := merge_two (literal (valuationOf q) (-57)) (literal (valuationOf q) (-59)) (literal (valuationOf q) (894)) (countLit q [-57]) (countLit q [-59]) (count893 q) 1 1 (meaningNeg57 q) (meaningNeg59 q) (meaning894 q) hs
  change (! (valuationOf q 57)) = false ∨ (! (valuationOf q 59)) = false ∨ valuationOf q 894 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause903 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 59 = true ∨ valuation q 894 = true := counterClause903 (baseVal q)

theorem counterClause904 (q : Nat → Bool) : valuationOf q 894 = false ∨ valuationOf q 896 = true := by
  have hs : count895 q = (countLit q [-53, -55]) + (countLit q [-57, -59]) := List.countP_append (p := literal q) (l₁ := [-53, -55]) (l₂ := [-57, -59])
  have hm := merge_right (literal (valuationOf q) (894)) (literal (valuationOf q) (896)) (countLit q [-53, -55]) (countLit q [-57, -59]) (count895 q) 2 (meaning894 q) (meaning896 q) hs
  change valuationOf q 894 = false ∨ valuationOf q 896 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause904 (q : Snake 81) (h : Conditions q) : valuation q 894 = false ∨ valuation q 896 = true := counterClause904 (baseVal q)

theorem counterClause905 (q : Nat → Bool) : valuationOf q 891 = false ∨ valuationOf q 893 = false ∨ valuationOf q 896 = true := by
  have hs : count895 q = (countLit q [-53, -55]) + (countLit q [-57, -59]) := List.countP_append (p := literal q) (l₁ := [-53, -55]) (l₂ := [-57, -59])
  have hm := merge_two (literal (valuationOf q) (891)) (literal (valuationOf q) (893)) (literal (valuationOf q) (896)) (countLit q [-53, -55]) (countLit q [-57, -59]) (count895 q) 1 1 (meaning891 q) (meaning893 q) (meaning896 q) hs
  change valuationOf q 891 = false ∨ valuationOf q 893 = false ∨ valuationOf q 896 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause905 (q : Snake 81) (h : Conditions q) : valuation q 891 = false ∨ valuation q 893 = false ∨ valuation q 896 = true := counterClause905 (baseVal q)

theorem counterClause906 (q : Nat → Bool) : valuationOf q 896 = false ∨ valuationOf q 900 = true := by
  have hs : count899 q = (countLit q [-43, -45, -49, -51]) + (countLit q [-53, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -49, -51]) (l₂ := [-53, -55, -57, -59])
  have hm := merge_right (literal (valuationOf q) (896)) (literal (valuationOf q) (900)) (countLit q [-43, -45, -49, -51]) (countLit q [-53, -55, -57, -59]) (count899 q) 2 (meaning896 q) (meaning900 q) hs
  change valuationOf q 896 = false ∨ valuationOf q 900 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause906 (q : Snake 81) (h : Conditions q) : valuation q 896 = false ∨ valuation q 900 = true := counterClause906 (baseVal q)

theorem counterClause907 (q : Nat → Bool) : valuationOf q 879 = false ∨ valuationOf q 900 = false ∨ valuationOf q 912 = true := by
  have hs : count907 q = (countLit q [-29, -31, -33, -35, -36, -40, -41]) + (countLit q [-43, -45, -49, -51, -53, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-29, -31, -33, -35, -36, -40, -41]) (l₂ := [-43, -45, -49, -51, -53, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (879)) (literal (valuationOf q) (900)) (literal (valuationOf q) (912)) (countLit q [-29, -31, -33, -35, -36, -40, -41]) (countLit q [-43, -45, -49, -51, -53, -55, -57, -59]) (count907 q) 4 2 (meaning879 q) (meaning900 q) (meaning912 q) hs
  change valuationOf q 879 = false ∨ valuationOf q 900 = false ∨ valuationOf q 912 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause907 (q : Snake 81) (h : Conditions q) : valuation q 879 = false ∨ valuation q 900 = false ∨ valuation q 912 = true := counterClause907 (baseVal q)

theorem counterClause908 (q : Nat → Bool) : valuationOf q 854 = false ∨ valuationOf q 912 = false ∨ valuationOf q 933 = true := by
  have hs : count922 q = (countLit q [-1, -2, -5, -8, -10, -11, -13, -14, -17, -19, -20, -23, -25, -27]) + (countLit q [-29, -31, -33, -35, -36, -40, -41, -43, -45, -49, -51, -53, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -8, -10, -11, -13, -14, -17, -19, -20, -23, -25, -27]) (l₂ := [-29, -31, -33, -35, -36, -40, -41, -43, -45, -49, -51, -53, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (854)) (literal (valuationOf q) (912)) (literal (valuationOf q) (933)) (countLit q [-1, -2, -5, -8, -10, -11, -13, -14, -17, -19, -20, -23, -25, -27]) (countLit q [-29, -31, -33, -35, -36, -40, -41, -43, -45, -49, -51, -53, -55, -57, -59]) (count922 q) 6 6 (meaning854 q) (meaning912 q) (meaning933 q) hs
  change valuationOf q 854 = false ∨ valuationOf q 912 = false ∨ valuationOf q 933 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause908 (q : Snake 81) (h : Conditions q) : valuation q 854 = false ∨ valuation q 912 = false ∨ valuation q 933 = true := counterClause908 (baseVal q)

theorem counterClause909 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 68 = true ∨ valuationOf q 947 = true := by
  have hs : count946 q = (countLit q [-67]) + (countLit q [-68]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-68])
  have hm := merge_two (literal (valuationOf q) (-67)) (literal (valuationOf q) (-68)) (literal (valuationOf q) (947)) (countLit q [-67]) (countLit q [-68]) (count946 q) 1 1 (meaningNeg67 q) (meaningNeg68 q) (meaning947 q) hs
  change (! (valuationOf q 67)) = false ∨ (! (valuationOf q 68)) = false ∨ valuationOf q 947 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause909 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 68 = true ∨ valuation q 947 = true := counterClause909 (baseVal q)

theorem counterClause910 (q : Nat → Bool) : valuationOf q 947 = false ∨ valuationOf q 951 = true := by
  have hs : count950 q = (countLit q [-67, -68]) + (countLit q [-69, -72]) := List.countP_append (p := literal q) (l₁ := [-67, -68]) (l₂ := [-69, -72])
  have hm := merge_left (literal (valuationOf q) (947)) (literal (valuationOf q) (951)) (countLit q [-67, -68]) (countLit q [-69, -72]) (count950 q) 2 (meaning947 q) (meaning951 q) hs
  change valuationOf q 947 = false ∨ valuationOf q 951 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause910 (q : Snake 81) (h : Conditions q) : valuation q 947 = false ∨ valuation q 951 = true := counterClause910 (baseVal q)

theorem counterClause911 (q : Nat → Bool) : valuationOf q 951 = false ∨ valuationOf q 955 = true := by
  have hs : count954 q = (countLit q [-60, -65, -66]) + (countLit q [-67, -68, -69, -72]) := List.countP_append (p := literal q) (l₁ := [-60, -65, -66]) (l₂ := [-67, -68, -69, -72])
  have hm := merge_right (literal (valuationOf q) (951)) (literal (valuationOf q) (955)) (countLit q [-60, -65, -66]) (countLit q [-67, -68, -69, -72]) (count954 q) 2 (meaning951 q) (meaning955 q) hs
  change valuationOf q 951 = false ∨ valuationOf q 955 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause911 (q : Snake 81) (h : Conditions q) : valuation q 951 = false ∨ valuation q 955 = true := counterClause911 (baseVal q)

theorem counterClause912 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 963 = true := by
  have hs : count963 q = (countLit q [-78]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-81])
  have hm := merge_right (literal (valuationOf q) (-81)) (literal (valuationOf q) (963)) (countLit q [-78]) (countLit q [-81]) (count963 q) 1 (meaningNeg81 q) (meaning963 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 963 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause912 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 963 = true := counterClause912 (baseVal q)

theorem counterClause913 (q : Nat → Bool) : valuationOf q 963 = false ∨ valuationOf q 965 = true := by
  have hs : count965 q = (countLit q [-74, -75]) + (countLit q [-78, -81]) := List.countP_append (p := literal q) (l₁ := [-74, -75]) (l₂ := [-78, -81])
  have hm := merge_right (literal (valuationOf q) (963)) (literal (valuationOf q) (965)) (countLit q [-74, -75]) (countLit q [-78, -81]) (count965 q) 1 (meaning963 q) (meaning965 q) hs
  change valuationOf q 963 = false ∨ valuationOf q 965 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause913 (q : Snake 81) (h : Conditions q) : valuation q 963 = false ∨ valuation q 965 = true := counterClause913 (baseVal q)

theorem counterClause914 (q : Nat → Bool) : valuationOf q 965 = false ∨ valuationOf q 977 = true := by
  have hs : count977 q = (countLit q [-74, -75, -78, -81]) + (countLit q [-83, -84, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-74, -75, -78, -81]) (l₂ := [-83, -84, -86, -89])
  have hm := merge_left (literal (valuationOf q) (965)) (literal (valuationOf q) (977)) (countLit q [-74, -75, -78, -81]) (countLit q [-83, -84, -86, -89]) (count977 q) 1 (meaning965 q) (meaning977 q) hs
  change valuationOf q 965 = false ∨ valuationOf q 977 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause914 (q : Snake 81) (h : Conditions q) : valuation q 965 = false ∨ valuation q 977 = true := counterClause914 (baseVal q)

theorem counterClause915 (q : Nat → Bool) : valuationOf q 955 = false ∨ valuationOf q 977 = false ∨ valuationOf q 987 = true := by
  have hs : count985 q = (countLit q [-60, -65, -66, -67, -68, -69, -72]) + (countLit q [-74, -75, -78, -81, -83, -84, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-60, -65, -66, -67, -68, -69, -72]) (l₂ := [-74, -75, -78, -81, -83, -84, -86, -89])
  have hm := merge_two (literal (valuationOf q) (955)) (literal (valuationOf q) (977)) (literal (valuationOf q) (987)) (countLit q [-60, -65, -66, -67, -68, -69, -72]) (countLit q [-74, -75, -78, -81, -83, -84, -86, -89]) (count985 q) 2 1 (meaning955 q) (meaning977 q) (meaning987 q) hs
  change valuationOf q 955 = false ∨ valuationOf q 977 = false ∨ valuationOf q 987 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause915 (q : Snake 81) (h : Conditions q) : valuation q 955 = false ∨ valuation q 977 = false ∨ valuation q 987 = true := counterClause915 (baseVal q)

theorem counterClause916 (q : Nat → Bool) : valuationOf q 96 = true ∨ valuationOf q 1000 = true := by
  have hs : count1000 q = (countLit q [-93]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-93]) (l₂ := [-96])
  have hm := merge_right (literal (valuationOf q) (-96)) (literal (valuationOf q) (1000)) (countLit q [-93]) (countLit q [-96]) (count1000 q) 1 (meaningNeg96 q) (meaning1000 q) hs
  change (! (valuationOf q 96)) = false ∨ valuationOf q 1000 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause916 (q : Snake 81) (h : Conditions q) : valuation q 96 = true ∨ valuation q 1000 = true := counterClause916 (baseVal q)

theorem counterClause917 (q : Nat → Bool) : valuationOf q 1000 = false ∨ valuationOf q 1002 = true := by
  have hs : count1002 q = (countLit q [-91]) + (countLit q [-93, -96]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-93, -96])
  have hm := merge_right (literal (valuationOf q) (1000)) (literal (valuationOf q) (1002)) (countLit q [-91]) (countLit q [-93, -96]) (count1002 q) 1 (meaning1000 q) (meaning1002 q) hs
  change valuationOf q 1000 = false ∨ valuationOf q 1002 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause917 (q : Snake 81) (h : Conditions q) : valuation q 1000 = false ∨ valuation q 1002 = true := counterClause917 (baseVal q)

theorem counterClause918 (q : Nat → Bool) : valuationOf q 97 = true ∨ valuationOf q 1005 = true := by
  have hs : count1005 q = (countLit q [-97]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-100])
  have hm := merge_left (literal (valuationOf q) (-97)) (literal (valuationOf q) (1005)) (countLit q [-97]) (countLit q [-100]) (count1005 q) 1 (meaningNeg97 q) (meaning1005 q) hs
  change (! (valuationOf q 97)) = false ∨ valuationOf q 1005 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause918 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 1005 = true := counterClause918 (baseVal q)

theorem counterClause919 (q : Nat → Bool) : valuationOf q 1005 = false ∨ valuationOf q 1009 = true := by
  have hs : count1009 q = (countLit q [-97, -100]) + (countLit q [-101, -102]) := List.countP_append (p := literal q) (l₁ := [-97, -100]) (l₂ := [-101, -102])
  have hm := merge_left (literal (valuationOf q) (1005)) (literal (valuationOf q) (1009)) (countLit q [-97, -100]) (countLit q [-101, -102]) (count1009 q) 1 (meaning1005 q) (meaning1009 q) hs
  change valuationOf q 1005 = false ∨ valuationOf q 1009 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause919 (q : Snake 81) (h : Conditions q) : valuation q 1005 = false ∨ valuation q 1009 = true := counterClause919 (baseVal q)

theorem counterClause920 (q : Nat → Bool) : valuationOf q 1002 = false ∨ valuationOf q 1009 = false ∨ valuationOf q 1014 = true := by
  have hs : count1013 q = (countLit q [-91, -93, -96]) + (countLit q [-97, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -96]) (l₂ := [-97, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1002)) (literal (valuationOf q) (1009)) (literal (valuationOf q) (1014)) (countLit q [-91, -93, -96]) (countLit q [-97, -100, -101, -102]) (count1013 q) 1 1 (meaning1002 q) (meaning1009 q) (meaning1014 q) hs
  change valuationOf q 1002 = false ∨ valuationOf q 1009 = false ∨ valuationOf q 1014 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause920 (q : Snake 81) (h : Conditions q) : valuation q 1002 = false ∨ valuation q 1009 = false ∨ valuation q 1014 = true := counterClause920 (baseVal q)

theorem counterClause921 (q : Nat → Bool) : valuationOf q 108 = true ∨ valuationOf q 1022 = true := by
  have hs : count1022 q = (countLit q [-107]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-107]) (l₂ := [-108])
  have hm := merge_right (literal (valuationOf q) (-108)) (literal (valuationOf q) (1022)) (countLit q [-107]) (countLit q [-108]) (count1022 q) 1 (meaningNeg108 q) (meaning1022 q) hs
  change (! (valuationOf q 108)) = false ∨ valuationOf q 1022 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause921 (q : Snake 81) (h : Conditions q) : valuation q 108 = true ∨ valuation q 1022 = true := counterClause921 (baseVal q)

theorem counterClause922 (q : Nat → Bool) : valuationOf q 1022 = false ∨ valuationOf q 1024 = true := by
  have hs : count1024 q = (countLit q [-103, -104]) + (countLit q [-107, -108]) := List.countP_append (p := literal q) (l₁ := [-103, -104]) (l₂ := [-107, -108])
  have hm := merge_right (literal (valuationOf q) (1022)) (literal (valuationOf q) (1024)) (countLit q [-103, -104]) (countLit q [-107, -108]) (count1024 q) 1 (meaning1022 q) (meaning1024 q) hs
  change valuationOf q 1022 = false ∨ valuationOf q 1024 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause922 (q : Snake 81) (h : Conditions q) : valuation q 1022 = false ∨ valuation q 1024 = true := counterClause922 (baseVal q)

theorem counterClause923 (q : Nat → Bool) : valuationOf q 119 = true ∨ valuationOf q 1030 = true := by
  have hs : count1030 q = (countLit q [-118]) + (countLit q [-119]) := List.countP_append (p := literal q) (l₁ := [-118]) (l₂ := [-119])
  have hm := merge_right (literal (valuationOf q) (-119)) (literal (valuationOf q) (1030)) (countLit q [-118]) (countLit q [-119]) (count1030 q) 1 (meaningNeg119 q) (meaning1030 q) hs
  change (! (valuationOf q 119)) = false ∨ valuationOf q 1030 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause923 (q : Snake 81) (h : Conditions q) : valuation q 119 = true ∨ valuation q 1030 = true := counterClause923 (baseVal q)

theorem counterClause924 (q : Nat → Bool) : valuationOf q 1030 = false ∨ valuationOf q 1032 = true := by
  have hs : count1032 q = (countLit q [-112, -114]) + (countLit q [-118, -119]) := List.countP_append (p := literal q) (l₁ := [-112, -114]) (l₂ := [-118, -119])
  have hm := merge_right (literal (valuationOf q) (1030)) (literal (valuationOf q) (1032)) (countLit q [-112, -114]) (countLit q [-118, -119]) (count1032 q) 1 (meaning1030 q) (meaning1032 q) hs
  change valuationOf q 1030 = false ∨ valuationOf q 1032 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause924 (q : Snake 81) (h : Conditions q) : valuation q 1030 = false ∨ valuation q 1032 = true := counterClause924 (baseVal q)

theorem counterClause925 (q : Nat → Bool) : valuationOf q 1024 = false ∨ valuationOf q 1032 = false ∨ valuationOf q 1037 = true := by
  have hs : count1036 q = (countLit q [-103, -104, -107, -108]) + (countLit q [-112, -114, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-103, -104, -107, -108]) (l₂ := [-112, -114, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1024)) (literal (valuationOf q) (1032)) (literal (valuationOf q) (1037)) (countLit q [-103, -104, -107, -108]) (countLit q [-112, -114, -118, -119]) (count1036 q) 1 1 (meaning1024 q) (meaning1032 q) (meaning1037 q) hs
  change valuationOf q 1024 = false ∨ valuationOf q 1032 = false ∨ valuationOf q 1037 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause925 (q : Snake 81) (h : Conditions q) : valuation q 1024 = false ∨ valuation q 1032 = false ∨ valuation q 1037 = true := counterClause925 (baseVal q)

theorem counterClause926 (q : Nat → Bool) : valuationOf q 1014 = false ∨ valuationOf q 1037 = false ∨ valuationOf q 1047 = true := by
  have hs : count1044 q = (countLit q [-91, -93, -96, -97, -100, -101, -102]) + (countLit q [-103, -104, -107, -108, -112, -114, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -96, -97, -100, -101, -102]) (l₂ := [-103, -104, -107, -108, -112, -114, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1014)) (literal (valuationOf q) (1037)) (literal (valuationOf q) (1047)) (countLit q [-91, -93, -96, -97, -100, -101, -102]) (countLit q [-103, -104, -107, -108, -112, -114, -118, -119]) (count1044 q) 2 2 (meaning1014 q) (meaning1037 q) (meaning1047 q) hs
  change valuationOf q 1014 = false ∨ valuationOf q 1037 = false ∨ valuationOf q 1047 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause926 (q : Snake 81) (h : Conditions q) : valuation q 1014 = false ∨ valuation q 1037 = false ∨ valuation q 1047 = true := counterClause926 (baseVal q)

theorem counterClause927 (q : Nat → Bool) : valuationOf q 987 = false ∨ valuationOf q 1047 = false ∨ valuationOf q 1065 = true := by
  have hs : count1059 q = (countLit q [-60, -65, -66, -67, -68, -69, -72, -74, -75, -78, -81, -83, -84, -86, -89]) + (countLit q [-91, -93, -96, -97, -100, -101, -102, -103, -104, -107, -108, -112, -114, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-60, -65, -66, -67, -68, -69, -72, -74, -75, -78, -81, -83, -84, -86, -89]) (l₂ := [-91, -93, -96, -97, -100, -101, -102, -103, -104, -107, -108, -112, -114, -118, -119])
  have hm := merge_two (literal (valuationOf q) (987)) (literal (valuationOf q) (1047)) (literal (valuationOf q) (1065)) (countLit q [-60, -65, -66, -67, -68, -69, -72, -74, -75, -78, -81, -83, -84, -86, -89]) (countLit q [-91, -93, -96, -97, -100, -101, -102, -103, -104, -107, -108, -112, -114, -118, -119]) (count1059 q) 3 4 (meaning987 q) (meaning1047 q) (meaning1065 q) hs
  change valuationOf q 987 = false ∨ valuationOf q 1047 = false ∨ valuationOf q 1065 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause927 (q : Snake 81) (h : Conditions q) : valuation q 987 = false ∨ valuation q 1047 = false ∨ valuation q 1065 = true := counterClause927 (baseVal q)

theorem counterClause928 (q : Nat → Bool) : valuationOf q 933 = false ∨ valuationOf q 1065 = false ∨ valuationOf q 1096 = true := by
  have hs : count1078 q = (countLit q [-1, -2, -5, -8, -10, -11, -13, -14, -17, -19, -20, -23, -25, -27, -29, -31, -33, -35, -36, -40, -41, -43, -45, -49, -51, -53, -55, -57, -59]) + (countLit q [-60, -65, -66, -67, -68, -69, -72, -74, -75, -78, -81, -83, -84, -86, -89, -91, -93, -96, -97, -100, -101, -102, -103, -104, -107, -108, -112, -114, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -8, -10, -11, -13, -14, -17, -19, -20, -23, -25, -27, -29, -31, -33, -35, -36, -40, -41, -43, -45, -49, -51, -53, -55, -57, -59]) (l₂ := [-60, -65, -66, -67, -68, -69, -72, -74, -75, -78, -81, -83, -84, -86, -89, -91, -93, -96, -97, -100, -101, -102, -103, -104, -107, -108, -112, -114, -118, -119])
  have hm := merge_two (literal (valuationOf q) (933)) (literal (valuationOf q) (1065)) (literal (valuationOf q) (1096)) (countLit q [-1, -2, -5, -8, -10, -11, -13, -14, -17, -19, -20, -23, -25, -27, -29, -31, -33, -35, -36, -40, -41, -43, -45, -49, -51, -53, -55, -57, -59]) (countLit q [-60, -65, -66, -67, -68, -69, -72, -74, -75, -78, -81, -83, -84, -86, -89, -91, -93, -96, -97, -100, -101, -102, -103, -104, -107, -108, -112, -114, -118, -119]) (count1078 q) 12 7 (meaning933 q) (meaning1065 q) (meaning1096 q) hs
  change valuationOf q 933 = false ∨ valuationOf q 1065 = false ∨ valuationOf q 1096 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause928 (q : Snake 81) (h : Conditions q) : valuation q 933 = false ∨ valuation q 1065 = false ∨ valuation q 1096 = true := counterClause928 (baseVal q)

theorem block28 (q : Snake 81) (h : Conditions q) : B112E040.Block28 (valuation q) :=
  ⟨clause897 q h, clause898 q h, clause899 q h, clause900 q h, clause901 q h, clause902 q h, clause903 q h, clause904 q h, clause905 q h, clause906 q h, clause907 q h, clause908 q h, clause909 q h, clause910 q h, clause911 q h, clause912 q h, clause913 q h, clause914 q h, clause915 q h, clause916 q h, clause917 q h, clause918 q h, clause919 q h, clause920 q h, clause921 q h, clause922 q h, clause923 q h, clause924 q h, clause925 q h, clause926 q h, clause927 q h, clause928 q h⟩

end
end Snake9.Regrowth.E112040
