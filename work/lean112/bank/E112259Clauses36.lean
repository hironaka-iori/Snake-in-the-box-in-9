import E112259Semantics
import B112E259Inputs
namespace Snake9.Regrowth.E112259
noncomputable section
local instance blockDec36 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1153 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 943 = true := by
  have hs : count943 q = (countLit q [-84]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-85])
  have hm := merge_right (literal (valuationOf q) (-85)) (literal (valuationOf q) (943)) (countLit q [-84]) (countLit q [-85]) (count943 q) 1 (meaningNeg85 q) (meaning943 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 943 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1153 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 943 = true := counterClause1153 (baseVal q)

theorem counterClause1154 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 943 = true := by
  have hs : count943 q = (countLit q [-84]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-85])
  have hm := merge_left (literal (valuationOf q) (-84)) (literal (valuationOf q) (943)) (countLit q [-84]) (countLit q [-85]) (count943 q) 1 (meaningNeg84 q) (meaning943 q) hs
  change (! (valuationOf q 84)) = false ∨ valuationOf q 943 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1154 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 943 = true := counterClause1154 (baseVal q)

theorem counterClause1155 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 85 = true ∨ valuationOf q 944 = true := by
  have hs : count943 q = (countLit q [-84]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-85])
  have hm := merge_two (literal (valuationOf q) (-84)) (literal (valuationOf q) (-85)) (literal (valuationOf q) (944)) (countLit q [-84]) (countLit q [-85]) (count943 q) 1 1 (meaningNeg84 q) (meaningNeg85 q) (meaning944 q) hs
  change (! (valuationOf q 84)) = false ∨ (! (valuationOf q 85)) = false ∨ valuationOf q 944 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1155 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 85 = true ∨ valuation q 944 = true := counterClause1155 (baseVal q)

theorem counterClause1156 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 945 = true := by
  have hs : count945 q = (countLit q [-87]) + (countLit q [-88]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-88])
  have hm := merge_right (literal (valuationOf q) (-88)) (literal (valuationOf q) (945)) (countLit q [-87]) (countLit q [-88]) (count945 q) 1 (meaningNeg88 q) (meaning945 q) hs
  change (! (valuationOf q 88)) = false ∨ valuationOf q 945 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1156 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 945 = true := counterClause1156 (baseVal q)

theorem counterClause1157 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 945 = true := by
  have hs : count945 q = (countLit q [-87]) + (countLit q [-88]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-88])
  have hm := merge_left (literal (valuationOf q) (-87)) (literal (valuationOf q) (945)) (countLit q [-87]) (countLit q [-88]) (count945 q) 1 (meaningNeg87 q) (meaning945 q) hs
  change (! (valuationOf q 87)) = false ∨ valuationOf q 945 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1157 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 945 = true := counterClause1157 (baseVal q)

theorem counterClause1158 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 88 = true ∨ valuationOf q 946 = true := by
  have hs : count945 q = (countLit q [-87]) + (countLit q [-88]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-88])
  have hm := merge_two (literal (valuationOf q) (-87)) (literal (valuationOf q) (-88)) (literal (valuationOf q) (946)) (countLit q [-87]) (countLit q [-88]) (count945 q) 1 1 (meaningNeg87 q) (meaningNeg88 q) (meaning946 q) hs
  change (! (valuationOf q 87)) = false ∨ (! (valuationOf q 88)) = false ∨ valuationOf q 946 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1158 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 88 = true ∨ valuation q 946 = true := counterClause1158 (baseVal q)

theorem counterClause1159 (q : Nat → Bool) : valuationOf q 945 = false ∨ valuationOf q 947 = true := by
  have hs : count947 q = (countLit q [-84, -85]) + (countLit q [-87, -88]) := List.countP_append (p := literal q) (l₁ := [-84, -85]) (l₂ := [-87, -88])
  have hm := merge_right (literal (valuationOf q) (945)) (literal (valuationOf q) (947)) (countLit q [-84, -85]) (countLit q [-87, -88]) (count947 q) 1 (meaning945 q) (meaning947 q) hs
  change valuationOf q 945 = false ∨ valuationOf q 947 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1159 (q : Snake 81) (h : Conditions q) : valuation q 945 = false ∨ valuation q 947 = true := counterClause1159 (baseVal q)

theorem counterClause1160 (q : Nat → Bool) : valuationOf q 946 = false ∨ valuationOf q 948 = true := by
  have hs : count947 q = (countLit q [-84, -85]) + (countLit q [-87, -88]) := List.countP_append (p := literal q) (l₁ := [-84, -85]) (l₂ := [-87, -88])
  have hm := merge_right (literal (valuationOf q) (946)) (literal (valuationOf q) (948)) (countLit q [-84, -85]) (countLit q [-87, -88]) (count947 q) 2 (meaning946 q) (meaning948 q) hs
  change valuationOf q 946 = false ∨ valuationOf q 948 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1160 (q : Snake 81) (h : Conditions q) : valuation q 946 = false ∨ valuation q 948 = true := counterClause1160 (baseVal q)

theorem counterClause1161 (q : Nat → Bool) : valuationOf q 943 = false ∨ valuationOf q 947 = true := by
  have hs : count947 q = (countLit q [-84, -85]) + (countLit q [-87, -88]) := List.countP_append (p := literal q) (l₁ := [-84, -85]) (l₂ := [-87, -88])
  have hm := merge_left (literal (valuationOf q) (943)) (literal (valuationOf q) (947)) (countLit q [-84, -85]) (countLit q [-87, -88]) (count947 q) 1 (meaning943 q) (meaning947 q) hs
  change valuationOf q 943 = false ∨ valuationOf q 947 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1161 (q : Snake 81) (h : Conditions q) : valuation q 943 = false ∨ valuation q 947 = true := counterClause1161 (baseVal q)

theorem counterClause1162 (q : Nat → Bool) : valuationOf q 943 = false ∨ valuationOf q 945 = false ∨ valuationOf q 948 = true := by
  have hs : count947 q = (countLit q [-84, -85]) + (countLit q [-87, -88]) := List.countP_append (p := literal q) (l₁ := [-84, -85]) (l₂ := [-87, -88])
  have hm := merge_two (literal (valuationOf q) (943)) (literal (valuationOf q) (945)) (literal (valuationOf q) (948)) (countLit q [-84, -85]) (countLit q [-87, -88]) (count947 q) 1 1 (meaning943 q) (meaning945 q) (meaning948 q) hs
  change valuationOf q 943 = false ∨ valuationOf q 945 = false ∨ valuationOf q 948 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1162 (q : Snake 81) (h : Conditions q) : valuation q 943 = false ∨ valuation q 945 = false ∨ valuation q 948 = true := counterClause1162 (baseVal q)

theorem counterClause1163 (q : Nat → Bool) : valuationOf q 943 = false ∨ valuationOf q 946 = false ∨ valuationOf q 949 = true := by
  have hs : count947 q = (countLit q [-84, -85]) + (countLit q [-87, -88]) := List.countP_append (p := literal q) (l₁ := [-84, -85]) (l₂ := [-87, -88])
  have hm := merge_two (literal (valuationOf q) (943)) (literal (valuationOf q) (946)) (literal (valuationOf q) (949)) (countLit q [-84, -85]) (countLit q [-87, -88]) (count947 q) 1 2 (meaning943 q) (meaning946 q) (meaning949 q) hs
  change valuationOf q 943 = false ∨ valuationOf q 946 = false ∨ valuationOf q 949 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1163 (q : Snake 81) (h : Conditions q) : valuation q 943 = false ∨ valuation q 946 = false ∨ valuation q 949 = true := counterClause1163 (baseVal q)

theorem counterClause1164 (q : Nat → Bool) : valuationOf q 944 = false ∨ valuationOf q 948 = true := by
  have hs : count947 q = (countLit q [-84, -85]) + (countLit q [-87, -88]) := List.countP_append (p := literal q) (l₁ := [-84, -85]) (l₂ := [-87, -88])
  have hm := merge_left (literal (valuationOf q) (944)) (literal (valuationOf q) (948)) (countLit q [-84, -85]) (countLit q [-87, -88]) (count947 q) 2 (meaning944 q) (meaning948 q) hs
  change valuationOf q 944 = false ∨ valuationOf q 948 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1164 (q : Snake 81) (h : Conditions q) : valuation q 944 = false ∨ valuation q 948 = true := counterClause1164 (baseVal q)

theorem counterClause1165 (q : Nat → Bool) : valuationOf q 944 = false ∨ valuationOf q 945 = false ∨ valuationOf q 949 = true := by
  have hs : count947 q = (countLit q [-84, -85]) + (countLit q [-87, -88]) := List.countP_append (p := literal q) (l₁ := [-84, -85]) (l₂ := [-87, -88])
  have hm := merge_two (literal (valuationOf q) (944)) (literal (valuationOf q) (945)) (literal (valuationOf q) (949)) (countLit q [-84, -85]) (countLit q [-87, -88]) (count947 q) 2 1 (meaning944 q) (meaning945 q) (meaning949 q) hs
  change valuationOf q 944 = false ∨ valuationOf q 945 = false ∨ valuationOf q 949 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1165 (q : Snake 81) (h : Conditions q) : valuation q 944 = false ∨ valuation q 945 = false ∨ valuation q 949 = true := counterClause1165 (baseVal q)

theorem counterClause1166 (q : Nat → Bool) : valuationOf q 944 = false ∨ valuationOf q 946 = false ∨ valuationOf q 950 = true := by
  have hs : count947 q = (countLit q [-84, -85]) + (countLit q [-87, -88]) := List.countP_append (p := literal q) (l₁ := [-84, -85]) (l₂ := [-87, -88])
  have hm := merge_two (literal (valuationOf q) (944)) (literal (valuationOf q) (946)) (literal (valuationOf q) (950)) (countLit q [-84, -85]) (countLit q [-87, -88]) (count947 q) 2 2 (meaning944 q) (meaning946 q) (meaning950 q) hs
  change valuationOf q 944 = false ∨ valuationOf q 946 = false ∨ valuationOf q 950 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1166 (q : Snake 81) (h : Conditions q) : valuation q 944 = false ∨ valuation q 946 = false ∨ valuation q 950 = true := counterClause1166 (baseVal q)

theorem counterClause1167 (q : Nat → Bool) : valuationOf q 947 = false ∨ valuationOf q 951 = true := by
  have hs : count951 q = (countLit q [-75, -78, -82]) + (countLit q [-84, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-75, -78, -82]) (l₂ := [-84, -85, -87, -88])
  have hm := merge_right (literal (valuationOf q) (947)) (literal (valuationOf q) (951)) (countLit q [-75, -78, -82]) (countLit q [-84, -85, -87, -88]) (count951 q) 1 (meaning947 q) (meaning951 q) hs
  change valuationOf q 947 = false ∨ valuationOf q 951 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1167 (q : Snake 81) (h : Conditions q) : valuation q 947 = false ∨ valuation q 951 = true := counterClause1167 (baseVal q)

theorem counterClause1168 (q : Nat → Bool) : valuationOf q 948 = false ∨ valuationOf q 952 = true := by
  have hs : count951 q = (countLit q [-75, -78, -82]) + (countLit q [-84, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-75, -78, -82]) (l₂ := [-84, -85, -87, -88])
  have hm := merge_right (literal (valuationOf q) (948)) (literal (valuationOf q) (952)) (countLit q [-75, -78, -82]) (countLit q [-84, -85, -87, -88]) (count951 q) 2 (meaning948 q) (meaning952 q) hs
  change valuationOf q 948 = false ∨ valuationOf q 952 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1168 (q : Snake 81) (h : Conditions q) : valuation q 948 = false ∨ valuation q 952 = true := counterClause1168 (baseVal q)

theorem counterClause1169 (q : Nat → Bool) : valuationOf q 949 = false ∨ valuationOf q 953 = true := by
  have hs : count951 q = (countLit q [-75, -78, -82]) + (countLit q [-84, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-75, -78, -82]) (l₂ := [-84, -85, -87, -88])
  have hm := merge_right (literal (valuationOf q) (949)) (literal (valuationOf q) (953)) (countLit q [-75, -78, -82]) (countLit q [-84, -85, -87, -88]) (count951 q) 3 (meaning949 q) (meaning953 q) hs
  change valuationOf q 949 = false ∨ valuationOf q 953 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1169 (q : Snake 81) (h : Conditions q) : valuation q 949 = false ∨ valuation q 953 = true := counterClause1169 (baseVal q)

theorem counterClause1170 (q : Nat → Bool) : valuationOf q 950 = false ∨ valuationOf q 954 = true := by
  have hs : count951 q = (countLit q [-75, -78, -82]) + (countLit q [-84, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-75, -78, -82]) (l₂ := [-84, -85, -87, -88])
  have hm := merge_right (literal (valuationOf q) (950)) (literal (valuationOf q) (954)) (countLit q [-75, -78, -82]) (countLit q [-84, -85, -87, -88]) (count951 q) 4 (meaning950 q) (meaning954 q) hs
  change valuationOf q 950 = false ∨ valuationOf q 954 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1170 (q : Snake 81) (h : Conditions q) : valuation q 950 = false ∨ valuation q 954 = true := counterClause1170 (baseVal q)

theorem counterClause1171 (q : Nat → Bool) : valuationOf q 940 = false ∨ valuationOf q 951 = true := by
  have hs : count951 q = (countLit q [-75, -78, -82]) + (countLit q [-84, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-75, -78, -82]) (l₂ := [-84, -85, -87, -88])
  have hm := merge_left (literal (valuationOf q) (940)) (literal (valuationOf q) (951)) (countLit q [-75, -78, -82]) (countLit q [-84, -85, -87, -88]) (count951 q) 1 (meaning940 q) (meaning951 q) hs
  change valuationOf q 940 = false ∨ valuationOf q 951 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1171 (q : Snake 81) (h : Conditions q) : valuation q 940 = false ∨ valuation q 951 = true := counterClause1171 (baseVal q)

theorem counterClause1172 (q : Nat → Bool) : valuationOf q 940 = false ∨ valuationOf q 947 = false ∨ valuationOf q 952 = true := by
  have hs : count951 q = (countLit q [-75, -78, -82]) + (countLit q [-84, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-75, -78, -82]) (l₂ := [-84, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (940)) (literal (valuationOf q) (947)) (literal (valuationOf q) (952)) (countLit q [-75, -78, -82]) (countLit q [-84, -85, -87, -88]) (count951 q) 1 1 (meaning940 q) (meaning947 q) (meaning952 q) hs
  change valuationOf q 940 = false ∨ valuationOf q 947 = false ∨ valuationOf q 952 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1172 (q : Snake 81) (h : Conditions q) : valuation q 940 = false ∨ valuation q 947 = false ∨ valuation q 952 = true := counterClause1172 (baseVal q)

theorem counterClause1173 (q : Nat → Bool) : valuationOf q 940 = false ∨ valuationOf q 948 = false ∨ valuationOf q 953 = true := by
  have hs : count951 q = (countLit q [-75, -78, -82]) + (countLit q [-84, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-75, -78, -82]) (l₂ := [-84, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (940)) (literal (valuationOf q) (948)) (literal (valuationOf q) (953)) (countLit q [-75, -78, -82]) (countLit q [-84, -85, -87, -88]) (count951 q) 1 2 (meaning940 q) (meaning948 q) (meaning953 q) hs
  change valuationOf q 940 = false ∨ valuationOf q 948 = false ∨ valuationOf q 953 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1173 (q : Snake 81) (h : Conditions q) : valuation q 940 = false ∨ valuation q 948 = false ∨ valuation q 953 = true := counterClause1173 (baseVal q)

theorem counterClause1174 (q : Nat → Bool) : valuationOf q 940 = false ∨ valuationOf q 949 = false ∨ valuationOf q 954 = true := by
  have hs : count951 q = (countLit q [-75, -78, -82]) + (countLit q [-84, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-75, -78, -82]) (l₂ := [-84, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (940)) (literal (valuationOf q) (949)) (literal (valuationOf q) (954)) (countLit q [-75, -78, -82]) (countLit q [-84, -85, -87, -88]) (count951 q) 1 3 (meaning940 q) (meaning949 q) (meaning954 q) hs
  change valuationOf q 940 = false ∨ valuationOf q 949 = false ∨ valuationOf q 954 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1174 (q : Snake 81) (h : Conditions q) : valuation q 940 = false ∨ valuation q 949 = false ∨ valuation q 954 = true := counterClause1174 (baseVal q)

theorem counterClause1175 (q : Nat → Bool) : valuationOf q 940 = false ∨ valuationOf q 950 = false ∨ valuationOf q 955 = true := by
  have hs : count951 q = (countLit q [-75, -78, -82]) + (countLit q [-84, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-75, -78, -82]) (l₂ := [-84, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (940)) (literal (valuationOf q) (950)) (literal (valuationOf q) (955)) (countLit q [-75, -78, -82]) (countLit q [-84, -85, -87, -88]) (count951 q) 1 4 (meaning940 q) (meaning950 q) (meaning955 q) hs
  change valuationOf q 940 = false ∨ valuationOf q 950 = false ∨ valuationOf q 955 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1175 (q : Snake 81) (h : Conditions q) : valuation q 940 = false ∨ valuation q 950 = false ∨ valuation q 955 = true := counterClause1175 (baseVal q)

theorem counterClause1176 (q : Nat → Bool) : valuationOf q 941 = false ∨ valuationOf q 952 = true := by
  have hs : count951 q = (countLit q [-75, -78, -82]) + (countLit q [-84, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-75, -78, -82]) (l₂ := [-84, -85, -87, -88])
  have hm := merge_left (literal (valuationOf q) (941)) (literal (valuationOf q) (952)) (countLit q [-75, -78, -82]) (countLit q [-84, -85, -87, -88]) (count951 q) 2 (meaning941 q) (meaning952 q) hs
  change valuationOf q 941 = false ∨ valuationOf q 952 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1176 (q : Snake 81) (h : Conditions q) : valuation q 941 = false ∨ valuation q 952 = true := counterClause1176 (baseVal q)

theorem counterClause1177 (q : Nat → Bool) : valuationOf q 941 = false ∨ valuationOf q 947 = false ∨ valuationOf q 953 = true := by
  have hs : count951 q = (countLit q [-75, -78, -82]) + (countLit q [-84, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-75, -78, -82]) (l₂ := [-84, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (941)) (literal (valuationOf q) (947)) (literal (valuationOf q) (953)) (countLit q [-75, -78, -82]) (countLit q [-84, -85, -87, -88]) (count951 q) 2 1 (meaning941 q) (meaning947 q) (meaning953 q) hs
  change valuationOf q 941 = false ∨ valuationOf q 947 = false ∨ valuationOf q 953 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1177 (q : Snake 81) (h : Conditions q) : valuation q 941 = false ∨ valuation q 947 = false ∨ valuation q 953 = true := counterClause1177 (baseVal q)

theorem counterClause1178 (q : Nat → Bool) : valuationOf q 941 = false ∨ valuationOf q 948 = false ∨ valuationOf q 954 = true := by
  have hs : count951 q = (countLit q [-75, -78, -82]) + (countLit q [-84, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-75, -78, -82]) (l₂ := [-84, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (941)) (literal (valuationOf q) (948)) (literal (valuationOf q) (954)) (countLit q [-75, -78, -82]) (countLit q [-84, -85, -87, -88]) (count951 q) 2 2 (meaning941 q) (meaning948 q) (meaning954 q) hs
  change valuationOf q 941 = false ∨ valuationOf q 948 = false ∨ valuationOf q 954 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1178 (q : Snake 81) (h : Conditions q) : valuation q 941 = false ∨ valuation q 948 = false ∨ valuation q 954 = true := counterClause1178 (baseVal q)

theorem counterClause1179 (q : Nat → Bool) : valuationOf q 941 = false ∨ valuationOf q 949 = false ∨ valuationOf q 955 = true := by
  have hs : count951 q = (countLit q [-75, -78, -82]) + (countLit q [-84, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-75, -78, -82]) (l₂ := [-84, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (941)) (literal (valuationOf q) (949)) (literal (valuationOf q) (955)) (countLit q [-75, -78, -82]) (countLit q [-84, -85, -87, -88]) (count951 q) 2 3 (meaning941 q) (meaning949 q) (meaning955 q) hs
  change valuationOf q 941 = false ∨ valuationOf q 949 = false ∨ valuationOf q 955 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1179 (q : Snake 81) (h : Conditions q) : valuation q 941 = false ∨ valuation q 949 = false ∨ valuation q 955 = true := counterClause1179 (baseVal q)

theorem counterClause1180 (q : Nat → Bool) : valuationOf q 941 = false ∨ valuationOf q 950 = false ∨ valuationOf q 956 = true := by
  have hs : count951 q = (countLit q [-75, -78, -82]) + (countLit q [-84, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-75, -78, -82]) (l₂ := [-84, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (941)) (literal (valuationOf q) (950)) (literal (valuationOf q) (956)) (countLit q [-75, -78, -82]) (countLit q [-84, -85, -87, -88]) (count951 q) 2 4 (meaning941 q) (meaning950 q) (meaning956 q) hs
  change valuationOf q 941 = false ∨ valuationOf q 950 = false ∨ valuationOf q 956 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1180 (q : Snake 81) (h : Conditions q) : valuation q 941 = false ∨ valuation q 950 = false ∨ valuation q 956 = true := counterClause1180 (baseVal q)

theorem counterClause1181 (q : Nat → Bool) : valuationOf q 942 = false ∨ valuationOf q 953 = true := by
  have hs : count951 q = (countLit q [-75, -78, -82]) + (countLit q [-84, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-75, -78, -82]) (l₂ := [-84, -85, -87, -88])
  have hm := merge_left (literal (valuationOf q) (942)) (literal (valuationOf q) (953)) (countLit q [-75, -78, -82]) (countLit q [-84, -85, -87, -88]) (count951 q) 3 (meaning942 q) (meaning953 q) hs
  change valuationOf q 942 = false ∨ valuationOf q 953 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1181 (q : Snake 81) (h : Conditions q) : valuation q 942 = false ∨ valuation q 953 = true := counterClause1181 (baseVal q)

theorem counterClause1182 (q : Nat → Bool) : valuationOf q 942 = false ∨ valuationOf q 947 = false ∨ valuationOf q 954 = true := by
  have hs : count951 q = (countLit q [-75, -78, -82]) + (countLit q [-84, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-75, -78, -82]) (l₂ := [-84, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (942)) (literal (valuationOf q) (947)) (literal (valuationOf q) (954)) (countLit q [-75, -78, -82]) (countLit q [-84, -85, -87, -88]) (count951 q) 3 1 (meaning942 q) (meaning947 q) (meaning954 q) hs
  change valuationOf q 942 = false ∨ valuationOf q 947 = false ∨ valuationOf q 954 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1182 (q : Snake 81) (h : Conditions q) : valuation q 942 = false ∨ valuation q 947 = false ∨ valuation q 954 = true := counterClause1182 (baseVal q)

theorem counterClause1183 (q : Nat → Bool) : valuationOf q 942 = false ∨ valuationOf q 948 = false ∨ valuationOf q 955 = true := by
  have hs : count951 q = (countLit q [-75, -78, -82]) + (countLit q [-84, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-75, -78, -82]) (l₂ := [-84, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (942)) (literal (valuationOf q) (948)) (literal (valuationOf q) (955)) (countLit q [-75, -78, -82]) (countLit q [-84, -85, -87, -88]) (count951 q) 3 2 (meaning942 q) (meaning948 q) (meaning955 q) hs
  change valuationOf q 942 = false ∨ valuationOf q 948 = false ∨ valuationOf q 955 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1183 (q : Snake 81) (h : Conditions q) : valuation q 942 = false ∨ valuation q 948 = false ∨ valuation q 955 = true := counterClause1183 (baseVal q)

theorem counterClause1184 (q : Nat → Bool) : valuationOf q 942 = false ∨ valuationOf q 949 = false ∨ valuationOf q 956 = true := by
  have hs : count951 q = (countLit q [-75, -78, -82]) + (countLit q [-84, -85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-75, -78, -82]) (l₂ := [-84, -85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (942)) (literal (valuationOf q) (949)) (literal (valuationOf q) (956)) (countLit q [-75, -78, -82]) (countLit q [-84, -85, -87, -88]) (count951 q) 3 3 (meaning942 q) (meaning949 q) (meaning956 q) hs
  change valuationOf q 942 = false ∨ valuationOf q 949 = false ∨ valuationOf q 956 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1184 (q : Snake 81) (h : Conditions q) : valuation q 942 = false ∨ valuation q 949 = false ∨ valuation q 956 = true := counterClause1184 (baseVal q)

theorem block36 (q : Snake 81) (h : Conditions q) : B112E259.Block36 (valuation q) :=
  ⟨clause1153 q h, clause1154 q h, clause1155 q h, clause1156 q h, clause1157 q h, clause1158 q h, clause1159 q h, clause1160 q h, clause1161 q h, clause1162 q h, clause1163 q h, clause1164 q h, clause1165 q h, clause1166 q h, clause1167 q h, clause1168 q h, clause1169 q h, clause1170 q h, clause1171 q h, clause1172 q h, clause1173 q h, clause1174 q h, clause1175 q h, clause1176 q h, clause1177 q h, clause1178 q h, clause1179 q h, clause1180 q h, clause1181 q h, clause1182 q h, clause1183 q h, clause1184 q h⟩

end
end Snake9.Regrowth.E112259
