import E112152Semantics
import B112E152Inputs
namespace Snake9.Regrowth.E112152
noncomputable section
local instance blockDec26 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause833 (q : Nat → Bool) : valuationOf q 117 = true ∨ valuationOf q 1678 = true := by
  have hs : count1678 q = (countLit q [-117]) + (countLit q [-120]) := List.countP_append (p := literal q) (l₁ := [-117]) (l₂ := [-120])
  have hm := merge_left (literal (valuationOf q) (-117)) (literal (valuationOf q) (1678)) (countLit q [-117]) (countLit q [-120]) (count1678 q) 1 (meaningNeg117 q) (meaning1678 q) hs
  change (! (valuationOf q 117)) = false ∨ valuationOf q 1678 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause833 (q : Snake 81) (h : Conditions q) : valuation q 117 = true ∨ valuation q 1678 = true := counterClause833 (baseVal q)

theorem counterClause834 (q : Nat → Bool) : valuationOf q 117 = true ∨ valuationOf q 120 = true ∨ valuationOf q 1679 = true := by
  have hs : count1678 q = (countLit q [-117]) + (countLit q [-120]) := List.countP_append (p := literal q) (l₁ := [-117]) (l₂ := [-120])
  have hm := merge_two (literal (valuationOf q) (-117)) (literal (valuationOf q) (-120)) (literal (valuationOf q) (1679)) (countLit q [-117]) (countLit q [-120]) (count1678 q) 1 1 (meaningNeg117 q) (meaningNeg120 q) (meaning1679 q) hs
  change (! (valuationOf q 117)) = false ∨ (! (valuationOf q 120)) = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause834 (q : Snake 81) (h : Conditions q) : valuation q 117 = true ∨ valuation q 120 = true ∨ valuation q 1679 = true := counterClause834 (baseVal q)

theorem counterClause835 (q : Nat → Bool) : valuationOf q 1678 = false ∨ valuationOf q 1680 = true := by
  have hs : count1680 q = (countLit q [-114, -116]) + (countLit q [-117, -120]) := List.countP_append (p := literal q) (l₁ := [-114, -116]) (l₂ := [-117, -120])
  have hm := merge_right (literal (valuationOf q) (1678)) (literal (valuationOf q) (1680)) (countLit q [-114, -116]) (countLit q [-117, -120]) (count1680 q) 1 (meaning1678 q) (meaning1680 q) hs
  change valuationOf q 1678 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause835 (q : Snake 81) (h : Conditions q) : valuation q 1678 = false ∨ valuation q 1680 = true := counterClause835 (baseVal q)

theorem counterClause836 (q : Nat → Bool) : valuationOf q 1679 = false ∨ valuationOf q 1681 = true := by
  have hs : count1680 q = (countLit q [-114, -116]) + (countLit q [-117, -120]) := List.countP_append (p := literal q) (l₁ := [-114, -116]) (l₂ := [-117, -120])
  have hm := merge_right (literal (valuationOf q) (1679)) (literal (valuationOf q) (1681)) (countLit q [-114, -116]) (countLit q [-117, -120]) (count1680 q) 2 (meaning1679 q) (meaning1681 q) hs
  change valuationOf q 1679 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause836 (q : Snake 81) (h : Conditions q) : valuation q 1679 = false ∨ valuation q 1681 = true := counterClause836 (baseVal q)

theorem counterClause837 (q : Nat → Bool) : valuationOf q 1676 = false ∨ valuationOf q 1680 = true := by
  have hs : count1680 q = (countLit q [-114, -116]) + (countLit q [-117, -120]) := List.countP_append (p := literal q) (l₁ := [-114, -116]) (l₂ := [-117, -120])
  have hm := merge_left (literal (valuationOf q) (1676)) (literal (valuationOf q) (1680)) (countLit q [-114, -116]) (countLit q [-117, -120]) (count1680 q) 1 (meaning1676 q) (meaning1680 q) hs
  change valuationOf q 1676 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause837 (q : Snake 81) (h : Conditions q) : valuation q 1676 = false ∨ valuation q 1680 = true := counterClause837 (baseVal q)

theorem counterClause838 (q : Nat → Bool) : valuationOf q 1676 = false ∨ valuationOf q 1678 = false ∨ valuationOf q 1681 = true := by
  have hs : count1680 q = (countLit q [-114, -116]) + (countLit q [-117, -120]) := List.countP_append (p := literal q) (l₁ := [-114, -116]) (l₂ := [-117, -120])
  have hm := merge_two (literal (valuationOf q) (1676)) (literal (valuationOf q) (1678)) (literal (valuationOf q) (1681)) (countLit q [-114, -116]) (countLit q [-117, -120]) (count1680 q) 1 1 (meaning1676 q) (meaning1678 q) (meaning1681 q) hs
  change valuationOf q 1676 = false ∨ valuationOf q 1678 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause838 (q : Snake 81) (h : Conditions q) : valuation q 1676 = false ∨ valuation q 1678 = false ∨ valuation q 1681 = true := counterClause838 (baseVal q)

theorem counterClause839 (q : Nat → Bool) : valuationOf q 1676 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1682 = true := by
  have hs : count1680 q = (countLit q [-114, -116]) + (countLit q [-117, -120]) := List.countP_append (p := literal q) (l₁ := [-114, -116]) (l₂ := [-117, -120])
  have hm := merge_two (literal (valuationOf q) (1676)) (literal (valuationOf q) (1679)) (literal (valuationOf q) (1682)) (countLit q [-114, -116]) (countLit q [-117, -120]) (count1680 q) 1 2 (meaning1676 q) (meaning1679 q) (meaning1682 q) hs
  change valuationOf q 1676 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause839 (q : Snake 81) (h : Conditions q) : valuation q 1676 = false ∨ valuation q 1679 = false ∨ valuation q 1682 = true := counterClause839 (baseVal q)

theorem counterClause840 (q : Nat → Bool) : valuationOf q 1677 = false ∨ valuationOf q 1681 = true := by
  have hs : count1680 q = (countLit q [-114, -116]) + (countLit q [-117, -120]) := List.countP_append (p := literal q) (l₁ := [-114, -116]) (l₂ := [-117, -120])
  have hm := merge_left (literal (valuationOf q) (1677)) (literal (valuationOf q) (1681)) (countLit q [-114, -116]) (countLit q [-117, -120]) (count1680 q) 2 (meaning1677 q) (meaning1681 q) hs
  change valuationOf q 1677 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause840 (q : Snake 81) (h : Conditions q) : valuation q 1677 = false ∨ valuation q 1681 = true := counterClause840 (baseVal q)

theorem counterClause841 (q : Nat → Bool) : valuationOf q 1677 = false ∨ valuationOf q 1678 = false ∨ valuationOf q 1682 = true := by
  have hs : count1680 q = (countLit q [-114, -116]) + (countLit q [-117, -120]) := List.countP_append (p := literal q) (l₁ := [-114, -116]) (l₂ := [-117, -120])
  have hm := merge_two (literal (valuationOf q) (1677)) (literal (valuationOf q) (1678)) (literal (valuationOf q) (1682)) (countLit q [-114, -116]) (countLit q [-117, -120]) (count1680 q) 2 1 (meaning1677 q) (meaning1678 q) (meaning1682 q) hs
  change valuationOf q 1677 = false ∨ valuationOf q 1678 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause841 (q : Snake 81) (h : Conditions q) : valuation q 1677 = false ∨ valuation q 1678 = false ∨ valuation q 1682 = true := counterClause841 (baseVal q)

theorem counterClause842 (q : Nat → Bool) : valuationOf q 1677 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1683 = true := by
  have hs : count1680 q = (countLit q [-114, -116]) + (countLit q [-117, -120]) := List.countP_append (p := literal q) (l₁ := [-114, -116]) (l₂ := [-117, -120])
  have hm := merge_two (literal (valuationOf q) (1677)) (literal (valuationOf q) (1679)) (literal (valuationOf q) (1683)) (countLit q [-114, -116]) (countLit q [-117, -120]) (count1680 q) 2 2 (meaning1677 q) (meaning1679 q) (meaning1683 q) hs
  change valuationOf q 1677 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause842 (q : Snake 81) (h : Conditions q) : valuation q 1677 = false ∨ valuation q 1679 = false ∨ valuation q 1683 = true := counterClause842 (baseVal q)

theorem counterClause843 (q : Nat → Bool) : valuationOf q 1680 = false ∨ valuationOf q 1684 = true := by
  have hs : count1684 q = (countLit q [-107, -108, -112, -113]) + (countLit q [-114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-107, -108, -112, -113]) (l₂ := [-114, -116, -117, -120])
  have hm := merge_right (literal (valuationOf q) (1680)) (literal (valuationOf q) (1684)) (countLit q [-107, -108, -112, -113]) (countLit q [-114, -116, -117, -120]) (count1684 q) 1 (meaning1680 q) (meaning1684 q) hs
  change valuationOf q 1680 = false ∨ valuationOf q 1684 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause843 (q : Snake 81) (h : Conditions q) : valuation q 1680 = false ∨ valuation q 1684 = true := counterClause843 (baseVal q)

theorem counterClause844 (q : Nat → Bool) : valuationOf q 1681 = false ∨ valuationOf q 1685 = true := by
  have hs : count1684 q = (countLit q [-107, -108, -112, -113]) + (countLit q [-114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-107, -108, -112, -113]) (l₂ := [-114, -116, -117, -120])
  have hm := merge_right (literal (valuationOf q) (1681)) (literal (valuationOf q) (1685)) (countLit q [-107, -108, -112, -113]) (countLit q [-114, -116, -117, -120]) (count1684 q) 2 (meaning1681 q) (meaning1685 q) hs
  change valuationOf q 1681 = false ∨ valuationOf q 1685 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause844 (q : Snake 81) (h : Conditions q) : valuation q 1681 = false ∨ valuation q 1685 = true := counterClause844 (baseVal q)

theorem counterClause845 (q : Nat → Bool) : valuationOf q 1682 = false ∨ valuationOf q 1686 = true := by
  have hs : count1684 q = (countLit q [-107, -108, -112, -113]) + (countLit q [-114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-107, -108, -112, -113]) (l₂ := [-114, -116, -117, -120])
  have hm := merge_right (literal (valuationOf q) (1682)) (literal (valuationOf q) (1686)) (countLit q [-107, -108, -112, -113]) (countLit q [-114, -116, -117, -120]) (count1684 q) 3 (meaning1682 q) (meaning1686 q) hs
  change valuationOf q 1682 = false ∨ valuationOf q 1686 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause845 (q : Snake 81) (h : Conditions q) : valuation q 1682 = false ∨ valuation q 1686 = true := counterClause845 (baseVal q)

theorem counterClause846 (q : Nat → Bool) : valuationOf q 1683 = false ∨ valuationOf q 1687 = true := by
  have hs : count1684 q = (countLit q [-107, -108, -112, -113]) + (countLit q [-114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-107, -108, -112, -113]) (l₂ := [-114, -116, -117, -120])
  have hm := merge_right (literal (valuationOf q) (1683)) (literal (valuationOf q) (1687)) (countLit q [-107, -108, -112, -113]) (countLit q [-114, -116, -117, -120]) (count1684 q) 4 (meaning1683 q) (meaning1687 q) hs
  change valuationOf q 1683 = false ∨ valuationOf q 1687 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause846 (q : Snake 81) (h : Conditions q) : valuation q 1683 = false ∨ valuation q 1687 = true := counterClause846 (baseVal q)

theorem counterClause847 (q : Nat → Bool) : valuationOf q 1672 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1685 = true := by
  have hs : count1684 q = (countLit q [-107, -108, -112, -113]) + (countLit q [-114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-107, -108, -112, -113]) (l₂ := [-114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1672)) (literal (valuationOf q) (1680)) (literal (valuationOf q) (1685)) (countLit q [-107, -108, -112, -113]) (countLit q [-114, -116, -117, -120]) (count1684 q) 1 1 (meaning1672 q) (meaning1680 q) (meaning1685 q) hs
  change valuationOf q 1672 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1685 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause847 (q : Snake 81) (h : Conditions q) : valuation q 1672 = false ∨ valuation q 1680 = false ∨ valuation q 1685 = true := counterClause847 (baseVal q)

theorem counterClause848 (q : Nat → Bool) : valuationOf q 1672 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1686 = true := by
  have hs : count1684 q = (countLit q [-107, -108, -112, -113]) + (countLit q [-114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-107, -108, -112, -113]) (l₂ := [-114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1672)) (literal (valuationOf q) (1681)) (literal (valuationOf q) (1686)) (countLit q [-107, -108, -112, -113]) (countLit q [-114, -116, -117, -120]) (count1684 q) 1 2 (meaning1672 q) (meaning1681 q) (meaning1686 q) hs
  change valuationOf q 1672 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1686 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause848 (q : Snake 81) (h : Conditions q) : valuation q 1672 = false ∨ valuation q 1681 = false ∨ valuation q 1686 = true := counterClause848 (baseVal q)

theorem counterClause849 (q : Nat → Bool) : valuationOf q 1672 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1687 = true := by
  have hs : count1684 q = (countLit q [-107, -108, -112, -113]) + (countLit q [-114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-107, -108, -112, -113]) (l₂ := [-114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1672)) (literal (valuationOf q) (1682)) (literal (valuationOf q) (1687)) (countLit q [-107, -108, -112, -113]) (countLit q [-114, -116, -117, -120]) (count1684 q) 1 3 (meaning1672 q) (meaning1682 q) (meaning1687 q) hs
  change valuationOf q 1672 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1687 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause849 (q : Snake 81) (h : Conditions q) : valuation q 1672 = false ∨ valuation q 1682 = false ∨ valuation q 1687 = true := counterClause849 (baseVal q)

theorem counterClause850 (q : Nat → Bool) : valuationOf q 1673 = false ∨ valuationOf q 1685 = true := by
  have hs : count1684 q = (countLit q [-107, -108, -112, -113]) + (countLit q [-114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-107, -108, -112, -113]) (l₂ := [-114, -116, -117, -120])
  have hm := merge_left (literal (valuationOf q) (1673)) (literal (valuationOf q) (1685)) (countLit q [-107, -108, -112, -113]) (countLit q [-114, -116, -117, -120]) (count1684 q) 2 (meaning1673 q) (meaning1685 q) hs
  change valuationOf q 1673 = false ∨ valuationOf q 1685 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause850 (q : Snake 81) (h : Conditions q) : valuation q 1673 = false ∨ valuation q 1685 = true := counterClause850 (baseVal q)

theorem counterClause851 (q : Nat → Bool) : valuationOf q 1673 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1686 = true := by
  have hs : count1684 q = (countLit q [-107, -108, -112, -113]) + (countLit q [-114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-107, -108, -112, -113]) (l₂ := [-114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1673)) (literal (valuationOf q) (1680)) (literal (valuationOf q) (1686)) (countLit q [-107, -108, -112, -113]) (countLit q [-114, -116, -117, -120]) (count1684 q) 2 1 (meaning1673 q) (meaning1680 q) (meaning1686 q) hs
  change valuationOf q 1673 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1686 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause851 (q : Snake 81) (h : Conditions q) : valuation q 1673 = false ∨ valuation q 1680 = false ∨ valuation q 1686 = true := counterClause851 (baseVal q)

theorem counterClause852 (q : Nat → Bool) : valuationOf q 1673 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1687 = true := by
  have hs : count1684 q = (countLit q [-107, -108, -112, -113]) + (countLit q [-114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-107, -108, -112, -113]) (l₂ := [-114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1673)) (literal (valuationOf q) (1681)) (literal (valuationOf q) (1687)) (countLit q [-107, -108, -112, -113]) (countLit q [-114, -116, -117, -120]) (count1684 q) 2 2 (meaning1673 q) (meaning1681 q) (meaning1687 q) hs
  change valuationOf q 1673 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1687 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause852 (q : Snake 81) (h : Conditions q) : valuation q 1673 = false ∨ valuation q 1681 = false ∨ valuation q 1687 = true := counterClause852 (baseVal q)

theorem counterClause853 (q : Nat → Bool) : valuationOf q 1673 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1688 = true := by
  have hs : count1684 q = (countLit q [-107, -108, -112, -113]) + (countLit q [-114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-107, -108, -112, -113]) (l₂ := [-114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1673)) (literal (valuationOf q) (1682)) (literal (valuationOf q) (1688)) (countLit q [-107, -108, -112, -113]) (countLit q [-114, -116, -117, -120]) (count1684 q) 2 3 (meaning1673 q) (meaning1682 q) (meaning1688 q) hs
  change valuationOf q 1673 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1688 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause853 (q : Snake 81) (h : Conditions q) : valuation q 1673 = false ∨ valuation q 1682 = false ∨ valuation q 1688 = true := counterClause853 (baseVal q)

theorem counterClause854 (q : Nat → Bool) : valuationOf q 1674 = false ∨ valuationOf q 1686 = true := by
  have hs : count1684 q = (countLit q [-107, -108, -112, -113]) + (countLit q [-114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-107, -108, -112, -113]) (l₂ := [-114, -116, -117, -120])
  have hm := merge_left (literal (valuationOf q) (1674)) (literal (valuationOf q) (1686)) (countLit q [-107, -108, -112, -113]) (countLit q [-114, -116, -117, -120]) (count1684 q) 3 (meaning1674 q) (meaning1686 q) hs
  change valuationOf q 1674 = false ∨ valuationOf q 1686 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause854 (q : Snake 81) (h : Conditions q) : valuation q 1674 = false ∨ valuation q 1686 = true := counterClause854 (baseVal q)

theorem counterClause855 (q : Nat → Bool) : valuationOf q 1674 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1687 = true := by
  have hs : count1684 q = (countLit q [-107, -108, -112, -113]) + (countLit q [-114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-107, -108, -112, -113]) (l₂ := [-114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1674)) (literal (valuationOf q) (1680)) (literal (valuationOf q) (1687)) (countLit q [-107, -108, -112, -113]) (countLit q [-114, -116, -117, -120]) (count1684 q) 3 1 (meaning1674 q) (meaning1680 q) (meaning1687 q) hs
  change valuationOf q 1674 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1687 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause855 (q : Snake 81) (h : Conditions q) : valuation q 1674 = false ∨ valuation q 1680 = false ∨ valuation q 1687 = true := counterClause855 (baseVal q)

theorem counterClause856 (q : Nat → Bool) : valuationOf q 1674 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1688 = true := by
  have hs : count1684 q = (countLit q [-107, -108, -112, -113]) + (countLit q [-114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-107, -108, -112, -113]) (l₂ := [-114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1674)) (literal (valuationOf q) (1681)) (literal (valuationOf q) (1688)) (countLit q [-107, -108, -112, -113]) (countLit q [-114, -116, -117, -120]) (count1684 q) 3 2 (meaning1674 q) (meaning1681 q) (meaning1688 q) hs
  change valuationOf q 1674 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1688 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause856 (q : Snake 81) (h : Conditions q) : valuation q 1674 = false ∨ valuation q 1681 = false ∨ valuation q 1688 = true := counterClause856 (baseVal q)

theorem counterClause857 (q : Nat → Bool) : valuationOf q 1674 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1689 = true := by
  have hs : count1684 q = (countLit q [-107, -108, -112, -113]) + (countLit q [-114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-107, -108, -112, -113]) (l₂ := [-114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1674)) (literal (valuationOf q) (1682)) (literal (valuationOf q) (1689)) (countLit q [-107, -108, -112, -113]) (countLit q [-114, -116, -117, -120]) (count1684 q) 3 3 (meaning1674 q) (meaning1682 q) (meaning1689 q) hs
  change valuationOf q 1674 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1689 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause857 (q : Snake 81) (h : Conditions q) : valuation q 1674 = false ∨ valuation q 1682 = false ∨ valuation q 1689 = true := counterClause857 (baseVal q)

theorem counterClause858 (q : Nat → Bool) : valuationOf q 1674 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1690 = true := by
  have hs : count1684 q = (countLit q [-107, -108, -112, -113]) + (countLit q [-114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-107, -108, -112, -113]) (l₂ := [-114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1674)) (literal (valuationOf q) (1683)) (literal (valuationOf q) (1690)) (countLit q [-107, -108, -112, -113]) (countLit q [-114, -116, -117, -120]) (count1684 q) 3 4 (meaning1674 q) (meaning1683 q) (meaning1690 q) hs
  change valuationOf q 1674 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause858 (q : Snake 81) (h : Conditions q) : valuation q 1674 = false ∨ valuation q 1683 = false ∨ valuation q 1690 = true := counterClause858 (baseVal q)

theorem counterClause859 (q : Nat → Bool) : valuationOf q 1675 = false ∨ valuationOf q 1687 = true := by
  have hs : count1684 q = (countLit q [-107, -108, -112, -113]) + (countLit q [-114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-107, -108, -112, -113]) (l₂ := [-114, -116, -117, -120])
  have hm := merge_left (literal (valuationOf q) (1675)) (literal (valuationOf q) (1687)) (countLit q [-107, -108, -112, -113]) (countLit q [-114, -116, -117, -120]) (count1684 q) 4 (meaning1675 q) (meaning1687 q) hs
  change valuationOf q 1675 = false ∨ valuationOf q 1687 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause859 (q : Snake 81) (h : Conditions q) : valuation q 1675 = false ∨ valuation q 1687 = true := counterClause859 (baseVal q)

theorem counterClause860 (q : Nat → Bool) : valuationOf q 1675 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1688 = true := by
  have hs : count1684 q = (countLit q [-107, -108, -112, -113]) + (countLit q [-114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-107, -108, -112, -113]) (l₂ := [-114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1675)) (literal (valuationOf q) (1680)) (literal (valuationOf q) (1688)) (countLit q [-107, -108, -112, -113]) (countLit q [-114, -116, -117, -120]) (count1684 q) 4 1 (meaning1675 q) (meaning1680 q) (meaning1688 q) hs
  change valuationOf q 1675 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1688 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause860 (q : Snake 81) (h : Conditions q) : valuation q 1675 = false ∨ valuation q 1680 = false ∨ valuation q 1688 = true := counterClause860 (baseVal q)

theorem counterClause861 (q : Nat → Bool) : valuationOf q 1675 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1689 = true := by
  have hs : count1684 q = (countLit q [-107, -108, -112, -113]) + (countLit q [-114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-107, -108, -112, -113]) (l₂ := [-114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1675)) (literal (valuationOf q) (1681)) (literal (valuationOf q) (1689)) (countLit q [-107, -108, -112, -113]) (countLit q [-114, -116, -117, -120]) (count1684 q) 4 2 (meaning1675 q) (meaning1681 q) (meaning1689 q) hs
  change valuationOf q 1675 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1689 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause861 (q : Snake 81) (h : Conditions q) : valuation q 1675 = false ∨ valuation q 1681 = false ∨ valuation q 1689 = true := counterClause861 (baseVal q)

theorem counterClause862 (q : Nat → Bool) : valuationOf q 1675 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1690 = true := by
  have hs : count1684 q = (countLit q [-107, -108, -112, -113]) + (countLit q [-114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-107, -108, -112, -113]) (l₂ := [-114, -116, -117, -120])
  have hm := merge_two (literal (valuationOf q) (1675)) (literal (valuationOf q) (1682)) (literal (valuationOf q) (1690)) (countLit q [-107, -108, -112, -113]) (countLit q [-114, -116, -117, -120]) (count1684 q) 4 3 (meaning1675 q) (meaning1682 q) (meaning1690 q) hs
  change valuationOf q 1675 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause862 (q : Snake 81) (h : Conditions q) : valuation q 1675 = false ∨ valuation q 1682 = false ∨ valuation q 1690 = true := counterClause862 (baseVal q)

theorem counterClause863 (q : Nat → Bool) : valuationOf q 1687 = false ∨ valuationOf q 1695 = true := by
  have hs : count1692 q = (countLit q [-90, -91, -94, -96, -99, -100, -104]) + (countLit q [-107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -94, -96, -99, -100, -104]) (l₂ := [-107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_right (literal (valuationOf q) (1687)) (literal (valuationOf q) (1695)) (countLit q [-90, -91, -94, -96, -99, -100, -104]) (countLit q [-107, -108, -112, -113, -114, -116, -117, -120]) (count1692 q) 4 (meaning1687 q) (meaning1695 q) hs
  change valuationOf q 1687 = false ∨ valuationOf q 1695 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause863 (q : Snake 81) (h : Conditions q) : valuation q 1687 = false ∨ valuation q 1695 = true := counterClause863 (baseVal q)

theorem counterClause864 (q : Nat → Bool) : valuationOf q 1688 = false ∨ valuationOf q 1696 = true := by
  have hs : count1692 q = (countLit q [-90, -91, -94, -96, -99, -100, -104]) + (countLit q [-107, -108, -112, -113, -114, -116, -117, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -94, -96, -99, -100, -104]) (l₂ := [-107, -108, -112, -113, -114, -116, -117, -120])
  have hm := merge_right (literal (valuationOf q) (1688)) (literal (valuationOf q) (1696)) (countLit q [-90, -91, -94, -96, -99, -100, -104]) (countLit q [-107, -108, -112, -113, -114, -116, -117, -120]) (count1692 q) 5 (meaning1688 q) (meaning1696 q) hs
  change valuationOf q 1688 = false ∨ valuationOf q 1696 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause864 (q : Snake 81) (h : Conditions q) : valuation q 1688 = false ∨ valuation q 1696 = true := counterClause864 (baseVal q)

theorem block26 (q : Snake 81) (h : Conditions q) : B112E152.Block26 (valuation q) :=
  ⟨clause833 q h, clause834 q h, clause835 q h, clause836 q h, clause837 q h, clause838 q h, clause839 q h, clause840 q h, clause841 q h, clause842 q h, clause843 q h, clause844 q h, clause845 q h, clause846 q h, clause847 q h, clause848 q h, clause849 q h, clause850 q h, clause851 q h, clause852 q h, clause853 q h, clause854 q h, clause855 q h, clause856 q h, clause857 q h, clause858 q h, clause859 q h, clause860 q h, clause861 q h, clause862 q h, clause863 q h, clause864 q h⟩

end
end Snake9.Regrowth.E112152
