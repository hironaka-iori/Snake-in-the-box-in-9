import DfsBankCert144v2
import DfsPrefix

/- Consequences of the certified bank-prefix exclusion. These results concern
only snakes sharing a specified 144-vertex end segment with a bank entry. -/
namespace Snake9.Dfs

theorem bank_no_long_prefix_keep144 (j : Nat) (hj : j < 262)
    {m : Nat} (hm : 192 ≤ m) (p : Snake m) :
    ¬ StartsWith p (oriented j) 144 :=
  prefix_exclusion_all_lengths (oriented j) 144 (by decide)
    (bank_no192_keep144v2 j hj) hm p

/-- The terminal segment is read from the final endpoint inward. -/
theorem bank_no_long_suffix_keep144 (j : Nat) (hj : j < 262)
    {m : Nat} (hm : 192 ≤ m) (p : Snake m) :
    ¬ EndsWith p (oriented j) 144 :=
  suffix_exclusion_all_lengths (oriented j) 144 (by decide)
    (bank_no192_keep144v2 j hj) hm p

/-- A snake with one of the specified end segments has at most 191 edges. -/
theorem bank_end_segment_length_le191 (j : Nat) (hj : j < 262)
    {m : Nat} (p : Snake m)
    (h : StartsWith p (oriented j) 144 ∨ EndsWith p (oriented j) 144) :
    m ≤ 191 := by
  by_cases hm : 192 ≤ m
  · rcases h with h | h
    · exact False.elim (bank_no_long_prefix_keep144 j hj hm p h)
    · exact False.elim (bank_no_long_suffix_keep144 j hj hm p h)
  · omega

#print axioms bank_no_long_prefix_keep144
#print axioms bank_no_long_suffix_keep144
#print axioms bank_end_segment_length_le191
end Snake9.Dfs
