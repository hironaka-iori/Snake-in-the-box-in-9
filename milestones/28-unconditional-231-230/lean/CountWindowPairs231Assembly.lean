import CountWindowPairs231
import FastCountD012A11.LocalWindow
import FastCountD012A12.LocalWindow
import FastCountD012A13.LocalWindow
import FastCountQ012A14.LocalWindow

/-! Assemble the four exact two-centre refutations into the aggregate hw2 premise.
Compilation and axiom receipts, rather than this source file, establish completion.
-/
namespace Snake9.CountWindowPairs231Assembly
open LocalWindow DirectionWindow WindowAutomaton CountWindowBridge

theorem all_refuted : AllRefutedIntervals CountWindowPairs231.keys := by
  intro key hk
  simp only [CountWindowPairs231.keys, List.mem_cons, List.mem_singleton] at hk
  rcases hk with h | h | h | h
  · subst key
    exact FastCountD012A11.refuted
  · subst key
    exact FastCountD012A12.refuted
  · subst key
    exact FastCountD012A13.refuted
  · subst key
    exact FastCountQ012A14.refuted

/-- The exact two-centre exclusion premise, with no certificate-family parameter. -/
theorem hw2 {m : Nat} (p : Snake m) :
    ∀ r, r + 3 ≤ m → wforbK6R34C7W [pathDir p r, pathDir p (r+1), pathDir p (r+2)]
      [symK 8 (countSeq p (r+1)), symK 8 (countSeq p (r+2))] = false :=
  CountWindowPairs231.hw2_of_pairs all_refuted p

#print axioms all_refuted
#print axioms hw2
end Snake9.CountWindowPairs231Assembly
