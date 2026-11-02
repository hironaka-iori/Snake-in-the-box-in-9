"""Generalize the already checked six-direction coordinate frame to any length."""
from pathlib import Path
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
old=(ROOT/'milestones/73-countfree-share-catalogue/adapter/lean/CanonicalShareAdapter.lean').read_text()
body=old[old.index('  let u :='):old.index('  have hsp :=')]
body=body.replace('dsOf p r 6','dsOf p r n').replace('j < 6','j < n')
source='''import StateWalk
import CanonicalShareAdapter

namespace Snake9.Guards79
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
set_option maxHeartbeats 1000000

theorem actual_canonical_frame {m : Nat} (p : Snake m) (r n : Nat)
    (hr : r+n ≤ m) :
    ∃ u : List Nat, u.Nodup ∧ (∀ d ∈ u, d < 9) ∧ u.length ≤ 9 ∧
      ∀ j, j < n → (canon (dsOf p r n)).getD j 0 < u.length ∧
        u.getD ((canon (dsOf p r n)).getD j 0) 0 = dir p (r+j) := by
'''+body+'''  exact ⟨u, hu, hu9, hulen, hcs⟩

theorem canonical_interval_exclusion {m : Nat} (p : Snake m) (r n : Nat)
    (cs : List Nat) (bounds : List (Nat × Nat))
    (hr : r+n ≤ m) (hlen : bounds.length+1 = n)
    (hshape : canon (dsOf p r n) = cs)
    (href : Refuted (winOf cs) bounds)
    (hb : ∀ i, i < bounds.length →
      (bounds.getD i (0,21)).1 ≤ coreAlpha p (r+i+1) ∧
      coreAlpha p (r+i+1) ≤ (bounds.getD i (0,21)).2) : False := by
  obtain ⟨u, hu, hu9, hulen, hcs⟩ := actual_canonical_frame p r n hr
  have hsp := mkPerm_spec hu hu9 hulen
  have href' : Refuted (winOf (canon (dsOf p r n))) bounds := by
    simpa only [hshape] using href
  apply refuted_bridge p (mkPerm u) r href' (canon_winOf _)
    (by simpa only [length_canon, length_dsOf] using hlen)
    (by simpa only [length_canon, length_dsOf] using hr)
  · intro j hj
    have hjn : j < n := by simpa only [length_canon, length_dsOf] using hj
    obtain ⟨hi, hd⟩ := hcs j hjn
    rw [← hd]
    exact hsp _ hi
  · exact hb

theorem canonical_symbol_exclusion {m : Nat} (p : Snake m) (r n : Nat)
    (cs syms : List Nat) (hr : r+n ≤ m) (hn : 1 ≤ n)
    (hshape : canon (dsOf p r n) = cs) (hsyms : symsOf p r n = syms)
    (href : Refuted (winOf cs) (boundsOf syms)) : False := by
  obtain ⟨u, hu, hu9, _, hcs⟩ := actual_canonical_frame p r n hr
  have hlen : syms.length+1 = n := by
    rw [← hsyms, length_symsOf]; omega
  have href' : Refuted (winOf (canon (dsOf p r n))) (boundsOf syms) := by
    simpa only [hshape] using href
  apply refuted_dir href' p r
    (by simpa only [length_canon, length_dsOf] using hlen)
    (by simpa only [length_canon, length_dsOf] using hr) hu hu9
  · simpa only [length_canon, length_dsOf] using hcs
  · intro i hi
    have hi' : i < n-1 := by rw [← hsyms, length_symsOf] at hi; exact hi
    rw [← hsyms, getD_symsOf p hi']

theorem reversed_symbol_exclusion {m : Nat} (p : Snake m) (r n : Nat)
    (cs syms : List Nat) (hr : r+n ≤ m) (hn : 1 ≤ n)
    (hshape : canon (dsOf p r n).reverse = cs)
    (hsyms : (symsOf p r n).reverse = syms)
    (href : Refuted (winOf cs) (boundsOf syms)) : False := by
  apply canonical_symbol_exclusion (revSnake p) (m-r-n) n cs syms (by omega) hn
  · rw [dsOf_rev p r n hr]; exact hshape
  · rw [symsOf_rev p r n hr]; exact hsyms
  · exact href

#print axioms actual_canonical_frame
#print axioms canonical_interval_exclusion
#print axioms canonical_symbol_exclusion
#print axioms reversed_symbol_exclusion
end Snake9.Guards79
'''
(HERE/'lean/CanonicalExclusions.lean').write_text(source,encoding='utf-8')
print('Generalized canonical frame and exclusion interfaces written')
