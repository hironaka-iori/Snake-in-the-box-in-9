import ConcreteRules95
import ReferenceRetention
import LocalWindowShareBridge

/-!
Count-conditioned share transport in the current history/graph environment.

The symbols are the existing `symsOf` values: symbols below six are exact,
and six represents the interval from six to the internal upper bound 21.
No concrete refutation or new numerical bound is asserted by this module.
The checking status is recorded in the accompanying compiler receipt.
-/

namespace Snake9.SymbolCredit97
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Guards79 Snake9.GraphInterpretation74 Snake9.GraphInterpretation75
open Snake9.GraphWalk78

set_option maxHeartbeats 2000000

/-- A canonical direction match and the exact stored count symbols transport
an interval-based share refutation to the actual internal centres. -/
theorem canonical_symbol_share {m M K : Nat} (p : Snake m) (r n : Nat)
    (cs syms : List Nat) (hr : r+n ≤ m) (hn : 1 ≤ n)
    (hshape : canon (dsOf p r n) = cs) (hsyms : symsOf p r n = syms)
    (href : RefutedShare (winOf cs) (boundsOf syms) M K) :
    K+1 ≤ ((List.range (n-1)).map fun i => coreShare M p (r+i+1)).sum := by
  obtain ⟨u, hu, hu9, _, hcs⟩ := actual_canonical_frame p r n hr
  have hlen : syms.length = n-1 := by
    rw [← hsyms, length_symsOf]
  have hsucc : syms.length+1 = n := by omega
  have href' : RefutedShare (winOf (canon (dsOf p r n))) (boundsOf syms) M K := by
    simpa only [hshape] using href
  have result := refuted_share_dir href' p r
    (by simpa only [length_canon, length_dsOf] using hsucc)
    (by simpa only [length_canon, length_dsOf] using hr) hu hu9
    (by simpa only [length_canon, length_dsOf] using hcs)
    (by
      intro i hi
      have hi' : i < n-1 := by simpa only [hlen] using hi
      rw [← hsyms, getD_symsOf p hi'])
  simpa only [hlen] using result

/-- Reversing a matching direction word also reverses its count symbols.
The share sum still concerns the same actual internal vertices. -/
theorem reversed_symbol_share {m M K : Nat} (p : Snake m) (r n : Nat)
    (cs syms : List Nat) (hr : r+n ≤ m) (hn : 1 ≤ n)
    (hshape : canon (dsOf p r n).reverse = cs)
    (hsyms : (symsOf p r n).reverse = syms)
    (href : RefutedShare (winOf cs) (boundsOf syms) M K) :
    K+1 ≤ ((List.range (n-1)).map fun i => coreShare M p (r+i+1)).sum := by
  have result := canonical_symbol_share (revSnake p) (m-r-n) n cs syms
    (by omega) hn
    (by rw [dsOf_rev p r n hr]; exact hshape)
    (by rw [symsOf_rev p r n hr]; exact hsyms) href
  have he := coreShare_window_rev M p r (n-1) (by omega)
  have hs : m-r-(n-1)-1 = m-r-n := by omega
  rw [hs] at he
  rw [he] at result
  exact result

/-- The last five symbols of the six-count code belong to the six-direction
suffix beginning at `r+3`. Its charged centres are exactly `r+4,...,r+8`. -/
theorem encoded_forward_suffix_share {m M K : Nat} (p : Snake m) (r : Nat)
    (cs syms : List Nat) (hr : r+9 ≤ m) (hlen : syms.length = 5)
    (hvalid : ∀ x ∈ syms, 1 ≤ x ∧ x ≤ 6)
    (href : RefutedShare (winOf cs) (boundsOf syms) M K)
    (hshape : canon ((canon (dsOf p r 9)).drop 3) = cs)
    (hcode : sixCode p r % 7776 = encodeCounts syms 0) :
    K+1 ≤ ((List.range 5).map fun i => coreShare M p (r+(i+4))).sum := by
  have hshape' : canon (dsOf p (r+3) 6) = cs := by
    rw [canonical_nine_share_suffix p r hr] at hshape
    exact hshape
  have hdecode := actual_slice_decode p r 1 5 hr (by omega) (by omega)
    syms hlen hvalid (by simpa using hcode)
  have hsyms : symsOf p (r+3) 6 = syms := by
    simpa only [Nat.add_assoc, Nat.reduceAdd] using hdecode
  have result := canonical_symbol_share p (r+3) 6 cs syms
    (by omega) (by omega) hshape' hsyms href
  simpa only [Nat.reduceSub, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using result

/-- The reversed suffix test must pair the reversed canonical directions with
reversed count symbols. Saturated symbols retain their interval meaning. -/
theorem encoded_reversed_suffix_share {m M K : Nat} (p : Snake m) (r : Nat)
    (cs syms : List Nat) (hr : r+9 ≤ m) (hlen : syms.length = 5)
    (hvalid : ∀ x ∈ syms, 1 ≤ x ∧ x ≤ 6)
    (href : RefutedShare (winOf cs) (boundsOf syms) M K)
    (hshape : canon (((canon (dsOf p r 9)).drop 3).reverse) = cs)
    (hcode : sixCode p r % 7776 = encodeCounts syms.reverse 0) :
    K+1 ≤ ((List.range 5).map fun i => coreShare M p (r+(i+4))).sum := by
  have hshape' : canon (dsOf p (r+3) 6).reverse = cs := by
    rw [← reverse_canon ((canon (dsOf p r 9)).drop 3),
      canonical_nine_share_suffix p r hr,
      reverse_canon (dsOf p (r+3) 6)] at hshape
    exact hshape
  have hdecode := actual_slice_decode p r 1 5 hr (by omega) (by omega)
    syms.reverse (by simpa using hlen)
    (fun x hx => hvalid x (List.mem_reverse.mp hx)) (by simpa using hcode)
  have hforward : symsOf p (r+3) 6 = syms.reverse := by
    simpa only [Nat.add_assoc, Nat.reduceAdd] using hdecode
  have hsyms : (symsOf p (r+3) 6).reverse = syms := by
    rw [hforward, List.reverse_reverse]
  have result := reversed_symbol_share p (r+3) 6 cs syms
    (by omega) (by omega) hshape' hsyms href
  simpa only [Nat.reduceSub, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using result

#print axioms canonical_symbol_share
#print axioms reversed_symbol_share
#print axioms encoded_forward_suffix_share
#print axioms encoded_reversed_suffix_share

end Snake9.SymbolCredit97
