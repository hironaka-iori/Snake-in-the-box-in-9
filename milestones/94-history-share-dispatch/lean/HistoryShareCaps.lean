import HistoryShareCover

/-!
Capped per-word history-share dispatch. Concrete geometric bounds remain
premises. Numeric cap transfer is restricted to positions below six and caps
strictly below six; a saturated symbol is never read as an exact count here.
This source awaits compilation.
-/

namespace Snake9.HistoryShare94
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Direction77 Snake9.Guards79 Snake9.GraphWalk78
open Snake9.CountGeometry78 Snake9.GraphInterpretation75
open Snake9.GraphInterpretation74 Snake9.CountFreeAdapter73 Snake9.History84

set_option maxHeartbeats 2000000

/-- For an eleven-direction window starting at s, cap position k refers to
s+(k+5). The credited centres are s+6 through s+10. Every concrete word still
requires a separate proof of this conditional geometric statement. -/
def WordCappedShareBound (cs : List Nat) (caps : List (Nat × Nat))
    (L : Nat) : Prop :=
  ∀ {m : Nat} (p : Snake m) (s : Nat), s+11 ≤ m →
    canon (dsOf p s 11) = cs →
    (∀ kc ∈ caps, coreAlpha p (s+(kc.1+5)) ≤ kc.2) →
    L ≤ ((List.range 5).map fun i => coreShare 12 p (s+(i+6))).sum

/-- The numeric conjunction used for the capped six-count symbols.
Position/cap validity is deliberately a separate hypothesis of its bridge. -/
def numericCapsTest (code : Nat) (caps : List (Nat × Nat)) : Bool :=
  caps.all fun kc => decide (digit code kc.1 ≤ kc.2)

/-- A digit cap below six transfers to the underlying count. The strict cap
bound is essential: the symbol six may represent a count greater than six. -/
theorem numeric_cap_to_actual {m : Nat} (p : Snake m) (r k cap : Nat)
    (hr : r+9 ≤ m) (hk : k < 6) (hcap : cap < 6)
    (hdigit : digit (sixCode p r) k ≤ cap) :
    coreAlpha p (r+(k+3)) ≤ cap := by
  rw [actual_digit p r k hr hk] at hdigit
  change min 6 (coreAlpha p (r+k+3)) ≤ cap at hdigit
  have hcount := (truncated_guard (coreAlpha p (r+k+3)) cap hcap).mp hdigit
  simpa only [Nat.add_assoc] using hcount

/-- Every valid cap in the numeric test gives its corresponding actual cap.
There is no bridge for a cap equal to six in this statement. -/
theorem numeric_caps_to_actual {m : Nat} (p : Snake m) (r : Nat)
    (caps : List (Nat × Nat)) (hr : r+9 ≤ m)
    (hvalid : ∀ kc ∈ caps, kc.1 < 6 ∧ kc.2 < 6)
    (hhit : numericCapsTest (sixCode p r) caps = true) :
    ∀ kc ∈ caps, coreAlpha p (r+(kc.1+3)) ≤ kc.2 := by
  intro kc hkc
  have htest := List.all_eq_true.mp hhit kc hkc
  have hdigit : digit (sixCode p r) kc.1 ≤ kc.2 := of_decide_eq_true htest
  exact numeric_cap_to_actual p r kc.1 kc.2 hr
    (hvalid kc hkc).1 (hvalid kc hkc).2 hdigit

/-- Dispatch actual cap hypotheses through the emitted canonical-word cover.
Every covered word must supply the same capped share bound explicitly. -/
theorem emitted_capped_five_centre_share {m : Nat} (p : Snake m) (r : Nat)
    (sig : List Nat) (expectedWords : List (List Nat))
    (caps : List (Nat × Nat)) (L : Nat)
    (hr : r+9 ≤ m) (hlen : sig.length = 3)
    (htable : shareCoverTable sig expectedWords = true)
    (hemit : sig <:+ Snake9.History75.prefixes.getD (actualHistory p r) [] ++
      [directionId p r])
    (hcaps : ∀ kc ∈ caps, coreAlpha p (r+(kc.1+3)) ≤ kc.2)
    (hwords : ∀ cs ∈ expectedWords, WordCappedShareBound cs caps L) :
    L ≤ ((List.range 5).map fun i => coreShare 12 p (r+(i+4))).sum := by
  obtain ⟨hr2,hmem⟩ := emitted_word_mem p r sig expectedWords hr hlen htable hemit
  have hcapShift : ∀ k : Nat, r-2+(k+5) = r+(k+3) := by
    intro k
    omega
  have hlocal : ∀ kc ∈ caps, coreAlpha p ((r-2)+(kc.1+5)) ≤ kc.2 := by
    intro kc hkc
    simpa only [hcapShift] using hcaps kc hkc
  have hbound := (hwords _ hmem) p (r-2) (by omega) rfl hlocal
  have hshareShift : ∀ i : Nat, r-2+(i+6) = r+(i+4) := by
    intro i
    omega
  simpa only [hshareShift] using hbound

/-- Numeric cap test followed by the conditional per-word geometric dispatch.
The cap validity, cover, emission and per-word share premises all remain. -/
theorem emitted_capped_share_of_numeric_test {m : Nat} (p : Snake m) (r : Nat)
    (sig : List Nat) (expectedWords : List (List Nat))
    (caps : List (Nat × Nat)) (L : Nat)
    (hr : r+9 ≤ m) (hlen : sig.length = 3)
    (htable : shareCoverTable sig expectedWords = true)
    (hemit : sig <:+ Snake9.History75.prefixes.getD (actualHistory p r) [] ++
      [directionId p r])
    (hvalid : ∀ kc ∈ caps, kc.1 < 6 ∧ kc.2 < 6)
    (hhit : numericCapsTest (sixCode p r) caps = true)
    (hwords : ∀ cs ∈ expectedWords, WordCappedShareBound cs caps L) :
    L ≤ ((List.range 5).map fun i => coreShare 12 p (r+(i+4))).sum := by
  exact emitted_capped_five_centre_share p r sig expectedWords caps L
    hr hlen htable hemit (numeric_caps_to_actual p r caps hr hvalid hhit) hwords

#print axioms numeric_cap_to_actual
#print axioms numeric_caps_to_actual
#print axioms emitted_capped_five_centre_share
#print axioms emitted_capped_share_of_numeric_test

end Snake9.HistoryShare94
