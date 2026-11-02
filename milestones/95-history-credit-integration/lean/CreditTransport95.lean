import HistoryShareCaps

/-!
Generic transport from coordinate-permuted local share theorems to canonical
history words. All concrete local geometry remains an explicit premise.
This source awaits compilation.
-/

namespace Snake9.CreditTransport95
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Guards79 Snake9.GraphWalk78 Snake9.CountGeometry78
open Snake9.GraphInterpretation74 Snake9.CountFreeAdapter73
open Snake9.HistoryShare94

set_option maxHeartbeats 2000000

/-- Coordinate permutation witnessing an actual canonical direction word.
This repeats the small generic transport proof without importing geometry. -/
theorem canonical_permutation {m : Nat} (p : Snake m) (s n : Nat)
    (hr : s+n ≤ m) :
    ∃ P : CPerm, ∀ j, j < n →
      P.fwd (dir p (s+j)) = (canon (dsOf p s n)).getD j 0 := by
  obtain ⟨u,hu,hu9,hlen,hcs⟩ := actual_canonical_frame p s n hr
  refine ⟨mkPerm u, ?_⟩
  intro j hj
  obtain ⟨hi,hd⟩ := hcs j hj
  rw [← hd]
  exact mkPerm_spec hu hu9 hlen _ hi

/-- The shape of an uncapped local in_snake-style theorem. The eleven-word
length is supplied separately when adapting this premise. -/
def LocalWordShare (cs : List Nat) (L : Nat) : Prop :=
  ∀ {m : Nat} (p : Snake m) (P : CPerm) (s : Nat), s+11 ≤ m →
    (∀ j, j < cs.length → P.fwd (dir p (s+j)) = cs.getD j 0) →
    L ≤ ((List.range 5).map fun i => coreShare 12 p (s+(i+6))).sum

theorem word_share_of_local (cs : List Nat) (L : Nat)
    (hlen : cs.length = 11) (hlocal : LocalWordShare cs L) :
    WordShareBound cs L := by
  intro m p s hr hcanon
  obtain ⟨P,hP⟩ := canonical_permutation p s 11 hr
  apply hlocal p P s hr
  intro j hj
  have hj11 : j < 11 := by simpa only [hlen] using hj
  have h := hP j hj11
  rw [hcanon] at h
  exact h

/-- A supplied ten-entry bounds list is usable if its lower endpoints are
zero and each upper endpoint is either 21 or a supplied cap at index 4+k.
The relation allows unused/repeated caps; it never invents an extra restriction.
Cap positions and unsaturated cap values are explicit validity requirements. -/
def BoundsFromCaps (caps bounds : List (Nat × Nat)) : Prop :=
  bounds.length = 10 ∧
    (∀ kc ∈ caps, kc.1 < 6 ∧ kc.2 < 6) ∧
    ∀ i, i < 10 →
      (bounds.getD i (0,21)).1 = 0 ∧
      ((bounds.getD i (0,21)).2 = 21 ∨
        ∃ kc ∈ caps, i = 4+kc.1 ∧ (bounds.getD i (0,21)).2 = kc.2)

/-- The shape of a local theorem with actual-count bounds at the ten internal
positions. These bounds are on coreAlpha, not on saturated count symbols. -/
def LocalBoundedWordShare (cs : List Nat) (bounds : List (Nat × Nat))
    (L : Nat) : Prop :=
  ∀ {m : Nat} (p : Snake m) (P : CPerm) (s : Nat), s+11 ≤ m →
    (∀ j, j < cs.length → P.fwd (dir p (s+j)) = cs.getD j 0) →
    (∀ i, i < bounds.length →
      (bounds.getD i (0,21)).1 ≤ coreAlpha p (s+i+1) ∧
      coreAlpha p (s+i+1) ≤ (bounds.getD i (0,21)).2) →
    L ≤ ((List.range 5).map fun i => coreShare 12 p (s+(i+6))).sum

/-- Actual caps imply the supplied local bounds. Default upper bounds use the
universal internal singleton-count bound; a cap at index 4+k addresses s+k+5. -/
theorem actual_bounds_from_caps {m : Nat} (p : Snake m) (s : Nat)
    (caps bounds : List (Nat × Nat)) (hr : s+11 ≤ m)
    (hrel : BoundsFromCaps caps bounds)
    (hcaps : ∀ kc ∈ caps, coreAlpha p (s+(kc.1+5)) ≤ kc.2) :
    ∀ i, i < bounds.length →
      (bounds.getD i (0,21)).1 ≤ coreAlpha p (s+i+1) ∧
      coreAlpha p (s+i+1) ≤ (bounds.getD i (0,21)).2 := by
  intro i hi
  have hi10 : i < 10 := by simpa only [hrel.1] using hi
  obtain ⟨hzero,hupper⟩ := hrel.2.2 i hi10
  constructor
  · rw [hzero]
    exact Nat.zero_le _
  · rcases hupper with hdefault | ⟨kc,hkc,hindex,hcap⟩
    · rw [hdefault]
      exact coreAlpha_le_21 p (by omega) (by omega)
    · rw [hcap]
      have hshift : s+i+1 = s+(kc.1+5) := by omega
      rw [hshift]
      exact hcaps kc hkc

theorem word_capped_share_of_local (cs : List Nat)
    (caps bounds : List (Nat × Nat)) (L : Nat)
    (hlen : cs.length = 11) (hrel : BoundsFromCaps caps bounds)
    (hlocal : LocalBoundedWordShare cs bounds L) :
    WordCappedShareBound cs caps L := by
  intro m p s hr hcanon hcaps
  obtain ⟨P,hP⟩ := canonical_permutation p s 11 hr
  apply hlocal p P s hr
  · intro j hj
    have hj11 : j < 11 := by simpa only [hlen] using hj
    have h := hP j hj11
    rw [hcanon] at h
    exact h
  · exact actual_bounds_from_caps p s caps bounds hr hrel hcaps

#print axioms canonical_permutation
#print axioms word_share_of_local
#print axioms actual_bounds_from_caps
#print axioms word_capped_share_of_local

end Snake9.CreditTransport95
