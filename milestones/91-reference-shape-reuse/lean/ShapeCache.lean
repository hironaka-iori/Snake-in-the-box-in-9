import WitnessFactors

namespace Snake9.Shape91
open Snake9.Boxes88 Snake9.Witness90

structure Shape where
  di : Nat
  offset : Nat
  width : Nat
  reverse : Bool
  pattern : List Nat
  deriving DecidableEq, Repr

def shapeValid (dirsAt : Nat → List Nat) (s : Shape) : Bool :=
  directionShapeAt (dirsAt s.di) s.offset s.width s.reverse s.pattern

def referenceRequest (refsAt : Nat → List Nat × List Nat)
    (di ki offset : Nat) (reverse : Bool) : Shape :=
  let key := refsAt ki
  ⟨di,offset+2,key.2.length+1,reverse,key.1⟩

/-- Only a reference shape calculation is replaced. Its catalogue and placement
guards remain, and its cache lookup must be bounded and match the full descriptor. -/
def cachedCompatibilityAt (dirsAt : Nat → List Nat)
    (refsAt : Nat → List Nat × List Nat) (referenceCount : Nat)
    (shapeAt : Nat → Shape) (shapeCount q di : Nat) (w : Witness) (cacheIndex : Nat) : Bool :=
  match w with
  | .reference ki offset reverse =>
    let key := refsAt ki
    decide (q < 75 ∧ di < 505) && (decide (ki < referenceCount) &&
      (decide (2 ≤ key.2.length ∧ offset+key.2.length ≤ 6) &&
      (decide (cacheIndex < shapeCount) &&
        decide (shapeAt cacheIndex = referenceRequest refsAt di ki offset reverse))))
  | _ => compatibilityAt dirsAt refsAt referenceCount q di w

def entriesCachedCompatibility (dirsAt : Nat → List Nat)
    (refsAt : Nat → List Nat × List Nat) (referenceCount : Nat)
    (shapeAt : Nat → Shape) (shapeCount q di : Nat)
    (entries : List (Box × Witness)) (indices : List Nat) : Bool :=
  decide (indices.length = entries.length) &&
    (entries.zip indices).all fun item =>
      cachedCompatibilityAt dirsAt refsAt referenceCount shapeAt shapeCount q di item.1.2 item.2

theorem cachedCompatibility_sound (dirsAt : Nat → List Nat)
    (refsAt : Nat → List Nat × List Nat) (referenceCount : Nat)
    (shapeAt : Nat → Shape) (shapeCount : Nat)
    (hshape : ∀ i, i < shapeCount → shapeValid dirsAt (shapeAt i) = true)
    (q di : Nat) (w : Witness) (cacheIndex : Nat)
    (hc : cachedCompatibilityAt dirsAt refsAt referenceCount shapeAt shapeCount q di w cacheIndex = true) :
    compatibilityAt dirsAt refsAt referenceCount q di w = true := by
  cases w with
  | reference ki offset reverse =>
    have h : (q < 75 ∧ di < 505) ∧ ki < referenceCount ∧
        (2 ≤ (refsAt ki).2.length ∧ offset+(refsAt ki).2.length ≤ 6) ∧
        cacheIndex < shapeCount ∧
        shapeAt cacheIndex = referenceRequest refsAt di ki offset reverse := by
      simpa only [cachedCompatibilityAt,Bool.and_eq_true_iff,decide_eq_true_eq] using hc
    have hs := hshape cacheIndex h.2.2.2.1
    rw [h.2.2.2.2] at hs
    have hs' : referenceShapeAt (dirsAt di) offset (refsAt ki).2.length reverse (refsAt ki).1 = true := by
      simpa only [shapeValid,referenceRequest,referenceShapeAt] using hs
    simp only [compatibilityAt,referenceCompatibilityAt,Bool.and_eq_true_iff,decide_eq_true_eq]
    exact ⟨h.1,h.2.1,h.2.2.1,hs'⟩
  | short ki offset reverse => exact hc
  | interval ki offset reverse => exact hc
  | history ki => exact hc

/-- Equal list lengths ensure every entry has a checked cache-index position,
including entries whose nonreference witness ignores that index. -/
theorem entriesCachedCompatibility_sound (dirsAt : Nat → List Nat)
    (refsAt : Nat → List Nat × List Nat) (referenceCount : Nat)
    (shapeAt : Nat → Shape) (shapeCount : Nat)
    (hshape : ∀ i, i < shapeCount → shapeValid dirsAt (shapeAt i) = true)
    (q di : Nat) (entries : List (Box × Witness)) (indices : List Nat)
    (hc : entriesCachedCompatibility dirsAt refsAt referenceCount shapeAt shapeCount q di entries indices = true) :
    entriesCompatibilityAt dirsAt refsAt referenceCount q di entries = true := by
  have h := Bool.and_eq_true_iff.mp hc
  have hlen : indices.length = entries.length := of_decide_eq_true h.1
  have hz : (entries.zip indices).map Prod.fst = entries := List.map_fst_zip (by omega)
  apply List.all_eq_true.mpr
  intro item hm
  have hm' : item ∈ (entries.zip indices).map Prod.fst := by simpa only [hz] using hm
  obtain ⟨pair,hpair,heq⟩ := List.mem_map.mp hm'
  have hp := List.all_eq_true.mp h.2 pair hpair
  have result := cachedCompatibility_sound dirsAt refsAt referenceCount shapeAt shapeCount
    hshape q di pair.1.2 pair.2 hp
  simpa only [heq] using result

theorem entries_valid_of_cache (dirsAt : Nat → List Nat)
    (refsAt : Nat → List Nat × List Nat) (referenceCount : Nat)
    (shapeAt : Nat → Shape) (shapeCount : Nat)
    (hshape : ∀ i, i < shapeCount → shapeValid dirsAt (shapeAt i) = true)
    (q di : Nat) (entries : List (Box × Witness)) (indices : List Nat)
    (hc : entriesCachedCompatibility dirsAt refsAt referenceCount shapeAt shapeCount q di entries indices = true)
    (hb : entriesBoxCountsAt refsAt entries = true) :
    entriesValidAt dirsAt refsAt referenceCount q di entries = true := by
  exact entries_valid_of_factors dirsAt refsAt referenceCount q di entries
    (entriesCachedCompatibility_sound dirsAt refsAt referenceCount shapeAt shapeCount
      hshape q di entries indices hc) hb

#print axioms cachedCompatibility_sound
#print axioms entriesCachedCompatibility_sound
#print axioms entries_valid_of_cache
end Snake9.Shape91
