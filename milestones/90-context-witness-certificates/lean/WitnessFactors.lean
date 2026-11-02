import WitnessLookup

namespace Snake9.Witness90
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Direction77 Snake9.Guards79 Snake9.ShortRules81 Snake9.History84
open Snake9.Boxes88 Snake9.Retained87

/-- This normalized shape expression does not contain a catalogue index or counts. -/
def directionShapeAt (ds : List Nat) (offset width : Nat) (reverse : Bool)
    (pattern : List Nat) : Bool :=
  canon (oriented reverse ((ds.drop offset).take width)) == pattern

def referenceShapeAt (ds : List Nat) (s width : Nat) (reverse : Bool)
    (pattern : List Nat) : Bool :=
  directionShapeAt ds (s+2) (width+1) reverse pattern

def referenceCompatibilityAt (refsAt : Nat → List Nat × List Nat) (referenceCount : Nat)
    (ds : List Nat) (ki s : Nat) (reverse : Bool) : Bool :=
  let k := refsAt ki
  decide (ki < referenceCount) && (decide (2 ≤ k.2.length ∧ s+k.2.length ≤ 6) &&
    referenceShapeAt ds s k.2.length reverse k.1)

def shortCompatibilityAt (ds : List Nat) (ki offset : Nat) (reverse : Bool) : Bool :=
  let rule := shortRules.getD ki ([],.caps [])
  decide (ki < shortRules.length ∧ offset < 10) &&
    (decide (offset+rule.1.length ≤ 9) &&
    ((rule.2.positions.all fun j => decide
      (3 ≤ offset+orientedPosition rule.1.length reverse j ∧
       offset+orientedPosition rule.1.length reverse j ≤ 8)) &&
    directionShapeAt ds offset rule.1.length reverse rule.1))

def intervalCompatibilityAt (ds : List Nat) (ki s : Nat) (reverse : Bool) : Bool :=
  let key := intervalKeys72.getD ki ([],[])
  decide (ki < intervalKeys72.length ∧ s < 3 ∧ key.2.length = 4) &&
    directionShapeAt ds (s+2) 5 reverse key.1

def historyCompatibilityAt (q decodedDi ki : Nat) : Bool :=
  let rule := historyRules.getD ki ([],0)
  let hist := Snake9.History75.prefixes.getD q [] ++ [decodedDi]
  decide (ki < historyRules.length ∧ rule.2 < 6) &&
    (decide (3 ≤ hist.length) && (hist.drop (hist.length-3) == rule.1))

/-- Catalogue and placement guards remain explicit. History uses precisely the
same direction-index recovery as the unfactored validator. -/
def compatibilityAt (dirsAt : Nat → List Nat)
    (refsAt : Nat → List Nat × List Nat) (referenceCount : Nat)
    (q di : Nat) (w : Witness) : Bool :=
  decide (q < 75 ∧ di < 505) &&
    let ds := dirsAt di
    match w with
    | .reference ki s reverse => referenceCompatibilityAt refsAt referenceCount ds ki s reverse
    | .short ki offset reverse => shortCompatibilityAt ds ki offset reverse
    | .interval ki s reverse => intervalCompatibilityAt ds ki s reverse
    | .history ki => historyCompatibilityAt q (extensions.idxOf ds) ki

/-- All box-coordinate tests and defaults are retained. The interval coordinate
range test stays with the interval containment test. -/
def boxCountsAt (refsAt : Nat → List Nat × List Nat) (b : Box) (w : Witness) : Bool :=
  decide (b.length = 6) &&
    match w with
    | .reference ki s reverse =>
      let k := refsAt ki
      (List.range k.2.length).all fun i => decide
        ((b.getD (s+i) (1,6)).1 = (oriented reverse k.2).getD i 0 ∧
         (b.getD (s+i) (1,6)).2 = (oriented reverse k.2).getD i 0)
    | .short ki offset reverse =>
      let rule := shortRules.getD ki ([],.caps [])
      encodedBadB rule.2 (fun j => (b.getD
        (offset+orientedPosition rule.1.length reverse j-3) (1,6)).2)
    | .interval ki s reverse =>
      let key := intervalKeys72.getD ki ([],[])
      (List.range key.2.length).all fun i =>
        let j := s + if reverse then 4-1-i else i
        decide (j < 6 ∧ (key.2.getD i (0,21)).1 ≤ (b.getD j (1,6)).1 ∧
          (b.getD j (1,6)).2 ≤ (key.2.getD i (0,21)).2)
    | .history ki =>
      let rule := historyRules.getD ki ([],0)
      decide ((b.getD rule.2 (1,6)).2 ≤ 2)

/-- Exact factorization for arbitrary supplied lookup functions, including
invalid indices and default cases. No catalogue identity is assumed here. -/
theorem factors_eq_validator (dirsAt : Nat → List Nat)
    (refsAt : Nat → List Nat × List Nat) (referenceCount q di : Nat)
    (b : Box) (w : Witness) :
    (compatibilityAt dirsAt refsAt referenceCount q di w && boxCountsAt refsAt b w) =
      boxWitnessValidAt dirsAt refsAt referenceCount q di b w := by
  apply Bool.eq_iff_iff.mpr
  cases w <;>
    simp only [compatibilityAt,boxCountsAt,boxWitnessValidAt,
      referenceCompatibilityAt,referenceShapeAt,directionShapeAt,referenceBoxValidAt,
      shortCompatibilityAt,shortBoxValid,intervalCompatibilityAt,intervalBoxValid,
      historyCompatibilityAt,historyBoxValid,Bool.and_eq_true_iff,decide_eq_true_eq] <;>
    tauto

def entriesCompatibilityAt (dirsAt : Nat → List Nat)
    (refsAt : Nat → List Nat × List Nat) (referenceCount q di : Nat)
    (entries : List (Box × Witness)) : Bool :=
  entries.all fun item => compatibilityAt dirsAt refsAt referenceCount q di item.2

def entriesBoxCountsAt (refsAt : Nat → List Nat × List Nat)
    (entries : List (Box × Witness)) : Bool :=
  entries.all fun item => boxCountsAt refsAt item.1 item.2

theorem entry_factors_eq_validator (dirsAt : Nat → List Nat)
    (refsAt : Nat → List Nat × List Nat) (referenceCount q di : Nat)
    (entries : List (Box × Witness)) :
    (entriesCompatibilityAt dirsAt refsAt referenceCount q di entries &&
      entriesBoxCountsAt refsAt entries) =
      entriesValidAt dirsAt refsAt referenceCount q di entries := by
  apply Bool.eq_iff_iff.mpr
  simp only [entriesCompatibilityAt,entriesBoxCountsAt,entriesValidAt,
    Bool.and_eq_true_iff,List.all_eq_true]
  constructor
  · intro h item hm
    rw [← factors_eq_validator]
    exact Bool.and_eq_true_iff.mpr ⟨h.1 item hm,h.2 item hm⟩
  · intro h
    constructor
    · intro item hm
      have hh := h item hm
      rw [← factors_eq_validator] at hh
      exact (Bool.and_eq_true_iff.mp hh).1
    · intro item hm
      have hh := h item hm
      rw [← factors_eq_validator] at hh
      exact (Bool.and_eq_true_iff.mp hh).2

/-- Independent compatibility and count certificates can be combined on a
shared list of ordered entries, including a list produced by zip. -/
theorem entries_valid_of_factors (dirsAt : Nat → List Nat)
    (refsAt : Nat → List Nat × List Nat) (referenceCount q di : Nat)
    (entries : List (Box × Witness))
    (hc : entriesCompatibilityAt dirsAt refsAt referenceCount q di entries = true)
    (hb : entriesBoxCountsAt refsAt entries = true) :
    entriesValidAt dirsAt refsAt referenceCount q di entries = true := by
  rw [← entry_factors_eq_validator,hc,hb]
  rfl

#print axioms factors_eq_validator
#print axioms entry_factors_eq_validator
#print axioms entries_valid_of_factors
end Snake9.Witness90
