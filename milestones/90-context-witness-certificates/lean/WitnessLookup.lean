import SharedAssembly

namespace Snake9.Witness90
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Direction77 Snake9.Reference85 Snake9.Boxes88 Snake9.Retained87

/-- Only catalogue lookup and catalogue length are parameters. All placement,
orientation, singleton and bounds tests agree with the original checker. -/
def referenceBoxValidAt (refsAt : Nat → List Nat × List Nat) (referenceCount : Nat)
    (ds : List Nat) (b : Box) (ki s : Nat) (reverse : Bool) : Bool :=
  let k := refsAt ki
  decide (ki < referenceCount) && (decide (2 ≤ k.2.length ∧ s+k.2.length ≤ 6) &&
    ((canon (oriented reverse ((ds.drop (s+2)).take (k.2.length+1))) == k.1) &&
    (List.range k.2.length).all fun i => decide
      ((b.getD (s+i) (1,6)).1 = (oriented reverse k.2).getD i 0 ∧
       (b.getD (s+i) (1,6)).2 = (oriented reverse k.2).getD i 0)))

/-- Direction lookup is supplied, while the history direction index retains
the original extensions.idxOf computation. -/
def boxWitnessValidAt (dirsAt : Nat → List Nat)
    (refsAt : Nat → List Nat × List Nat) (referenceCount : Nat)
    (q di : Nat) (b : Box) (w : Witness) : Bool :=
  decide (b.length = 6 ∧ q < 75 ∧ di < 505) &&
    let ds := dirsAt di
    match w with
    | .reference ki s reverse => referenceBoxValidAt refsAt referenceCount ds b ki s reverse
    | .short ki s reverse => shortBoxValid ds b ki s reverse
    | .interval ki s reverse => intervalBoxValid ds b ki s reverse
    | .history ki => historyBoxValid q (extensions.idxOf ds) b ki

def entriesValidAt (dirsAt : Nat → List Nat)
    (refsAt : Nat → List Nat × List Nat) (referenceCount : Nat)
    (q di : Nat) (entries : List (Box × Witness)) : Bool :=
  entries.all fun item => boxWitnessValidAt dirsAt refsAt referenceCount q di item.1 item.2

theorem referenceBoxValidAt_eq (refsAt : Nat → List Nat × List Nat) (referenceCount : Nat)
    (hrefs : ∀ i, refsAt i = referenceKeys.getD i ([],[]))
    (hcount : referenceCount = referenceKeys.length) :
    referenceBoxValidAt refsAt referenceCount = referenceBoxValid := by
  funext ds b ki s reverse
  simp only [referenceBoxValidAt,referenceBoxValid,hrefs,hcount]

/-- The all-index hypotheses also fix the defaults outside each source table. -/
theorem boxWitnessValidAt_eq (dirsAt : Nat → List Nat)
    (refsAt : Nat → List Nat × List Nat) (referenceCount : Nat)
    (hdirs : ∀ i, dirsAt i = extensions.getD i [])
    (hrefs : ∀ i, refsAt i = referenceKeys.getD i ([],[]))
    (hcount : referenceCount = referenceKeys.length) :
    boxWitnessValidAt dirsAt refsAt referenceCount = boxWitnessValid := by
  funext q di b w
  cases w <;> simp only [boxWitnessValidAt,boxWitnessValid,hdirs,
    referenceBoxValidAt_eq refsAt referenceCount hrefs hcount]

theorem entriesValidAt_eq (dirsAt : Nat → List Nat)
    (refsAt : Nat → List Nat × List Nat) (referenceCount : Nat)
    (hdirs : ∀ i, dirsAt i = extensions.getD i [])
    (hrefs : ∀ i, refsAt i = referenceKeys.getD i ([],[]))
    (hcount : referenceCount = referenceKeys.length) :
    entriesValidAt dirsAt refsAt referenceCount = entriesValid := by
  funext q di entries
  simp only [entriesValidAt,entriesValid,
    boxWitnessValidAt_eq dirsAt refsAt referenceCount hdirs hrefs hcount]

/-- The optimized finite validity check can feed the existing shared assembly
once its supplied lookups are identified with the original tables. -/
theorem lookup_validated_membership (dirsAt : Nat → List Nat)
    (refsAt : Nat → List Nat × List Nat) (referenceCount : Nat)
    (hdirs : ∀ i, dirsAt i = extensions.getD i [])
    (hrefs : ∀ i, refsAt i = referenceKeys.getD i ([],[]))
    (hcount : referenceCount = referenceKeys.length)
    (q di code : Nat) (g : Diagram) (node : Nat)
    (boxes : List Box) (ws : List Witness) (certificate : CoverTree)
    (hlen : ws.length = boxes.length)
    (hv : entriesValidAt dirsAt refsAt referenceCount q di (boxes.zip ws) = true)
    (hcover : checkCover g boxes 6 [] node certificate = true)
    (hc : code < 46656) (hkeep : numericKeep q di code = true) :
    diagramEval g node (digits code) = true := by
  apply Snake9.Shared89.shared_numeric_keep_implies_diagram q di code g node boxes ws
    certificate hlen ?_ hcover hc hkeep
  simpa only [entriesValidAt_eq dirsAt refsAt referenceCount hdirs hrefs hcount] using hv

#print axioms referenceBoxValidAt_eq
#print axioms boxWitnessValidAt_eq
#print axioms entriesValidAt_eq
#print axioms lookup_validated_membership
end Snake9.Witness90
