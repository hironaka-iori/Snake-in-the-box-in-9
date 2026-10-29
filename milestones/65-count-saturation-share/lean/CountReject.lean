import CountChoice
namespace Snake9.LocalWindow.CountPropagation65
open ForcedShare58 ExtendedShare59 SplitShare62 NeighbourChoice64
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def isRejection : Ending → Bool
  | .share _ => false
  | _ => true

theorem certCheck_rejection (W A B C : List Nat) (cs : List Condition) (L : Nat)
    (a b : Option Nat) (cert : TraceCertificate) (h : isRejection cert.ending=true) :
    certCheck W A B C cs L a b cert=certCheck W A B C cs 0 a b cert := by
  cases he : cert.ending <;> simp_all [isRejection,certCheck,endingCheck]

theorem count_choices_impossible {W dirs A B C : List Nat} {bounds : List (Nat × Nat)}
    {centres : List Centre} {start : Nat}
    (cert : Option Nat → Option Nat → TraceCertificate)
    (hc : Canon W dirs) (hlen : bounds.length+1=dirs.length) (hstart : start+4≤dirs.length)
    (hC : C=(List.range 5).map (fun i => W.getD (i+start) 0))
    (hcentres : ∀ c∈centres, c∈centresOf W bounds)
    (hp : supportCheck W C=true) (hA : pairCheck W A=true) (hB : pairCheck W B=true)
    (hcheck : (choices A).all (fun a => (choices B).all (fun b =>
      certCheck W A B C (centres.map ofCentre) 0 a b (cert a b)))=true)
    (hreject : (choices A).all (fun a => (choices B).all (fun b => isRejection (cert a b).ending))=true)
    {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+dirs.length≤m) (hP : ∀ j, j<dirs.length → P.fwd (dir p (r+j))=dirs.getD j 0)
    (hb : ∀ i, i<bounds.length → (bounds.getD i (0,21)).1≤coreAlpha p (r+i+1) ∧
      coreAlpha p (r+i+1)≤(bounds.getD i (0,21)).2) : False := by
  let L := ((List.range 5).map (fun i => coreShare 12 p (r+(i+start)))).sum+1
  have hall : (choices A).all (fun a => (choices B).all (fun b =>
      certCheck W A B C (centres.map ofCentre) L a b (cert a b)))=true := by
    apply List.all_eq_true.mpr
    intro a ha
    apply List.all_eq_true.mpr
    intro b hb'
    have hrej := List.all_eq_true.mp (List.all_eq_true.mp hreject a ha) b hb'
    rw [certCheck_rejection W A B C (centres.map ofCentre) L a b (cert a b) hrej]
    exact List.all_eq_true.mp (List.all_eq_true.mp hcheck a ha) b hb'
  have h := count_choices_in_snake (L:=L) cert hc hlen hstart hC hcentres hp hA hB hall p P r hr hP hb
  dsimp [L] at h
  omega

#print axioms certCheck_rejection
#print axioms count_choices_impossible
end Snake9.LocalWindow.CountPropagation65
