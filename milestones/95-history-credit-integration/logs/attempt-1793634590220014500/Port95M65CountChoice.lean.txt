import Port95M65TraceShare
namespace Snake9.LocalWindow.CountPropagationPort95
open ForcedShare58 ExtendedShare59 SplitShare62 NeighbourChoice64
set_option maxHeartbeats 0
set_option maxRecDepth 100000

structure TraceCertificate where
  forced : List Nat
  steps : List Step
  ending : Ending

def certCheck (W A B C : List Nat) (cs : List Condition) (L : Nat)
    (a b : Option Nat) (cert : TraceCertificate) : Bool :=
  let T := picked a ++ picked b ++ W
  let D := cert.forced ++ unpicked A a ++ unpicked B b
  forceCheckPlus T cert.forced && traceCheck cs T D cert.steps &&
    endingCheck cs C L (run T D cert.steps).1 (run T D cert.steps).2 cert.ending

theorem cert_sound (S : Nat → Bool) (W A B C : List Nat) (cs : List Condition) (L : Nat)
    (a b : Option Nat) (cert : TraceCertificate)
    (hc : ∀ c∈cs, c.Valid S)
    (hW : ∀ v∈W, S v=true) (hd : ∀ v, S v=true → cnt S (nbrs v)≤2)
    (hlt : ∀ v, S v=true → v<512) (hp : supportCheck W C=true)
    (ha : ∀ v∈picked a, S v=true) (hb : ∀ v∈picked b, S v=true)
    (hna : ∀ v∈unpicked A a, S v=false) (hnb : ∀ v∈unpicked B b, S v=false)
    (hcheck : certCheck W A B C cs L a b cert=true) :
    L≤(C.map (shareLocal 12 S)).sum := by
  obtain ⟨hft,he⟩ := Bool.and_eq_true_iff.mp hcheck
  obtain ⟨hf,ht⟩ := Bool.and_eq_true_iff.mp hft
  have hT : ∀ v∈picked a ++ picked b ++ W, S v=true := by
    intro v hv
    simp only [List.mem_append] at hv
    rcases hv with (hv | hv) | hv
    · exact ha v hv
    · exact hb v hv
    · exact hW v hv
  have hD : ∀ v∈cert.forced ++ unpicked A a ++ unpicked B b, S v=false := by
    intro v hv
    simp only [List.mem_append] at hv
    rcases hv with (hv | hv) | hv
    · exact forced_absent_plus S _ cert.forced hT hd hf v hv
    · exact hna v hv
    · exact hnb v hv
  exact trace_share S cs W C _ _ L cert.steps cert.ending hc ⟨hT,hD⟩ hW hd hlt hp ht he

theorem count_choices_share (S : Nat → Bool) (W A B C : List Nat) (cs : List Condition) (L : Nat)
    (cert : Option Nat → Option Nat → TraceCertificate)
    (hc : ∀ c∈cs, c.Valid S)
    (hW : ∀ v∈W, S v=true) (hd : ∀ v, S v=true → cnt S (nbrs v)≤2)
    (hlt : ∀ v, S v=true → v<512) (hp : supportCheck W C=true)
    (hA : pairCheck W A=true) (hB : pairCheck W B=true)
    (hcheck : ∀ a∈choices A, ∀ b∈choices B, certCheck W A B C cs L a b (cert a b)=true) :
    L≤(C.map (shareLocal 12 S)).sum := by
  obtain ⟨a,ha,hsa,hna⟩ := one_choice S A (unique_selected S W A hW hd hA)
  obtain ⟨b,hb,hsb,hnb⟩ := one_choice S B (unique_selected S W B hW hd hB)
  exact cert_sound S W A B C cs L a b (cert a b) hc hW hd hlt hp hsa hsb hna hnb (hcheck a ha b hb)

def ofCentre (c : Centre) : Condition := ⟨corners c,c.lo,c.hi⟩

def canonicalCentres (W dirs : List Nat) (bounds : List (Nat × Nat)) : List Centre :=
  (List.range bounds.length).map fun i =>
    ⟨W.getD (i+1) 0, dirs.getD i 0, dirs.getD (i+1) 0,
      (bounds.getD i (0,21)).1, (bounds.getD i (0,21)).2⟩

theorem centresOf_canon {W dirs : List Nat} {bounds : List (Nat × Nat)}
    (hc : Canon W dirs) (hlen : bounds.length+1=dirs.length) :
    centresOf W bounds=canonicalCentres W dirs bounds := by
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  have h1 : dirOfStep (W.getD i 0) (W.getD (i+1) 0)=dirs.getD i 0 := by
    rw [hc.step i (by omega),dirOfStep_xor]
  have h2 : dirOfStep (W.getD (i+1) 0) (W.getD (i+2) 0)=dirs.getD (i+1) 0 := by
    rw [show i+2=i+1+1 by omega,hc.step (i+1) (by omega),dirOfStep_xor]
  simp only [h1,h2]

theorem count_choices_in_snake {W dirs A B C : List Nat} {bounds : List (Nat × Nat)}
    {centres : List Centre} {L start : Nat}
    (cert : Option Nat → Option Nat → TraceCertificate)
    (hc : Canon W dirs) (hlen : bounds.length+1=dirs.length) (hstart : start+4≤dirs.length)
    (hC : C=(List.range 5).map (fun i => W.getD (i+start) 0))
    (hcentres : ∀ c∈centres, c∈centresOf W bounds)
    (hp : supportCheck W C=true) (hA : pairCheck W A=true) (hB : pairCheck W B=true)
    (hcheck : (choices A).all (fun a => (choices B).all (fun b =>
      certCheck W A B C (centres.map ofCentre) L a b (cert a b)))=true)
    {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+dirs.length≤m) (hP : ∀ j, j<dirs.length → P.fwd (dir p (r+j))=dirs.getD j 0)
    (hb : ∀ i, i<bounds.length → (bounds.getD i (0,21)).1≤coreAlpha p (r+i+1) ∧
      coreAlpha p (r+i+1)≤(bounds.getD i (0,21)).2) :
    L≤((List.range 5).map (fun i => coreShare 12 p (r+(i+start)))).sum := by
  have ax := frame_axioms p P r hc hlen hr hP hb
  have hconds : ∀ c∈centres.map ofCentre, c.Valid (sel p (amap P (vx p r))) := by
    intro c hmem
    obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hmem
    have h := ax.alpha c' (hcentres c' hc')
    change c'.lo≤cnt (fun x => !(sel p (amap P (vx p r))) x) (corners c') ∧
      cnt (fun x => !(sel p (amap P (vx p r))) x) (corners c')≤c'.hi
    simpa only [corners_count] using h
  have hs := count_choices_share (sel p (amap P (vx p r))) W A B C (centres.map ofCentre) L cert
    hconds ax.window_sel ax.deg_le_two ax.sel_lt hp hA hB
    (fun a ha b hb => List.all_eq_true.mp (List.all_eq_true.mp hcheck a ha) b hb)
  have he : (C.map (shareLocal 12 (sel p (amap P (vx p r))))).sum =
      ((List.range 5).map (fun i => coreShare 12 p (r+(i+start)))).sum := by
    rw [hC,List.map_map]
    congr 1
    apply List.map_congr_left
    intro i hi
    have hi' := List.mem_range.mp hi
    change shareLocal 12 (sel p (amap P (vx p r))) (W.getD (i+start) 0)=_
    rw [frame_window p P r hc hr hP (i+start) (by omega)]
    exact shareLocal_frame p P _ (vx_lt p r) (vx_lt p _) 12
  exact he ▸ hs

#print axioms cert_sound
#print axioms count_choices_share
#print axioms centresOf_canon
#print axioms count_choices_in_snake
end Snake9.LocalWindow.CountPropagationPort95
