import Port95M62SplitShare
namespace Snake9.LocalWindow.NeighbourChoice64
open ForcedShare58 ExtendedShare59 CriticalExtension60 SplitShare62
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def badCheck (T : List Nat) : Bool :=
  T.any fun v => decide (3 ≤ cnt (fun t => T.contains t) (nbrs v))

theorem bad_impossible (S : Nat → Bool) (T : List Nat)
    (hT : ∀ v ∈ T, S v=true) (hd : ∀ v, S v=true → cnt S (nbrs v)≤2)
    (hb : badCheck T=true) : False := by
  obtain ⟨v,hv,h3⟩ := List.any_eq_true.mp hb
  have hh : 3≤cnt (fun t => T.contains t) (nbrs v) := of_decide_eq_true h3
  have hm := count_mono (fun t => T.contains t) S (nbrs v)
    (fun x _ hx => hT x (List.contains_iff.mp hx))
  have hl := hd v (hT v hv)
  change cnt (fun t => T.contains t) (nbrs v)≤cnt S (nbrs v) at hm
  omega

def pairCheck (W A : List Nat) : Bool :=
  A.all fun a => A.all fun b => decide (a=b) || badCheck (a::b::W)

theorem unique_selected (S : Nat → Bool) (W A : List Nat)
    (hW : ∀ v ∈ W, S v=true) (hd : ∀ v, S v=true → cnt S (nbrs v)≤2)
    (hc : pairCheck W A=true) :
    ∀ a∈A, ∀ b∈A, S a=true → S b=true → a=b := by
  intro a ha b hb hsa hsb
  have h := List.all_eq_true.mp (List.all_eq_true.mp hc a ha) b hb
  rcases Bool.or_eq_true_iff.mp h with he | he
  · exact of_decide_eq_true he
  · exfalso
    apply bad_impossible S (a::b::W) ?_ hd he
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with hx | hx | hx
    · simpa [hx] using hsa
    · simpa [hx] using hsb
    · exact hW x hx

def choices (A : List Nat) : List (Option Nat) := none::A.map some
def picked (o : Option Nat) : List Nat := o.toList
def unpicked (A : List Nat) (o : Option Nat) : List Nat :=
  A.filter fun v => !(picked o).contains v

theorem one_choice (S : Nat → Bool) (A : List Nat)
    (hu : ∀ a∈A, ∀ b∈A, S a=true → S b=true → a=b) :
    ∃ o∈choices A, (∀ v∈picked o, S v=true) ∧ (∀ v∈unpicked A o, S v=false) := by
  classical
  by_cases he : ∃ a∈A, S a=true
  · obtain ⟨a,ha,hsa⟩ := he
    refine ⟨some a,?_,?_,?_⟩
    · simp [choices,ha]
    · intro v hv
      have hv' : v=a := by simpa [picked] using hv
      simpa [hv'] using hsa
    · intro v hv
      have hm := List.mem_filter.mp hv
      cases hs : S v with
      | false => rfl
      | true =>
        have hv' := hu v hm.1 a ha hs hsa
        simp [unpicked,picked,hv'] at hv
  · refine ⟨none,by simp [choices],?_,?_⟩
    · simp [picked]
    · intro v hv
      have ha : v∈A := (List.mem_filter.mp hv).1
      cases hs : S v with
      | false => rfl
      | true => exact False.elim (he ⟨v,ha,hs⟩)

def branchCheck (W A B C : List Nat) (L : Nat) (a b : Option Nat)
    (D : List Nat) (mask : Nat) : Bool :=
  let T := picked a ++ picked b ++ W
  badCheck T || (forceCheckPlus T D &&
    maskCheck mask (D ++ unpicked A a ++ unpicked B b) &&
    decide (L ≤ (C.map (shareLocal 12 (allowed mask))).sum))

theorem branch_share (S : Nat → Bool) (W A B C : List Nat) (L : Nat)
    (a b : Option Nat) (D : List Nat) (mask : Nat)
    (hW : ∀ v∈W, S v=true) (hd : ∀ v, S v=true → cnt S (nbrs v)≤2)
    (hlt : ∀ v, S v=true → v<512) (hp : supportCheck W C=true)
    (ha : ∀ v∈picked a, S v=true) (hb : ∀ v∈picked b, S v=true)
    (hna : ∀ v∈unpicked A a, S v=false) (hnb : ∀ v∈unpicked B b, S v=false)
    (hc : branchCheck W A B C L a b D mask=true) :
    L ≤ (C.map (shareLocal 12 S)).sum := by
  have hT : ∀ v∈picked a ++ picked b ++ W, S v=true := by
    intro v hv
    simp only [List.mem_append] at hv
    rcases hv with (hv | hv) | hv
    · exact ha v hv
    · exact hb v hv
    · exact hW v hv
  rcases Bool.or_eq_true_iff.mp hc with hc | hc
  · exact False.elim (bad_impossible S _ hT hd hc)
  · obtain ⟨hfm,hL⟩ := Bool.and_eq_true_iff.mp hc
    obtain ⟨hf,hm⟩ := Bool.and_eq_true_iff.mp hfm
    have hL' := of_decide_eq_true hL
    apply hL'.trans (mask_share_of_absent 12 mask S W
      (D ++ unpicked A a ++ unpicked B b) C hW ?_ hlt hp hm)
    intro v hv
    simp only [List.mem_append] at hv
    rcases hv with (hv | hv) | hv
    · exact forced_absent_plus S _ D hT hd hf v hv
    · exact hna v hv
    · exact hnb v hv

theorem all_choices_share (S : Nat → Bool) (W A B C : List Nat) (L : Nat)
    (cert : Option Nat → Option Nat → List Nat × Nat)
    (hW : ∀ v∈W, S v=true) (hd : ∀ v, S v=true → cnt S (nbrs v)≤2)
    (hlt : ∀ v, S v=true → v<512) (hp : supportCheck W C=true)
    (hA : pairCheck W A=true) (hB : pairCheck W B=true)
    (hc : ∀ a∈choices A, ∀ b∈choices B,
      branchCheck W A B C L a b (cert a b).1 (cert a b).2=true) :
    L ≤ (C.map (shareLocal 12 S)).sum := by
  obtain ⟨a,ha,hsa,hna⟩ := one_choice S A (unique_selected S W A hW hd hA)
  obtain ⟨b,hb,hsb,hnb⟩ := one_choice S B (unique_selected S W B hW hd hB)
  exact branch_share S W A B C L a b (cert a b).1 (cert a b).2
    hW hd hlt hp hsa hsb hna hnb (hc a ha b hb)

theorem neighbour_in_snake {W cs A B C : List Nat} {L start : Nat}
    (cert : Option Nat → Option Nat → List Nat × Nat)
    (hc : Canon W cs) (hn : 1≤cs.length) (hstart : start+4≤cs.length)
    (hC : C=(List.range 5).map (fun i => W.getD (i+start) 0))
    (hp : supportCheck W C=true) (hA : pairCheck W A=true) (hB : pairCheck W B=true)
    (hcheck : (choices A).all (fun a => (choices B).all (fun b =>
      branchCheck W A B C L a b (cert a b).1 (cert a b).2))=true)
    {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+cs.length≤m) (hP : ∀ j, j<cs.length → P.fwd (dir p (r+j))=cs.getD j 0) :
    L≤((List.range 5).map (fun i => coreShare 12 p (r+(i+start)))).sum := by
  have ax := frame_without_count_conditions hc hn p P r hr hP
  have hs := all_choices_share (sel p (amap P (vx p r))) W A B C L cert
    ax.window_sel ax.deg_le_two ax.sel_lt hp hA hB
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

#print axioms bad_impossible
#print axioms unique_selected
#print axioms one_choice
#print axioms branch_share
#print axioms all_choices_share
#print axioms neighbour_in_snake
end Snake9.LocalWindow.NeighbourChoice64
