import Port95M60GenericWindow

namespace Snake9.LocalWindow.SplitShare62
open ForcedShare58 ExtendedShare59 CriticalExtension60
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- The newly selected candidate may itself witness a degree violation. -/
def forceCheckPlus (W D : List Nat) : Bool :=
  D.all fun q => (q::W).any fun v =>
    decide (3 ≤ cnt (fun t => (q::W).contains t) (nbrs v))

theorem forced_absent_plus (S : Nat → Bool) (W D : List Nat)
    (hW : ∀ v ∈ W, S v = true)
    (hd : ∀ v, S v = true → cnt S (nbrs v) ≤ 2)
    (hc : forceCheckPlus W D = true) : ∀ q ∈ D, S q = false := by
  intro q hq
  cases he : S q with
  | false => rfl
  | true =>
    have hsel : ∀ x ∈ q::W, S x = true := by
      intro x hx
      rcases List.mem_cons.mp hx with hx | hx
      · simpa [hx] using he
      · exact hW x hx
    obtain ⟨v,hv,hv3⟩ := List.any_eq_true.mp (List.all_eq_true.mp hc q hq)
    have hv3' : 3 ≤ cnt (fun t => (q::W).contains t) (nbrs v) := of_decide_eq_true hv3
    have hm := count_mono (fun t => (q::W).contains t) S (nbrs v)
      (fun x _ hx => hsel x (List.contains_iff.mp hx))
    have hh := hd v (hsel v hv)
    change cnt (fun t => (q::W).contains t) (nbrs v) ≤ cnt S (nbrs v) at hm
    omega

theorem mask_share_of_absent (M mask : Nat) (S : Nat → Bool) (W D C : List Nat)
    (hW : ∀ v ∈ W, S v = true) (ha : ∀ q ∈ D, S q = false)
    (hlt : ∀ v, S v = true → v < 512)
    (hp : supportCheck W C = true) (hmask : maskCheck mask D = true) :
    (C.map (shareLocal M (allowed mask))).sum ≤ (C.map (shareLocal M S)).sum := by
  have hU : ∀ x, S x = true → allowed mask x = true := by
    intro x hx
    have h := List.all_eq_true.mp hmask x (List.mem_range.mpr (hlt x hx))
    cases he : mask.testBit x with
    | false => simp [allowed,he]
    | true =>
      have hh : D.contains x = true := by simpa [he] using h
      have := ha x (List.contains_iff.mp hh)
      simp_all
  apply List.sum_le_sum
  intro x hx
  apply local_share_mono M S _ x hU
  intro k hk
  have h := List.all_eq_true.mp (List.all_eq_true.mp hp x hx) k hk
  have h' : 0 < cnt (fun t => W.contains t) (nbrs (x ^^^ (1 <<< k))) := of_decide_eq_true h
  have hm := count_mono (fun t => W.contains t) S (nbrs (x ^^^ (1 <<< k)))
    (fun t _ ht => hW t (List.contains_iff.mp ht))
  change cnt (fun t => W.contains t) (nbrs (x ^^^ (1 <<< k))) ≤ cnt S (nbrs (x ^^^ (1 <<< k))) at hm
  omega

theorem split_share (S : Nat → Bool) (W D0 D1 C : List Nat) (q mask0 mask1 L : Nat)
    (hW : ∀ v ∈ W, S v = true)
    (hd : ∀ v, S v = true → cnt S (nbrs v) ≤ 2)
    (hlt : ∀ v, S v = true → v < 512)
    (hf0 : forceCheckPlus W D0=true) (hf1 : forceCheckPlus (q::W) D1=true)
    (hp : supportCheck W C=true)
    (hm0 : maskCheck mask0 (q::D0)=true) (hm1 : maskCheck mask1 D1=true)
    (hL0 : L ≤ (C.map (shareLocal 12 (allowed mask0))).sum)
    (hL1 : L ≤ (C.map (shareLocal 12 (allowed mask1))).sum) :
    L ≤ (C.map (shareLocal 12 S)).sum := by
  cases hq : S q with
  | false =>
    apply hL0.trans (mask_share_of_absent 12 mask0 S W (q::D0) C hW ?_ hlt hp hm0)
    intro v hv
    rcases List.mem_cons.mp hv with hv | hv
    · simpa [hv] using hq
    · exact forced_absent_plus S W D0 hW hd hf0 v hv
  | true =>
    have hw1 : ∀ v ∈ q::W, S v=true := by
      intro v hv
      rcases List.mem_cons.mp hv with hv | hv
      · simpa [hv] using hq
      · exact hW v hv
    exact hL1.trans (mask_share_of_absent 12 mask1 S W D1 C hW
      (forced_absent_plus S (q::W) D1 hw1 hd hf1) hlt hp hm1)

theorem split_in_snake {W cs D0 D1 C : List Nat} {q mask0 mask1 L start : Nat}
    (hc : Canon W cs) (hn : 1 ≤ cs.length) (hstart : start+4 ≤ cs.length)
    (hC : C=(List.range 5).map (fun i => W.getD (i+start) 0))
    (hf0 : forceCheckPlus W D0=true) (hf1 : forceCheckPlus (q::W) D1=true)
    (hp : supportCheck W C=true)
    (hm0 : maskCheck mask0 (q::D0)=true) (hm1 : maskCheck mask1 D1=true)
    (hL0 : L ≤ (C.map (shareLocal 12 (allowed mask0))).sum)
    (hL1 : L ≤ (C.map (shareLocal 12 (allowed mask1))).sum)
    {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+cs.length≤m) (hP : ∀ j, j<cs.length → P.fwd (dir p (r+j))=cs.getD j 0) :
    L ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+start)))).sum := by
  have ax := frame_without_count_conditions hc hn p P r hr hP
  have hs := split_share (sel p (amap P (vx p r))) W D0 D1 C q mask0 mask1 L
    ax.window_sel ax.deg_le_two ax.sel_lt hf0 hf1 hp hm0 hm1 hL0 hL1
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

#print axioms forced_absent_plus
#print axioms mask_share_of_absent
#print axioms split_share
#print axioms split_in_snake
end Snake9.LocalWindow.SplitShare62
