import Port95M59ExtendedShareBridge

namespace Snake9.LocalWindow.ExtendedShare59
open ForcedShare58
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def allowed (mask x : Nat) : Bool := !(mask.testBit x)
def maskCheck (mask : Nat) (D : List Nat) : Bool :=
  (List.range 512).all fun x => !(mask.testBit x) || D.contains x

theorem mask_share (M mask : Nat) (S : Nat → Bool) (W D C : List Nat)
    (hW : ∀ v ∈ W, S v = true)
    (hd : ∀ v, S v = true → cnt S (nbrs v) ≤ 2)
    (hlt : ∀ v, S v = true → v < 512)
    (hf : forceCheck W D = true) (hp : supportCheck W C = true)
    (hmask : maskCheck mask D = true) :
    (C.map (shareLocal M (allowed mask))).sum ≤ (C.map (shareLocal M S)).sum := by
  have ha := forced_absent S W D hW hd hf
  have hU : ∀ x, S x = true → allowed mask x = true := by
    intro x hx
    have h := List.all_eq_true.mp hmask x (List.mem_range.mpr (hlt x hx))
    cases he : mask.testBit x with
    | false => simp [allowed, he]
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
  have hc := count_mono (fun t => W.contains t) S (nbrs (x ^^^ (1 <<< k))) (by
    intro t _ ht
    exact hW t (List.contains_iff.mp ht))
  change cnt (fun t => W.contains t) (nbrs (x ^^^ (1 <<< k))) ≤ cnt S (nbrs (x ^^^ (1 <<< k))) at hc
  omega

theorem mask_credit_in_snake {W cs D C : List Nat} {L mask start : Nat}
    (hc : Canon W cs) (hlen : cs.length = 9) (hstart : start+4 ≤ 9)
    (hC : C = (List.range 5).map (fun i => W.getD (i + start) 0))
    (hf : forceCheck W D = true) (hp : supportCheck W C = true)
    (hmask : maskCheck mask D = true)
    (hL : L ≤ (C.map (shareLocal 12 (allowed mask))).sum)
    {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 9 ≤ m)
    (hP : ∀ j, j < cs.length → P.fwd (dir p (r+j)) = cs.getD j 0) :
    L ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+start)))).sum := by
  have hr' : r+cs.length ≤ m := by omega
  have hb : ∀ i, i < (List.replicate 8 (0,21)).length →
      ((List.replicate 8 (0,21)).getD i (0,21)).1 ≤ coreAlpha p (r+i+1) ∧
      coreAlpha p (r+i+1) ≤ ((List.replicate 8 (0,21)).getD i (0,21)).2 := by
    intro i hi
    have hi' : i < 8 := by simpa using hi
    have he : (List.replicate 8 (0,21)).getD i (0,21) = (0,21) := by
      interval_cases i <;> decide
    rw [he]
    exact ⟨Nat.zero_le _, coreAlpha_le_21 p (by omega) (by omega)⟩
  have ax := frame_axioms p P r hc (by simpa using hlen.symm) hr' hP hb
  have hs := mask_share 12 mask (sel p (amap P (vx p r))) W D C
    ax.window_sel ax.deg_le_two ax.sel_lt hf hp hmask
  have he : (C.map (shareLocal 12 (sel p (amap P (vx p r))))).sum =
      ((List.range 5).map (fun i => coreShare 12 p (r+(i+start)))).sum := by
    rw [hC,List.map_map]
    congr 1
    apply List.map_congr_left
    intro i hi
    have hi' := List.mem_range.mp hi
    change shareLocal 12 (sel p (amap P (vx p r))) (W.getD (i+start) 0) = _
    rw [frame_window p P r hc hr' hP (i+start) (by omega)]
    exact shareLocal_frame p P _ (vx_lt p r) (vx_lt p _) 12
  exact hL.trans (he ▸ hs)

#print axioms mask_share
#print axioms mask_credit_in_snake
end Snake9.LocalWindow.ExtendedShare59
