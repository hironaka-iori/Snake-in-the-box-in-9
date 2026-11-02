import Port95M59MaskShareBridge

namespace Snake9.LocalWindow.CriticalExtension60
open ForcedShare58 ExtendedShare59
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem replicate_getD {α : Type} (a : α) (n k : Nat) :
    (List.replicate n a).getD k a = a := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k => simpa [List.replicate_succ] using ih k

theorem frame_without_count_conditions {W cs : List Nat} (hc : Canon W cs)
    (hn : 1 ≤ cs.length) {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+cs.length ≤ m)
    (hP : ∀ j, j<cs.length → P.fwd (dir p (r+j))=cs.getD j 0) :
    Axioms (sel p (amap P (vx p r))) (frameE p P (vx p r)) W
      (centresOf W (List.replicate (cs.length-1) (0,21))) := by
  apply frame_axioms p P r hc
  · simp; omega
  · exact hr
  · exact hP
  · intro i hi
    have hi' : i < cs.length-1 := by simpa using hi
    rw [replicate_getD]
    exact ⟨Nat.zero_le _,coreAlpha_le_21 p (by omega) (by omega)⟩

theorem share_in_snake {W cs D C : List Nat} {L mask start : Nat}
    (hc : Canon W cs) (hn : 1 ≤ cs.length) (hstart : start+4 ≤ cs.length)
    (hC : C=(List.range 5).map (fun i => W.getD (i+start) 0))
    (hf : forceCheck W D=true) (hp : supportCheck W C=true)
    (hm : maskCheck mask D=true)
    (hL : L ≤ (C.map (shareLocal 12 (allowed mask))).sum)
    {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+cs.length ≤ m)
    (hP : ∀ j, j<cs.length → P.fwd (dir p (r+j))=cs.getD j 0) :
    L ≤ ((List.range 5).map (fun i => coreShare 12 p (r+(i+start)))).sum := by
  have ax := frame_without_count_conditions hc hn p P r hr hP
  have hs := mask_share 12 mask (sel p (amap P (vx p r))) W D C
    ax.window_sel ax.deg_le_two ax.sel_lt hf hp hm
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
  exact hL.trans (he ▸ hs)

/-- Validity control for a proposed longer selected window. -/
theorem cycle_window_forbidden {W cs : List Nat} (hc : Canon W cs)
    (hn : 1 ≤ cs.length) (hne : W ≠ [])
    (hcycle : ∀ v ∈ W, 2 ≤ cnt (fun x => W.contains x) (nbrs v))
    {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+cs.length ≤ m)
    (hP : ∀ j, j<cs.length → P.fwd (dir p (r+j))=cs.getD j 0) : False := by
  have ax := frame_without_count_conditions hc hn p P r hr hP
  obtain ⟨v,hv,ha⟩ := ax.acyclic W hne hcycle
  have := ax.window_sel v hv
  simp_all

#print axioms replicate_getD
#print axioms frame_without_count_conditions
#print axioms share_in_snake
#print axioms cycle_window_forbidden
end Snake9.LocalWindow.CriticalExtension60
