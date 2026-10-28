import ForcedShare

namespace Snake9.LocalWindow.ForcedShare58
set_option maxHeartbeats 0

/-- Transport a finite forced-absence calculation to any occurrence in a snake. -/
theorem credit_in_snake {W cs D C : List Nat} {L : Nat}
    (hc : Canon W cs) (hlen : cs.length = 8)
    (hC : C = (List.range 5).map (fun i => W.getD (i + 3) 0))
    (hf : forceCheck W D = true) (hp : supportCheck W C = true)
    (hL : L ≤ (C.map (shareLocal 12 (fun x => !D.contains x))).sum)
    {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + 8 ≤ m)
    (hP : ∀ j, j < cs.length → P.fwd (dir p (r + j)) = cs.getD j 0) :
    L ≤ ((List.range 5).map (fun i => coreShare 12 p (r + (i + 3)))).sum := by
  have hr' : r + cs.length ≤ m := by omega
  have hb : ∀ i, i < (List.replicate 7 (0,21)).length →
      ((List.replicate 7 (0,21)).getD i (0,21)).1 ≤ coreAlpha p (r+i+1) ∧
      coreAlpha p (r+i+1) ≤ ((List.replicate 7 (0,21)).getD i (0,21)).2 := by
    intro i hi
    have hi' : i < 7 := by simpa using hi
    have he : (List.replicate 7 (0,21)).getD i (0,21) = (0,21) := by
      interval_cases i <;> decide
    rw [he]
    exact ⟨Nat.zero_le _, coreAlpha_le_21 p (by omega) (by omega)⟩
  have ax := frame_axioms p P r hc (by simpa using hlen.symm) hr' hP hb
  have hs := forced_share 12 (sel p (amap P (vx p r))) W D C
    ax.window_sel ax.deg_le_two hf hp
  have he : (C.map (shareLocal 12 (sel p (amap P (vx p r))))).sum =
      ((List.range 5).map (fun i => coreShare 12 p (r + (i + 3)))).sum := by
    rw [hC, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i hi
    have hi' := List.mem_range.mp hi
    change shareLocal 12 (sel p (amap P (vx p r))) (W.getD (i+3) 0) = _
    rw [frame_window p P r hc hr' hP (i+3) (by omega)]
    exact shareLocal_frame p P _ (vx_lt p r) (vx_lt p _) 12
  exact hL.trans (he ▸ hs)

#print axioms credit_in_snake
end Snake9.LocalWindow.ForcedShare58
