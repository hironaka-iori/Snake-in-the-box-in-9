import CountWindowBridge
import ParallelShareShapeBridge
import WindowAutomatonK6R34C7WData
import ShareBridge

/-! Exact coverage of the two-centre table in the conditional 231 chain.
The four concrete refutations remain explicit until their replay build completes.
-/
namespace Snake9.CountWindowPairs231
open LocalWindow DirectionWindow WindowAutomaton CountWindowBridge
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

def keys : List IntervalKey :=
  [([0,1,2], [(1,1),(1,1)]), ([0,1,2], [(1,1),(2,2)]),
   ([0,1,2], [(1,1),(3,3)]), ([0,1,2], [(1,1),(4,4)])]

theorem shape_checked : allRGS 3 0 (fun ds =>
    !inducedPattern ds || decide (ds = [0,1,2])) = true := by decide +kernel

theorem shape {m : Nat} (p : Snake m) (r : Nat) (hr : r + 3 ≤ m) :
    canon (dsOf p r 3) = [0,1,2] := by
  have h := allRGS_spec 3 0 _ shape_checked (canon (dsOf p r 3))
    (by simp [length_canon, dsOf]) (canon_isRGS _)
  have hind : inducedPattern (canon (dsOf p r 3)) = true := by
    rw [inducedPattern_canon, ← ParallelShareShapeBridge.blockList_eq_dsOf p r 3 hr]
    exact snake_inducedPattern_block p r 3 hr
  simpa [hind] using h

theorem reverse_shape {m : Nat} (p : Snake m) (r : Nat) (hr : r + 3 ≤ m) :
    canon (dsOf p r 3).reverse = [0,1,2] := by
  rw [← dsOf_rev p r 3 hr]
  exact shape (revSnake p) (m - r - 3) (by omega)

theorem table_checked : allBelow 8 (fun a => allBelow 8 (fun b =>
    !wforbK6R34C7W [0,1,2] [a+1,b+1] ||
      intervalHit 8 keys [0,1,2] [a+1,b+1] ||
      intervalHit 8 keys [0,1,2] [b+1,a+1])) = true := by decide +kernel

theorem coreAlpha_pos {m : Nat} (p : Snake m) (j : Nat) (hm : j ≤ m) :
    1 ≤ coreAlpha p j := by
  rw [← countSeq_eq_coreAlpha p j hm, countSeq_eq p j (by omega)]
  exact SquareIncidence.localAlpha_positive p _

theorem no_pair_window (h : AllRefutedIntervals keys) {m : Nat} (p : Snake m)
    (r : Nat) (hr : r + 3 ≤ m) :
    wforbK6R34C7W (dsOf p r 3) (symsK p 8 r 3) = false := by
  let a := symK 8 (coreAlpha p (r+1))
  let b := symK 8 (coreAlpha p (r+2))
  have ha : 1 ≤ a := symK_ge_one 8 _ (by decide) (coreAlpha_pos p (r+1) (by omega))
  have hb : 1 ≤ b := symK_ge_one 8 _ (by decide) (coreAlpha_pos p (r+2) (by omega))
  have ha8 : a ≤ 8 := symK_le_K _ _
  have hb8 : b ≤ 8 := symK_le_K _ _
  have ht := allBelow_spec 8 _ (allBelow_spec 8 _ table_checked (a-1) (by omega)) (b-1) (by omega)
  rw [show a - 1 + 1 = a by omega, show b - 1 + 1 = b by omega] at ht
  have hf := no_interval_hit h p r 3 (by decide) hr (K := 8)
  have hr' := no_reverse_interval_hit h p r 3 (by decide) hr (K := 8)
  have hs := shape p r hr
  have hsr := reverse_shape p r hr
  have hf' : intervalHit 8 keys [0,1,2] [a,b] = false := by
    simpa only [intervalHit, hs] using hf
  have hr'' : intervalHit 8 keys [0,1,2] [b,a] = false := by
    simpa only [intervalHit, hsr] using hr'
  rw [hf', hr''] at ht
  have ht' : wforbK6R34C7W [0,1,2] [a,b] = false := by simpa using ht
  simpa only [wforbK6R34C7W, wshK6R34C7W, hs, hsr] using ht'

/-- Exactly the `hw2` premise of the existing conditional 231 theorem. -/
theorem hw2_of_pairs (h : AllRefutedIntervals keys) {m : Nat} (p : Snake m) :
    ∀ r, r + 3 ≤ m → wforbK6R34C7W [pathDir p r, pathDir p (r+1), pathDir p (r+2)]
      [symK 8 (countSeq p (r+1)), symK 8 (countSeq p (r+2))] = false := by
  intro r hr
  rw [countSeq_eq_coreAlpha p (r+1) (by omega), countSeq_eq_coreAlpha p (r+2) (by omega),
    pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega), pathDir_eq_dir p (by omega)]
  exact no_pair_window h p r hr

#print axioms table_checked
#print axioms no_pair_window
#print axioms hw2_of_pairs
end Snake9.CountWindowPairs231
