import LocalWindowBridge
import Mathlib.Tactic

namespace Snake9.LocalWindow.JointTags

/-- Exact singleton-count preservation for an individual canonical centre.
The original bridge uses this equality only inside independent interval bounds;
exposing it permits a joint sum over several centres. -/
theorem frame_count {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    {W ds : List Nat} (hc : Canon W ds) (hr : r+ds.length ≤ m)
    (hP : ∀ j, j < ds.length → P.fwd (dir p (r+j)) = ds.getD j 0)
    (i : Nat) (hi : i+1 < ds.length) :
    absentCorners (sel p (amap P (vx p r))) (W.getD (i+1) 0)
      (dirOfStep (W.getD i 0) (W.getD (i+1) 0))
      (dirOfStep (W.getD (i+1) 0) (W.getD (i+2) 0)) =
        coreAlpha p (r+i+1) := by
  have e1 : dirOfStep (W.getD i 0) (W.getD (i+1) 0) = P.fwd (dir p (r+i)) := by
    rw [hc.step i (by omega), dirOfStep_xor, hP i (by omega)]
  have e2 : dirOfStep (W.getD (i+1) 0) (W.getD (i+2) 0) = P.fwd (dir p (r+i+1)) := by
    rw [show i+2 = i+1+1 from rfl, hc.step (i+1) (by omega), dirOfStep_xor]
    exact (hP (i+1) hi).symm
  have e3 : W.getD (i+1) 0 = amap P (vx p r) (vx p (r+i+1)) :=
    frame_window p P r hc hr hP (i+1) (by omega)
  rw [e1,e2,e3]
  have h := frame_absent_eq p P (vx p r) (vx_lt p r)
    (k := r+i+1) (by omega) (by omega)
  rw [show r+i+1-1 = r+i by omega] at h
  rw [h, singCount_frame p P _ (vx_lt p r) (vx_lt p _)]
  rfl

#print axioms frame_count
end Snake9.LocalWindow.JointTags
