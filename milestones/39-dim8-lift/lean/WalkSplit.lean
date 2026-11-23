import Walk
import CoverDefs
/-! Splitting the cover walk `walkN FULL 0 core` into independent parts (one kernel evaluation per part of
`FULL`), so that no single check evaluates the whole cover CNF.

`walkN_step`: if part `a` walks the core slice `(core.drop d).take n` from index `i`, and the rest `b` walks
`core.drop (d + n)` from `j = i + a.length`, then `a ++ b` walks `core.drop d` from `i`. -/
namespace Dim8Lift.Walk
open Dim8Lift.Cover Dim8Lift.Tab

theorem walkN_head_le : ∀ (b : List (List Int)) (k j : Nat) (c : List Nat) (cs : List (Nat × List Nat)),
    walkN b k ((j, c) :: cs) = true → k ≤ j
  | [], _, _, _, _, h => by simp [walkN] at h
  | f :: fs, k, j, c, cs, h => by
    unfold walkN at h
    by_cases e : k = j
    · omega
    · rw [if_neg e] at h
      by_cases l : k < j
      · omega
      · rw [if_neg l] at h; simp at h

theorem walkN_skip (b : List (List Int)) : ∀ (pre : List (List Int)) (i : Nat) (cb : List (Nat × List Nat)),
    walkN b (i + pre.length) cb = true → walkN (pre ++ b) i cb = true
  | [], i, cb, h => by simpa using h
  | f :: fs, i, [], _ => by cases fs <;> cases b <;> simp [walkN]
  | f :: fs, i, (j, c) :: cs, h => by
    have hl := walkN_head_le b _ j c cs h
    simp only [List.length_cons] at hl h
    have e : i ≠ j := by omega
    have l : i < j := by omega
    show walkN (f :: (fs ++ b)) i ((j, c) :: cs) = true
    unfold walkN; rw [if_neg e, if_pos l]
    exact walkN_skip b fs (i + 1) _ (by rw [show i + 1 + fs.length = i + (fs.length + 1) by omega]; exact h)

theorem walkN_nil_core : ∀ (f : List (List Int)) (i : Nat), walkN f i [] = true
  | [], _ => rfl
  | _ :: _, _ => rfl

theorem walkN_append (b : List (List Int)) : ∀ (a : List (List Int)) (i : Nat) (ca cb : List (Nat × List Nat)),
    walkN a i ca = true → walkN b (i + a.length) cb = true → walkN (a ++ b) i (ca ++ cb) = true
  | [], i, [], cb, _, hb => by simpa using hb
  | [], _, _ :: _, _, ha, _ => by simp [walkN] at ha
  | f :: fs, i, [], cb, _, hb => walkN_skip b (f :: fs) i cb hb
  | f :: fs, i, (j, c) :: cs, cb, ha, hb => by
    unfold walkN at ha
    show walkN (f :: (fs ++ b)) i ((j, c) :: (cs ++ cb)) = true
    have hb' : walkN b (i + 1 + fs.length) cb = true := by
      rw [show i + 1 + fs.length = i + (f :: fs).length by simp; omega]; exact hb
    by_cases e : i = j
    · rw [if_pos e] at ha
      simp only [Bool.and_eq_true] at ha
      unfold walkN; rw [if_pos e]
      simp only [Bool.and_eq_true]
      exact ⟨ha.1, walkN_append b fs (i + 1) cs cb ha.2 hb'⟩
    · rw [if_neg e] at ha
      by_cases l : i < j
      · rw [if_pos l] at ha
        unfold walkN; rw [if_neg e, if_pos l]
        exact walkN_append b fs (i + 1) ((j, c) :: cs) cb ha hb'
      · rw [if_neg l] at ha; simp at ha

/-- one step of a split walk: part `a` takes the core slice `(core.drop d).take n` -/
theorem walkN_step (a b : List (List Int)) (i j : Nat) (core : List (Nat × List Nat)) (d n : Nat)
    (hj : i + a.length = j) (ha : walkN a i ((core.drop d).take n) = true) (hb : walkN b j (core.drop (d + n)) = true) :
    walkN (a ++ b) i (core.drop d) = true := by
  have e : core.drop d = (core.drop d).take n ++ core.drop (d + n) := by
    rw [← List.drop_drop, List.take_append_drop]
  rw [e]; exact walkN_append b a i _ _ ha (hj ▸ hb)

theorem cBlk_append (n : Nat) (a b : List Nat) : cBlk n (a ++ b) = cBlk n a ++ cBlk n b := by
  simp [cBlk]

end Dim8Lift.Walk
