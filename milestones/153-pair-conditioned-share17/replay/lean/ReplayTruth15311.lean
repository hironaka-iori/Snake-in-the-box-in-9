import ReplayParts15311
import ReplayTools153
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayData153
theorem part88_slice : input88.clauses = ((Snake9.LocalWindow.ShareWindow153.raw88 ++ Snake9.LocalWindow.ShareWindow153.raw89).drop 4).take 127 := by
  rw [part88_clauses]
  rfl
theorem part88_true (τ : Nat → Bool)
    (h88 : Snake9.LocalWindow.ShareWindow153.raw88.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h89 : Snake9.LocalWindow.ShareWindow153.raw89.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat153Replay.TreeTrue τ part88 := by
  rw [← part88_build]
  apply build_true_of_slice τ input88 (Snake9.LocalWindow.ShareWindow153.raw88 ++ Snake9.LocalWindow.ShareWindow153.raw89) 4 127 part88_slice
  rw [List.all_append]
  rw [h88, h89]
  rfl
#print axioms part88_true
theorem part89_slice : input89.clauses = ((Snake9.LocalWindow.ShareWindow153.raw89 ++ Snake9.LocalWindow.ShareWindow153.raw90).drop 3).take 127 := by
  rw [part89_clauses]
  rfl
theorem part89_true (τ : Nat → Bool)
    (h89 : Snake9.LocalWindow.ShareWindow153.raw89.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h90 : Snake9.LocalWindow.ShareWindow153.raw90.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat153Replay.TreeTrue τ part89 := by
  rw [← part89_build]
  apply build_true_of_slice τ input89 (Snake9.LocalWindow.ShareWindow153.raw89 ++ Snake9.LocalWindow.ShareWindow153.raw90) 3 127 part89_slice
  rw [List.all_append]
  rw [h89, h90]
  rfl
#print axioms part89_true
theorem part90_slice : input90.clauses = ((Snake9.LocalWindow.ShareWindow153.raw90 ++ Snake9.LocalWindow.ShareWindow153.raw91).drop 3).take 127 := by
  rw [part90_clauses]
  rfl
theorem part90_true (τ : Nat → Bool)
    (h90 : Snake9.LocalWindow.ShareWindow153.raw90.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h91 : Snake9.LocalWindow.ShareWindow153.raw91.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat153Replay.TreeTrue τ part90 := by
  rw [← part90_build]
  apply build_true_of_slice τ input90 (Snake9.LocalWindow.ShareWindow153.raw90 ++ Snake9.LocalWindow.ShareWindow153.raw91) 3 127 part90_slice
  rw [List.all_append]
  rw [h90, h91]
  rfl
#print axioms part90_true
theorem part91_slice : input91.clauses = ((Snake9.LocalWindow.ShareWindow153.raw91 ++ Snake9.LocalWindow.ShareWindow153.raw92).drop 2).take 127 := by
  rw [part91_clauses]
  rfl
theorem part91_true (τ : Nat → Bool)
    (h91 : Snake9.LocalWindow.ShareWindow153.raw91.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h92 : Snake9.LocalWindow.ShareWindow153.raw92.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat153Replay.TreeTrue τ part91 := by
  rw [← part91_build]
  apply build_true_of_slice τ input91 (Snake9.LocalWindow.ShareWindow153.raw91 ++ Snake9.LocalWindow.ShareWindow153.raw92) 2 127 part91_slice
  rw [List.all_append]
  rw [h91, h92]
  rfl
#print axioms part91_true
theorem part92_slice : input92.clauses = ((Snake9.LocalWindow.ShareWindow153.raw92).drop 3).take 90 := by
  rw [part92_clauses]
  rfl
theorem part92_true (τ : Nat → Bool)
    (h92 : Snake9.LocalWindow.ShareWindow153.raw92.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat153Replay.TreeTrue τ part92 := by
  rw [← part92_build]
  apply build_true_of_slice τ input92 (Snake9.LocalWindow.ShareWindow153.raw92) 3 90 part92_slice
  exact h92
#print axioms part92_true
end Snake9.ReplayData153
