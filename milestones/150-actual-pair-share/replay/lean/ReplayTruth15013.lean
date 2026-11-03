import ReplayParts15013
import ReplayTools150
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayData150
theorem part104_slice : input104.clauses = ((Snake9.LocalWindow.ShareWindow150.raw104 ++ Snake9.LocalWindow.ShareWindow150.raw105).drop 4).take 127 := by
  rw [part104_clauses]
  rfl
theorem part104_true (τ : Nat → Bool)
    (h104 : Snake9.LocalWindow.ShareWindow150.raw104.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h105 : Snake9.LocalWindow.ShareWindow150.raw105.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat150Replay.TreeTrue τ part104 := by
  rw [← part104_build]
  apply build_true_of_slice τ input104 (Snake9.LocalWindow.ShareWindow150.raw104 ++ Snake9.LocalWindow.ShareWindow150.raw105) 4 127 part104_slice
  rw [List.all_append]
  rw [h104, h105]
  rfl
#print axioms part104_true
theorem part105_slice : input105.clauses = ((Snake9.LocalWindow.ShareWindow150.raw105 ++ Snake9.LocalWindow.ShareWindow150.raw106).drop 3).take 127 := by
  rw [part105_clauses]
  rfl
theorem part105_true (τ : Nat → Bool)
    (h105 : Snake9.LocalWindow.ShareWindow150.raw105.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h106 : Snake9.LocalWindow.ShareWindow150.raw106.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat150Replay.TreeTrue τ part105 := by
  rw [← part105_build]
  apply build_true_of_slice τ input105 (Snake9.LocalWindow.ShareWindow150.raw105 ++ Snake9.LocalWindow.ShareWindow150.raw106) 3 127 part105_slice
  rw [List.all_append]
  rw [h105, h106]
  rfl
#print axioms part105_true
theorem part106_slice : input106.clauses = ((Snake9.LocalWindow.ShareWindow150.raw106).drop 3).take 84 := by
  rw [part106_clauses]
  rfl
theorem part106_true (τ : Nat → Bool)
    (h106 : Snake9.LocalWindow.ShareWindow150.raw106.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat150Replay.TreeTrue τ part106 := by
  rw [← part106_build]
  apply build_true_of_slice τ input106 (Snake9.LocalWindow.ShareWindow150.raw106) 3 84 part106_slice
  exact h106
#print axioms part106_true
end Snake9.ReplayData150
