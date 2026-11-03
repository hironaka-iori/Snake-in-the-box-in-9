import ReplayParts15008
import ReplayTools150
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayData150
theorem part64_slice : input64.clauses = ((Snake9.LocalWindow.ShareWindow150.raw64 ++ Snake9.LocalWindow.ShareWindow150.raw65).drop 6).take 127 := by
  rw [part64_clauses]
  rfl
theorem part64_true (τ : Nat → Bool)
    (h64 : Snake9.LocalWindow.ShareWindow150.raw64.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h65 : Snake9.LocalWindow.ShareWindow150.raw65.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat150Replay.TreeTrue τ part64 := by
  rw [← part64_build]
  apply build_true_of_slice τ input64 (Snake9.LocalWindow.ShareWindow150.raw64 ++ Snake9.LocalWindow.ShareWindow150.raw65) 6 127 part64_slice
  rw [List.all_append]
  rw [h64, h65]
  rfl
#print axioms part64_true
theorem part65_slice : input65.clauses = ((Snake9.LocalWindow.ShareWindow150.raw65 ++ Snake9.LocalWindow.ShareWindow150.raw66).drop 5).take 127 := by
  rw [part65_clauses]
  rfl
theorem part65_true (τ : Nat → Bool)
    (h65 : Snake9.LocalWindow.ShareWindow150.raw65.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h66 : Snake9.LocalWindow.ShareWindow150.raw66.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat150Replay.TreeTrue τ part65 := by
  rw [← part65_build]
  apply build_true_of_slice τ input65 (Snake9.LocalWindow.ShareWindow150.raw65 ++ Snake9.LocalWindow.ShareWindow150.raw66) 5 127 part65_slice
  rw [List.all_append]
  rw [h65, h66]
  rfl
#print axioms part65_true
theorem part66_slice : input66.clauses = ((Snake9.LocalWindow.ShareWindow150.raw66 ++ Snake9.LocalWindow.ShareWindow150.raw67).drop 5).take 127 := by
  rw [part66_clauses]
  rfl
theorem part66_true (τ : Nat → Bool)
    (h66 : Snake9.LocalWindow.ShareWindow150.raw66.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h67 : Snake9.LocalWindow.ShareWindow150.raw67.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat150Replay.TreeTrue τ part66 := by
  rw [← part66_build]
  apply build_true_of_slice τ input66 (Snake9.LocalWindow.ShareWindow150.raw66 ++ Snake9.LocalWindow.ShareWindow150.raw67) 5 127 part66_slice
  rw [List.all_append]
  rw [h66, h67]
  rfl
#print axioms part66_true
theorem part67_slice : input67.clauses = ((Snake9.LocalWindow.ShareWindow150.raw67 ++ Snake9.LocalWindow.ShareWindow150.raw68).drop 4).take 127 := by
  rw [part67_clauses]
  rfl
theorem part67_true (τ : Nat → Bool)
    (h67 : Snake9.LocalWindow.ShareWindow150.raw67.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h68 : Snake9.LocalWindow.ShareWindow150.raw68.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat150Replay.TreeTrue τ part67 := by
  rw [← part67_build]
  apply build_true_of_slice τ input67 (Snake9.LocalWindow.ShareWindow150.raw67 ++ Snake9.LocalWindow.ShareWindow150.raw68) 4 127 part67_slice
  rw [List.all_append]
  rw [h67, h68]
  rfl
#print axioms part67_true
theorem part68_slice : input68.clauses = ((Snake9.LocalWindow.ShareWindow150.raw68 ++ Snake9.LocalWindow.ShareWindow150.raw69).drop 5).take 127 := by
  rw [part68_clauses]
  rfl
theorem part68_true (τ : Nat → Bool)
    (h68 : Snake9.LocalWindow.ShareWindow150.raw68.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h69 : Snake9.LocalWindow.ShareWindow150.raw69.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat150Replay.TreeTrue τ part68 := by
  rw [← part68_build]
  apply build_true_of_slice τ input68 (Snake9.LocalWindow.ShareWindow150.raw68 ++ Snake9.LocalWindow.ShareWindow150.raw69) 5 127 part68_slice
  rw [List.all_append]
  rw [h68, h69]
  rfl
#print axioms part68_true
theorem part69_slice : input69.clauses = ((Snake9.LocalWindow.ShareWindow150.raw69 ++ Snake9.LocalWindow.ShareWindow150.raw70).drop 4).take 127 := by
  rw [part69_clauses]
  rfl
theorem part69_true (τ : Nat → Bool)
    (h69 : Snake9.LocalWindow.ShareWindow150.raw69.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h70 : Snake9.LocalWindow.ShareWindow150.raw70.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat150Replay.TreeTrue τ part69 := by
  rw [← part69_build]
  apply build_true_of_slice τ input69 (Snake9.LocalWindow.ShareWindow150.raw69 ++ Snake9.LocalWindow.ShareWindow150.raw70) 4 127 part69_slice
  rw [List.all_append]
  rw [h69, h70]
  rfl
#print axioms part69_true
theorem part70_slice : input70.clauses = ((Snake9.LocalWindow.ShareWindow150.raw70 ++ Snake9.LocalWindow.ShareWindow150.raw71).drop 4).take 127 := by
  rw [part70_clauses]
  rfl
theorem part70_true (τ : Nat → Bool)
    (h70 : Snake9.LocalWindow.ShareWindow150.raw70.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h71 : Snake9.LocalWindow.ShareWindow150.raw71.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat150Replay.TreeTrue τ part70 := by
  rw [← part70_build]
  apply build_true_of_slice τ input70 (Snake9.LocalWindow.ShareWindow150.raw70 ++ Snake9.LocalWindow.ShareWindow150.raw71) 4 127 part70_slice
  rw [List.all_append]
  rw [h70, h71]
  rfl
#print axioms part70_true
theorem part71_slice : input71.clauses = ((Snake9.LocalWindow.ShareWindow150.raw71 ++ Snake9.LocalWindow.ShareWindow150.raw72).drop 3).take 127 := by
  rw [part71_clauses]
  rfl
theorem part71_true (τ : Nat → Bool)
    (h71 : Snake9.LocalWindow.ShareWindow150.raw71.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h72 : Snake9.LocalWindow.ShareWindow150.raw72.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat150Replay.TreeTrue τ part71 := by
  rw [← part71_build]
  apply build_true_of_slice τ input71 (Snake9.LocalWindow.ShareWindow150.raw71 ++ Snake9.LocalWindow.ShareWindow150.raw72) 3 127 part71_slice
  rw [List.all_append]
  rw [h71, h72]
  rfl
#print axioms part71_true
end Snake9.ReplayData150
