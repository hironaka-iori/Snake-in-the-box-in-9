import ReplayParts15006
import ReplayTools150
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayData150
theorem part48_slice : input48.clauses = ((Snake9.LocalWindow.ShareWindow150.raw48 ++ Snake9.LocalWindow.ShareWindow150.raw49).drop 5).take 127 := by
  rw [part48_clauses]
  rfl
theorem part48_true (τ : Nat → Bool)
    (h48 : Snake9.LocalWindow.ShareWindow150.raw48.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h49 : Snake9.LocalWindow.ShareWindow150.raw49.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat150Replay.TreeTrue τ part48 := by
  rw [← part48_build]
  apply build_true_of_slice τ input48 (Snake9.LocalWindow.ShareWindow150.raw48 ++ Snake9.LocalWindow.ShareWindow150.raw49) 5 127 part48_slice
  rw [List.all_append]
  rw [h48, h49]
  rfl
#print axioms part48_true
theorem part49_slice : input49.clauses = ((Snake9.LocalWindow.ShareWindow150.raw49 ++ Snake9.LocalWindow.ShareWindow150.raw50).drop 4).take 127 := by
  rw [part49_clauses]
  rfl
theorem part49_true (τ : Nat → Bool)
    (h49 : Snake9.LocalWindow.ShareWindow150.raw49.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h50 : Snake9.LocalWindow.ShareWindow150.raw50.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat150Replay.TreeTrue τ part49 := by
  rw [← part49_build]
  apply build_true_of_slice τ input49 (Snake9.LocalWindow.ShareWindow150.raw49 ++ Snake9.LocalWindow.ShareWindow150.raw50) 4 127 part49_slice
  rw [List.all_append]
  rw [h49, h50]
  rfl
#print axioms part49_true
theorem part50_slice : input50.clauses = ((Snake9.LocalWindow.ShareWindow150.raw50 ++ Snake9.LocalWindow.ShareWindow150.raw51).drop 4).take 127 := by
  rw [part50_clauses]
  rfl
theorem part50_true (τ : Nat → Bool)
    (h50 : Snake9.LocalWindow.ShareWindow150.raw50.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h51 : Snake9.LocalWindow.ShareWindow150.raw51.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat150Replay.TreeTrue τ part50 := by
  rw [← part50_build]
  apply build_true_of_slice τ input50 (Snake9.LocalWindow.ShareWindow150.raw50 ++ Snake9.LocalWindow.ShareWindow150.raw51) 4 127 part50_slice
  rw [List.all_append]
  rw [h50, h51]
  rfl
#print axioms part50_true
theorem part51_slice : input51.clauses = ((Snake9.LocalWindow.ShareWindow150.raw51 ++ Snake9.LocalWindow.ShareWindow150.raw52).drop 3).take 127 := by
  rw [part51_clauses]
  rfl
theorem part51_true (τ : Nat → Bool)
    (h51 : Snake9.LocalWindow.ShareWindow150.raw51.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h52 : Snake9.LocalWindow.ShareWindow150.raw52.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat150Replay.TreeTrue τ part51 := by
  rw [← part51_build]
  apply build_true_of_slice τ input51 (Snake9.LocalWindow.ShareWindow150.raw51 ++ Snake9.LocalWindow.ShareWindow150.raw52) 3 127 part51_slice
  rw [List.all_append]
  rw [h51, h52]
  rfl
#print axioms part51_true
theorem part52_slice : input52.clauses = ((Snake9.LocalWindow.ShareWindow150.raw52 ++ Snake9.LocalWindow.ShareWindow150.raw53).drop 4).take 127 := by
  rw [part52_clauses]
  rfl
theorem part52_true (τ : Nat → Bool)
    (h52 : Snake9.LocalWindow.ShareWindow150.raw52.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h53 : Snake9.LocalWindow.ShareWindow150.raw53.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat150Replay.TreeTrue τ part52 := by
  rw [← part52_build]
  apply build_true_of_slice τ input52 (Snake9.LocalWindow.ShareWindow150.raw52 ++ Snake9.LocalWindow.ShareWindow150.raw53) 4 127 part52_slice
  rw [List.all_append]
  rw [h52, h53]
  rfl
#print axioms part52_true
theorem part53_slice : input53.clauses = ((Snake9.LocalWindow.ShareWindow150.raw53 ++ Snake9.LocalWindow.ShareWindow150.raw54).drop 3).take 127 := by
  rw [part53_clauses]
  rfl
theorem part53_true (τ : Nat → Bool)
    (h53 : Snake9.LocalWindow.ShareWindow150.raw53.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h54 : Snake9.LocalWindow.ShareWindow150.raw54.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat150Replay.TreeTrue τ part53 := by
  rw [← part53_build]
  apply build_true_of_slice τ input53 (Snake9.LocalWindow.ShareWindow150.raw53 ++ Snake9.LocalWindow.ShareWindow150.raw54) 3 127 part53_slice
  rw [List.all_append]
  rw [h53, h54]
  rfl
#print axioms part53_true
theorem part54_slice : input54.clauses = ((Snake9.LocalWindow.ShareWindow150.raw54 ++ Snake9.LocalWindow.ShareWindow150.raw55).drop 3).take 127 := by
  rw [part54_clauses]
  rfl
theorem part54_true (τ : Nat → Bool)
    (h54 : Snake9.LocalWindow.ShareWindow150.raw54.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h55 : Snake9.LocalWindow.ShareWindow150.raw55.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat150Replay.TreeTrue τ part54 := by
  rw [← part54_build]
  apply build_true_of_slice τ input54 (Snake9.LocalWindow.ShareWindow150.raw54 ++ Snake9.LocalWindow.ShareWindow150.raw55) 3 127 part54_slice
  rw [List.all_append]
  rw [h54, h55]
  rfl
#print axioms part54_true
theorem part55_slice : input55.clauses = ((Snake9.LocalWindow.ShareWindow150.raw55 ++ Snake9.LocalWindow.ShareWindow150.raw56).drop 2).take 127 := by
  rw [part55_clauses]
  rfl
theorem part55_true (τ : Nat → Bool)
    (h55 : Snake9.LocalWindow.ShareWindow150.raw55.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h56 : Snake9.LocalWindow.ShareWindow150.raw56.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat150Replay.TreeTrue τ part55 := by
  rw [← part55_build]
  apply build_true_of_slice τ input55 (Snake9.LocalWindow.ShareWindow150.raw55 ++ Snake9.LocalWindow.ShareWindow150.raw56) 2 127 part55_slice
  rw [List.all_append]
  rw [h55, h56]
  rfl
#print axioms part55_true
end Snake9.ReplayData150
