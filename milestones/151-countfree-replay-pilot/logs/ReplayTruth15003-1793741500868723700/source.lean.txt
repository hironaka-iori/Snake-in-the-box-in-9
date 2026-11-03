import ReplayParts15003
import ReplayTools150
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayData150
theorem part24_slice : input24.clauses = ((Snake9.LocalWindow.ShareWindow150.raw24 ++ Snake9.LocalWindow.ShareWindow150.raw25).drop 5).take 127 := by
  rw [part24_clauses]
  rfl
theorem part24_true (τ : Nat → Bool)
    (h24 : Snake9.LocalWindow.ShareWindow150.raw24.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h25 : Snake9.LocalWindow.ShareWindow150.raw25.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat150Replay.TreeTrue τ part24 := by
  rw [← part24_build]
  apply build_true_of_slice τ input24 (Snake9.LocalWindow.ShareWindow150.raw24 ++ Snake9.LocalWindow.ShareWindow150.raw25) 5 127 part24_slice
  rw [List.all_append]
  rw [h24, h25]
  rfl
#print axioms part24_true
theorem part25_slice : input25.clauses = ((Snake9.LocalWindow.ShareWindow150.raw25 ++ Snake9.LocalWindow.ShareWindow150.raw26).drop 4).take 127 := by
  rw [part25_clauses]
  rfl
theorem part25_true (τ : Nat → Bool)
    (h25 : Snake9.LocalWindow.ShareWindow150.raw25.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h26 : Snake9.LocalWindow.ShareWindow150.raw26.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat150Replay.TreeTrue τ part25 := by
  rw [← part25_build]
  apply build_true_of_slice τ input25 (Snake9.LocalWindow.ShareWindow150.raw25 ++ Snake9.LocalWindow.ShareWindow150.raw26) 4 127 part25_slice
  rw [List.all_append]
  rw [h25, h26]
  rfl
#print axioms part25_true
theorem part26_slice : input26.clauses = ((Snake9.LocalWindow.ShareWindow150.raw26 ++ Snake9.LocalWindow.ShareWindow150.raw27).drop 4).take 127 := by
  rw [part26_clauses]
  rfl
theorem part26_true (τ : Nat → Bool)
    (h26 : Snake9.LocalWindow.ShareWindow150.raw26.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h27 : Snake9.LocalWindow.ShareWindow150.raw27.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat150Replay.TreeTrue τ part26 := by
  rw [← part26_build]
  apply build_true_of_slice τ input26 (Snake9.LocalWindow.ShareWindow150.raw26 ++ Snake9.LocalWindow.ShareWindow150.raw27) 4 127 part26_slice
  rw [List.all_append]
  rw [h26, h27]
  rfl
#print axioms part26_true
theorem part27_slice : input27.clauses = ((Snake9.LocalWindow.ShareWindow150.raw27 ++ Snake9.LocalWindow.ShareWindow150.raw28).drop 3).take 127 := by
  rw [part27_clauses]
  rfl
theorem part27_true (τ : Nat → Bool)
    (h27 : Snake9.LocalWindow.ShareWindow150.raw27.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h28 : Snake9.LocalWindow.ShareWindow150.raw28.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat150Replay.TreeTrue τ part27 := by
  rw [← part27_build]
  apply build_true_of_slice τ input27 (Snake9.LocalWindow.ShareWindow150.raw27 ++ Snake9.LocalWindow.ShareWindow150.raw28) 3 127 part27_slice
  rw [List.all_append]
  rw [h27, h28]
  rfl
#print axioms part27_true
theorem part28_slice : input28.clauses = ((Snake9.LocalWindow.ShareWindow150.raw28 ++ Snake9.LocalWindow.ShareWindow150.raw29).drop 4).take 127 := by
  rw [part28_clauses]
  rfl
theorem part28_true (τ : Nat → Bool)
    (h28 : Snake9.LocalWindow.ShareWindow150.raw28.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h29 : Snake9.LocalWindow.ShareWindow150.raw29.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat150Replay.TreeTrue τ part28 := by
  rw [← part28_build]
  apply build_true_of_slice τ input28 (Snake9.LocalWindow.ShareWindow150.raw28 ++ Snake9.LocalWindow.ShareWindow150.raw29) 4 127 part28_slice
  rw [List.all_append]
  rw [h28, h29]
  rfl
#print axioms part28_true
theorem part29_slice : input29.clauses = ((Snake9.LocalWindow.ShareWindow150.raw29 ++ Snake9.LocalWindow.ShareWindow150.raw30).drop 3).take 127 := by
  rw [part29_clauses]
  rfl
theorem part29_true (τ : Nat → Bool)
    (h29 : Snake9.LocalWindow.ShareWindow150.raw29.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h30 : Snake9.LocalWindow.ShareWindow150.raw30.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat150Replay.TreeTrue τ part29 := by
  rw [← part29_build]
  apply build_true_of_slice τ input29 (Snake9.LocalWindow.ShareWindow150.raw29 ++ Snake9.LocalWindow.ShareWindow150.raw30) 3 127 part29_slice
  rw [List.all_append]
  rw [h29, h30]
  rfl
#print axioms part29_true
theorem part30_slice : input30.clauses = ((Snake9.LocalWindow.ShareWindow150.raw30 ++ Snake9.LocalWindow.ShareWindow150.raw31).drop 3).take 127 := by
  rw [part30_clauses]
  rfl
theorem part30_true (τ : Nat → Bool)
    (h30 : Snake9.LocalWindow.ShareWindow150.raw30.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h31 : Snake9.LocalWindow.ShareWindow150.raw31.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat150Replay.TreeTrue τ part30 := by
  rw [← part30_build]
  apply build_true_of_slice τ input30 (Snake9.LocalWindow.ShareWindow150.raw30 ++ Snake9.LocalWindow.ShareWindow150.raw31) 3 127 part30_slice
  rw [List.all_append]
  rw [h30, h31]
  rfl
#print axioms part30_true
theorem part31_slice : input31.clauses = ((Snake9.LocalWindow.ShareWindow150.raw31 ++ Snake9.LocalWindow.ShareWindow150.raw32).drop 2).take 127 := by
  rw [part31_clauses]
  rfl
theorem part31_true (τ : Nat → Bool)
    (h31 : Snake9.LocalWindow.ShareWindow150.raw31.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h32 : Snake9.LocalWindow.ShareWindow150.raw32.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat150Replay.TreeTrue τ part31 := by
  rw [← part31_build]
  apply build_true_of_slice τ input31 (Snake9.LocalWindow.ShareWindow150.raw31 ++ Snake9.LocalWindow.ShareWindow150.raw32) 2 127 part31_slice
  rw [List.all_append]
  rw [h31, h32]
  rfl
#print axioms part31_true
end Snake9.ReplayData150
