import ReplayParts15012
import ReplayTools150
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayData150
theorem part96_slice : input96.clauses = ((Snake9.LocalWindow.ShareWindow150.raw96 ++ Snake9.LocalWindow.ShareWindow150.raw97).drop 5).take 127 := by
  rw [part96_clauses]
  rfl
theorem part96_true (τ : Nat → Bool)
    (h96 : Snake9.LocalWindow.ShareWindow150.raw96.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h97 : Snake9.LocalWindow.ShareWindow150.raw97.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat150Replay.TreeTrue τ part96 := by
  rw [← part96_build]
  apply build_true_of_slice τ input96 (Snake9.LocalWindow.ShareWindow150.raw96 ++ Snake9.LocalWindow.ShareWindow150.raw97) 5 127 part96_slice
  rw [List.all_append]
  rw [h96, h97]
  rfl
#print axioms part96_true
theorem part97_slice : input97.clauses = ((Snake9.LocalWindow.ShareWindow150.raw97 ++ Snake9.LocalWindow.ShareWindow150.raw98).drop 4).take 127 := by
  rw [part97_clauses]
  rfl
theorem part97_true (τ : Nat → Bool)
    (h97 : Snake9.LocalWindow.ShareWindow150.raw97.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h98 : Snake9.LocalWindow.ShareWindow150.raw98.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat150Replay.TreeTrue τ part97 := by
  rw [← part97_build]
  apply build_true_of_slice τ input97 (Snake9.LocalWindow.ShareWindow150.raw97 ++ Snake9.LocalWindow.ShareWindow150.raw98) 4 127 part97_slice
  rw [List.all_append]
  rw [h97, h98]
  rfl
#print axioms part97_true
theorem part98_slice : input98.clauses = ((Snake9.LocalWindow.ShareWindow150.raw98 ++ Snake9.LocalWindow.ShareWindow150.raw99).drop 4).take 127 := by
  rw [part98_clauses]
  rfl
theorem part98_true (τ : Nat → Bool)
    (h98 : Snake9.LocalWindow.ShareWindow150.raw98.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h99 : Snake9.LocalWindow.ShareWindow150.raw99.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat150Replay.TreeTrue τ part98 := by
  rw [← part98_build]
  apply build_true_of_slice τ input98 (Snake9.LocalWindow.ShareWindow150.raw98 ++ Snake9.LocalWindow.ShareWindow150.raw99) 4 127 part98_slice
  rw [List.all_append]
  rw [h98, h99]
  rfl
#print axioms part98_true
theorem part99_slice : input99.clauses = ((Snake9.LocalWindow.ShareWindow150.raw99 ++ Snake9.LocalWindow.ShareWindow150.raw100).drop 3).take 127 := by
  rw [part99_clauses]
  rfl
theorem part99_true (τ : Nat → Bool)
    (h99 : Snake9.LocalWindow.ShareWindow150.raw99.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h100 : Snake9.LocalWindow.ShareWindow150.raw100.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat150Replay.TreeTrue τ part99 := by
  rw [← part99_build]
  apply build_true_of_slice τ input99 (Snake9.LocalWindow.ShareWindow150.raw99 ++ Snake9.LocalWindow.ShareWindow150.raw100) 3 127 part99_slice
  rw [List.all_append]
  rw [h99, h100]
  rfl
#print axioms part99_true
theorem part100_slice : input100.clauses = ((Snake9.LocalWindow.ShareWindow150.raw100 ++ Snake9.LocalWindow.ShareWindow150.raw101).drop 4).take 127 := by
  rw [part100_clauses]
  rfl
theorem part100_true (τ : Nat → Bool)
    (h100 : Snake9.LocalWindow.ShareWindow150.raw100.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h101 : Snake9.LocalWindow.ShareWindow150.raw101.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat150Replay.TreeTrue τ part100 := by
  rw [← part100_build]
  apply build_true_of_slice τ input100 (Snake9.LocalWindow.ShareWindow150.raw100 ++ Snake9.LocalWindow.ShareWindow150.raw101) 4 127 part100_slice
  rw [List.all_append]
  rw [h100, h101]
  rfl
#print axioms part100_true
theorem part101_slice : input101.clauses = ((Snake9.LocalWindow.ShareWindow150.raw101 ++ Snake9.LocalWindow.ShareWindow150.raw102).drop 3).take 127 := by
  rw [part101_clauses]
  rfl
theorem part101_true (τ : Nat → Bool)
    (h101 : Snake9.LocalWindow.ShareWindow150.raw101.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h102 : Snake9.LocalWindow.ShareWindow150.raw102.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat150Replay.TreeTrue τ part101 := by
  rw [← part101_build]
  apply build_true_of_slice τ input101 (Snake9.LocalWindow.ShareWindow150.raw101 ++ Snake9.LocalWindow.ShareWindow150.raw102) 3 127 part101_slice
  rw [List.all_append]
  rw [h101, h102]
  rfl
#print axioms part101_true
theorem part102_slice : input102.clauses = ((Snake9.LocalWindow.ShareWindow150.raw102 ++ Snake9.LocalWindow.ShareWindow150.raw103).drop 3).take 127 := by
  rw [part102_clauses]
  rfl
theorem part102_true (τ : Nat → Bool)
    (h102 : Snake9.LocalWindow.ShareWindow150.raw102.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h103 : Snake9.LocalWindow.ShareWindow150.raw103.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat150Replay.TreeTrue τ part102 := by
  rw [← part102_build]
  apply build_true_of_slice τ input102 (Snake9.LocalWindow.ShareWindow150.raw102 ++ Snake9.LocalWindow.ShareWindow150.raw103) 3 127 part102_slice
  rw [List.all_append]
  rw [h102, h103]
  rfl
#print axioms part102_true
theorem part103_slice : input103.clauses = ((Snake9.LocalWindow.ShareWindow150.raw103 ++ Snake9.LocalWindow.ShareWindow150.raw104).drop 2).take 127 := by
  rw [part103_clauses]
  rfl
theorem part103_true (τ : Nat → Bool)
    (h103 : Snake9.LocalWindow.ShareWindow150.raw103.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h104 : Snake9.LocalWindow.ShareWindow150.raw104.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat150Replay.TreeTrue τ part103 := by
  rw [← part103_build]
  apply build_true_of_slice τ input103 (Snake9.LocalWindow.ShareWindow150.raw103 ++ Snake9.LocalWindow.ShareWindow150.raw104) 2 127 part103_slice
  rw [List.all_append]
  rw [h103, h104]
  rfl
#print axioms part103_true
end Snake9.ReplayData150
