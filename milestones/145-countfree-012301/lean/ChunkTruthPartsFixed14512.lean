import ChunkParts14512
import ChunkTruthTools145
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace Snake9.ChunkData145
open Snake9.InputTree145 (InputTree)
theorem part96_slice : part96.clauses = (((Snake9.LocalWindow.ShareWindow144.raw96 ++ Snake9.LocalWindow.ShareWindow144.raw97)).drop 5).take 127 := by
  rw [part96_clauses]
  rfl
theorem part96_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw96.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw97.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part96 := by
  rw [← part96_build]
  apply build_true_of_slice τ part96 (Snake9.LocalWindow.ShareWindow144.raw96 ++ Snake9.LocalWindow.ShareWindow144.raw97) 5 127 part96_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part96_slice
#print axioms part96_true
theorem part97_slice : part97.clauses = (((Snake9.LocalWindow.ShareWindow144.raw97 ++ Snake9.LocalWindow.ShareWindow144.raw98)).drop 4).take 127 := by
  rw [part97_clauses]
  rfl
theorem part97_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw97.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw98.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part97 := by
  rw [← part97_build]
  apply build_true_of_slice τ part97 (Snake9.LocalWindow.ShareWindow144.raw97 ++ Snake9.LocalWindow.ShareWindow144.raw98) 4 127 part97_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part97_slice
#print axioms part97_true
theorem part98_slice : part98.clauses = (((Snake9.LocalWindow.ShareWindow144.raw98 ++ Snake9.LocalWindow.ShareWindow144.raw99)).drop 4).take 127 := by
  rw [part98_clauses]
  rfl
theorem part98_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw98.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw99.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part98 := by
  rw [← part98_build]
  apply build_true_of_slice τ part98 (Snake9.LocalWindow.ShareWindow144.raw98 ++ Snake9.LocalWindow.ShareWindow144.raw99) 4 127 part98_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part98_slice
#print axioms part98_true
theorem part99_slice : part99.clauses = (((Snake9.LocalWindow.ShareWindow144.raw99 ++ Snake9.LocalWindow.ShareWindow144.raw100)).drop 3).take 127 := by
  rw [part99_clauses]
  rfl
theorem part99_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw99.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw100.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part99 := by
  rw [← part99_build]
  apply build_true_of_slice τ part99 (Snake9.LocalWindow.ShareWindow144.raw99 ++ Snake9.LocalWindow.ShareWindow144.raw100) 3 127 part99_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part99_slice
#print axioms part99_true
theorem part100_slice : part100.clauses = (((Snake9.LocalWindow.ShareWindow144.raw100 ++ Snake9.LocalWindow.ShareWindow144.raw101)).drop 4).take 127 := by
  rw [part100_clauses]
  rfl
theorem part100_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw100.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw101.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part100 := by
  rw [← part100_build]
  apply build_true_of_slice τ part100 (Snake9.LocalWindow.ShareWindow144.raw100 ++ Snake9.LocalWindow.ShareWindow144.raw101) 4 127 part100_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part100_slice
#print axioms part100_true
theorem part101_slice : part101.clauses = (((Snake9.LocalWindow.ShareWindow144.raw101 ++ Snake9.LocalWindow.ShareWindow144.raw102)).drop 3).take 127 := by
  rw [part101_clauses]
  rfl
theorem part101_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw101.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw102.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part101 := by
  rw [← part101_build]
  apply build_true_of_slice τ part101 (Snake9.LocalWindow.ShareWindow144.raw101 ++ Snake9.LocalWindow.ShareWindow144.raw102) 3 127 part101_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part101_slice
#print axioms part101_true
theorem part102_slice : part102.clauses = (((Snake9.LocalWindow.ShareWindow144.raw102 ++ Snake9.LocalWindow.ShareWindow144.raw103)).drop 3).take 127 := by
  rw [part102_clauses]
  rfl
theorem part102_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw102.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw103.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part102 := by
  rw [← part102_build]
  apply build_true_of_slice τ part102 (Snake9.LocalWindow.ShareWindow144.raw102 ++ Snake9.LocalWindow.ShareWindow144.raw103) 3 127 part102_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part102_slice
#print axioms part102_true
theorem part103_slice : part103.clauses = ((Snake9.LocalWindow.ShareWindow144.raw103).drop 2).take 38 := by
  rw [part103_clauses]
  rfl
theorem part103_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw103.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part103 := by
  rw [← part103_build]
  apply build_true_of_slice τ part103 Snake9.LocalWindow.ShareWindow144.raw103 2 38 part103_slice
  exact h0
#print axioms part103_slice
#print axioms part103_true
end Snake9.ChunkData145
