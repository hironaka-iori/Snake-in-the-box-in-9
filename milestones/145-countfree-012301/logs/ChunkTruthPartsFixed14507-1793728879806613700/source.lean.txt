import ChunkParts14507
import ChunkTruthTools145
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace Snake9.ChunkData145
open Snake9.InputTree145 (InputTree)
theorem part56_slice : part56.clauses = (((Snake9.LocalWindow.ShareWindow144.raw56 ++ Snake9.LocalWindow.ShareWindow144.raw57)).drop 4).take 127 := by
  rw [part56_clauses]
  rfl
theorem part56_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw56.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw57.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part56 := by
  rw [← part56_build]
  apply build_true_of_slice τ part56 (Snake9.LocalWindow.ShareWindow144.raw56 ++ Snake9.LocalWindow.ShareWindow144.raw57) 4 127 part56_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part56_slice
#print axioms part56_true
theorem part57_slice : part57.clauses = (((Snake9.LocalWindow.ShareWindow144.raw57 ++ Snake9.LocalWindow.ShareWindow144.raw58)).drop 3).take 127 := by
  rw [part57_clauses]
  rfl
theorem part57_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw57.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw58.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part57 := by
  rw [← part57_build]
  apply build_true_of_slice τ part57 (Snake9.LocalWindow.ShareWindow144.raw57 ++ Snake9.LocalWindow.ShareWindow144.raw58) 3 127 part57_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part57_slice
#print axioms part57_true
theorem part58_slice : part58.clauses = (((Snake9.LocalWindow.ShareWindow144.raw58 ++ Snake9.LocalWindow.ShareWindow144.raw59)).drop 3).take 127 := by
  rw [part58_clauses]
  rfl
theorem part58_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw58.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw59.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part58 := by
  rw [← part58_build]
  apply build_true_of_slice τ part58 (Snake9.LocalWindow.ShareWindow144.raw58 ++ Snake9.LocalWindow.ShareWindow144.raw59) 3 127 part58_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part58_slice
#print axioms part58_true
theorem part59_slice : part59.clauses = (((Snake9.LocalWindow.ShareWindow144.raw59 ++ Snake9.LocalWindow.ShareWindow144.raw60)).drop 2).take 127 := by
  rw [part59_clauses]
  rfl
theorem part59_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw59.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw60.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part59 := by
  rw [← part59_build]
  apply build_true_of_slice τ part59 (Snake9.LocalWindow.ShareWindow144.raw59 ++ Snake9.LocalWindow.ShareWindow144.raw60) 2 127 part59_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part59_slice
#print axioms part59_true
theorem part60_slice : part60.clauses = (((Snake9.LocalWindow.ShareWindow144.raw60 ++ Snake9.LocalWindow.ShareWindow144.raw61)).drop 3).take 127 := by
  rw [part60_clauses]
  rfl
theorem part60_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw60.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw61.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part60 := by
  rw [← part60_build]
  apply build_true_of_slice τ part60 (Snake9.LocalWindow.ShareWindow144.raw60 ++ Snake9.LocalWindow.ShareWindow144.raw61) 3 127 part60_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part60_slice
#print axioms part60_true
theorem part61_slice : part61.clauses = (((Snake9.LocalWindow.ShareWindow144.raw61 ++ Snake9.LocalWindow.ShareWindow144.raw62)).drop 2).take 127 := by
  rw [part61_clauses]
  rfl
theorem part61_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw61.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw62.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part61 := by
  rw [← part61_build]
  apply build_true_of_slice τ part61 (Snake9.LocalWindow.ShareWindow144.raw61 ++ Snake9.LocalWindow.ShareWindow144.raw62) 2 127 part61_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part61_slice
#print axioms part61_true
theorem part62_slice : part62.clauses = (((Snake9.LocalWindow.ShareWindow144.raw62 ++ Snake9.LocalWindow.ShareWindow144.raw63)).drop 2).take 127 := by
  rw [part62_clauses]
  rfl
theorem part62_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw62.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw63.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part62 := by
  rw [← part62_build]
  apply build_true_of_slice τ part62 (Snake9.LocalWindow.ShareWindow144.raw62 ++ Snake9.LocalWindow.ShareWindow144.raw63) 2 127 part62_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part62_slice
#print axioms part62_true
theorem part63_slice : part63.clauses = ((Snake9.LocalWindow.ShareWindow144.raw63).drop 1).take 127 := by
  rw [part63_clauses]
  rfl
theorem part63_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw63.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part63 := by
  rw [← part63_build]
  apply build_true_of_slice τ part63 Snake9.LocalWindow.ShareWindow144.raw63 1 127 part63_slice
  exact h0
#print axioms part63_slice
#print axioms part63_true
end Snake9.ChunkData145
