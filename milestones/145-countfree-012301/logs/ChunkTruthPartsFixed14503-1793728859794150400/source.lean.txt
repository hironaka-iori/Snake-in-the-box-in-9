import ChunkParts14503
import ChunkTruthTools145
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace Snake9.ChunkData145
open Snake9.InputTree145 (InputTree)
theorem part24_slice : part24.clauses = (((Snake9.LocalWindow.ShareWindow144.raw24 ++ Snake9.LocalWindow.ShareWindow144.raw25)).drop 5).take 127 := by
  rw [part24_clauses]
  rfl
theorem part24_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw24.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw25.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part24 := by
  rw [← part24_build]
  apply build_true_of_slice τ part24 (Snake9.LocalWindow.ShareWindow144.raw24 ++ Snake9.LocalWindow.ShareWindow144.raw25) 5 127 part24_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part24_slice
#print axioms part24_true
theorem part25_slice : part25.clauses = (((Snake9.LocalWindow.ShareWindow144.raw25 ++ Snake9.LocalWindow.ShareWindow144.raw26)).drop 4).take 127 := by
  rw [part25_clauses]
  rfl
theorem part25_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw25.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw26.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part25 := by
  rw [← part25_build]
  apply build_true_of_slice τ part25 (Snake9.LocalWindow.ShareWindow144.raw25 ++ Snake9.LocalWindow.ShareWindow144.raw26) 4 127 part25_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part25_slice
#print axioms part25_true
theorem part26_slice : part26.clauses = (((Snake9.LocalWindow.ShareWindow144.raw26 ++ Snake9.LocalWindow.ShareWindow144.raw27)).drop 4).take 127 := by
  rw [part26_clauses]
  rfl
theorem part26_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw26.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw27.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part26 := by
  rw [← part26_build]
  apply build_true_of_slice τ part26 (Snake9.LocalWindow.ShareWindow144.raw26 ++ Snake9.LocalWindow.ShareWindow144.raw27) 4 127 part26_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part26_slice
#print axioms part26_true
theorem part27_slice : part27.clauses = (((Snake9.LocalWindow.ShareWindow144.raw27 ++ Snake9.LocalWindow.ShareWindow144.raw28)).drop 3).take 127 := by
  rw [part27_clauses]
  rfl
theorem part27_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw27.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw28.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part27 := by
  rw [← part27_build]
  apply build_true_of_slice τ part27 (Snake9.LocalWindow.ShareWindow144.raw27 ++ Snake9.LocalWindow.ShareWindow144.raw28) 3 127 part27_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part27_slice
#print axioms part27_true
theorem part28_slice : part28.clauses = (((Snake9.LocalWindow.ShareWindow144.raw28 ++ Snake9.LocalWindow.ShareWindow144.raw29)).drop 4).take 127 := by
  rw [part28_clauses]
  rfl
theorem part28_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw28.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw29.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part28 := by
  rw [← part28_build]
  apply build_true_of_slice τ part28 (Snake9.LocalWindow.ShareWindow144.raw28 ++ Snake9.LocalWindow.ShareWindow144.raw29) 4 127 part28_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part28_slice
#print axioms part28_true
theorem part29_slice : part29.clauses = (((Snake9.LocalWindow.ShareWindow144.raw29 ++ Snake9.LocalWindow.ShareWindow144.raw30)).drop 3).take 127 := by
  rw [part29_clauses]
  rfl
theorem part29_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw29.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw30.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part29 := by
  rw [← part29_build]
  apply build_true_of_slice τ part29 (Snake9.LocalWindow.ShareWindow144.raw29 ++ Snake9.LocalWindow.ShareWindow144.raw30) 3 127 part29_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part29_slice
#print axioms part29_true
theorem part30_slice : part30.clauses = (((Snake9.LocalWindow.ShareWindow144.raw30 ++ Snake9.LocalWindow.ShareWindow144.raw31)).drop 3).take 127 := by
  rw [part30_clauses]
  rfl
theorem part30_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw30.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw31.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part30 := by
  rw [← part30_build]
  apply build_true_of_slice τ part30 (Snake9.LocalWindow.ShareWindow144.raw30 ++ Snake9.LocalWindow.ShareWindow144.raw31) 3 127 part30_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part30_slice
#print axioms part30_true
theorem part31_slice : part31.clauses = (((Snake9.LocalWindow.ShareWindow144.raw31 ++ Snake9.LocalWindow.ShareWindow144.raw32)).drop 2).take 127 := by
  rw [part31_clauses]
  rfl
theorem part31_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw31.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw32.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part31 := by
  rw [← part31_build]
  apply build_true_of_slice τ part31 (Snake9.LocalWindow.ShareWindow144.raw31 ++ Snake9.LocalWindow.ShareWindow144.raw32) 2 127 part31_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part31_slice
#print axioms part31_true
end Snake9.ChunkData145
