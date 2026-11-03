import ChunkParts14501
import ChunkTruthTools145
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace Snake9.ChunkData145
open Snake9.InputTree145 (InputTree)
theorem part8_slice : part8.clauses = (((Snake9.LocalWindow.ShareWindow144.raw8 ++ Snake9.LocalWindow.ShareWindow144.raw9)).drop 6).take 127 := by
  rw [part8_clauses]
  rfl
theorem part8_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw8.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw9.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part8 := by
  rw [← part8_build]
  apply build_true_of_slice τ part8 (Snake9.LocalWindow.ShareWindow144.raw8 ++ Snake9.LocalWindow.ShareWindow144.raw9) 6 127 part8_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part8_slice
#print axioms part8_true
theorem part9_slice : part9.clauses = (((Snake9.LocalWindow.ShareWindow144.raw9 ++ Snake9.LocalWindow.ShareWindow144.raw10)).drop 5).take 127 := by
  rw [part9_clauses]
  rfl
theorem part9_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw9.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw10.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part9 := by
  rw [← part9_build]
  apply build_true_of_slice τ part9 (Snake9.LocalWindow.ShareWindow144.raw9 ++ Snake9.LocalWindow.ShareWindow144.raw10) 5 127 part9_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part9_slice
#print axioms part9_true
theorem part10_slice : part10.clauses = (((Snake9.LocalWindow.ShareWindow144.raw10 ++ Snake9.LocalWindow.ShareWindow144.raw11)).drop 5).take 127 := by
  rw [part10_clauses]
  rfl
theorem part10_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw10.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw11.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part10 := by
  rw [← part10_build]
  apply build_true_of_slice τ part10 (Snake9.LocalWindow.ShareWindow144.raw10 ++ Snake9.LocalWindow.ShareWindow144.raw11) 5 127 part10_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part10_slice
#print axioms part10_true
theorem part11_slice : part11.clauses = (((Snake9.LocalWindow.ShareWindow144.raw11 ++ Snake9.LocalWindow.ShareWindow144.raw12)).drop 4).take 127 := by
  rw [part11_clauses]
  rfl
theorem part11_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw11.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw12.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part11 := by
  rw [← part11_build]
  apply build_true_of_slice τ part11 (Snake9.LocalWindow.ShareWindow144.raw11 ++ Snake9.LocalWindow.ShareWindow144.raw12) 4 127 part11_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part11_slice
#print axioms part11_true
theorem part12_slice : part12.clauses = (((Snake9.LocalWindow.ShareWindow144.raw12 ++ Snake9.LocalWindow.ShareWindow144.raw13)).drop 5).take 127 := by
  rw [part12_clauses]
  rfl
theorem part12_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw12.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw13.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part12 := by
  rw [← part12_build]
  apply build_true_of_slice τ part12 (Snake9.LocalWindow.ShareWindow144.raw12 ++ Snake9.LocalWindow.ShareWindow144.raw13) 5 127 part12_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part12_slice
#print axioms part12_true
theorem part13_slice : part13.clauses = (((Snake9.LocalWindow.ShareWindow144.raw13 ++ Snake9.LocalWindow.ShareWindow144.raw14)).drop 4).take 127 := by
  rw [part13_clauses]
  rfl
theorem part13_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw13.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw14.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part13 := by
  rw [← part13_build]
  apply build_true_of_slice τ part13 (Snake9.LocalWindow.ShareWindow144.raw13 ++ Snake9.LocalWindow.ShareWindow144.raw14) 4 127 part13_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part13_slice
#print axioms part13_true
theorem part14_slice : part14.clauses = (((Snake9.LocalWindow.ShareWindow144.raw14 ++ Snake9.LocalWindow.ShareWindow144.raw15)).drop 4).take 127 := by
  rw [part14_clauses]
  rfl
theorem part14_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw14.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw15.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part14 := by
  rw [← part14_build]
  apply build_true_of_slice τ part14 (Snake9.LocalWindow.ShareWindow144.raw14 ++ Snake9.LocalWindow.ShareWindow144.raw15) 4 127 part14_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part14_slice
#print axioms part14_true
theorem part15_slice : part15.clauses = (((Snake9.LocalWindow.ShareWindow144.raw15 ++ Snake9.LocalWindow.ShareWindow144.raw16)).drop 3).take 127 := by
  rw [part15_clauses]
  rfl
theorem part15_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw15.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw16.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part15 := by
  rw [← part15_build]
  apply build_true_of_slice τ part15 (Snake9.LocalWindow.ShareWindow144.raw15 ++ Snake9.LocalWindow.ShareWindow144.raw16) 3 127 part15_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part15_slice
#print axioms part15_true
end Snake9.ChunkData145
