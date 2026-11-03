import ChunkParts14504
import ChunkTruthTools145
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace Snake9.ChunkData145
open Snake9.InputTree145 (InputTree)
theorem part32_slice : part32.clauses = (((Snake9.LocalWindow.ShareWindow144.raw32 ++ Snake9.LocalWindow.ShareWindow144.raw33)).drop 6).take 127 := by
  rw [part32_clauses]
  rfl
theorem part32_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw32.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw33.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part32 := by
  rw [← part32_build]
  apply build_true_of_slice τ part32 (Snake9.LocalWindow.ShareWindow144.raw32 ++ Snake9.LocalWindow.ShareWindow144.raw33) 6 127 part32_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part32_slice
#print axioms part32_true
theorem part33_slice : part33.clauses = (((Snake9.LocalWindow.ShareWindow144.raw33 ++ Snake9.LocalWindow.ShareWindow144.raw34)).drop 5).take 127 := by
  rw [part33_clauses]
  rfl
theorem part33_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw33.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw34.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part33 := by
  rw [← part33_build]
  apply build_true_of_slice τ part33 (Snake9.LocalWindow.ShareWindow144.raw33 ++ Snake9.LocalWindow.ShareWindow144.raw34) 5 127 part33_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part33_slice
#print axioms part33_true
theorem part34_slice : part34.clauses = (((Snake9.LocalWindow.ShareWindow144.raw34 ++ Snake9.LocalWindow.ShareWindow144.raw35)).drop 5).take 127 := by
  rw [part34_clauses]
  rfl
theorem part34_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw34.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw35.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part34 := by
  rw [← part34_build]
  apply build_true_of_slice τ part34 (Snake9.LocalWindow.ShareWindow144.raw34 ++ Snake9.LocalWindow.ShareWindow144.raw35) 5 127 part34_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part34_slice
#print axioms part34_true
theorem part35_slice : part35.clauses = (((Snake9.LocalWindow.ShareWindow144.raw35 ++ Snake9.LocalWindow.ShareWindow144.raw36)).drop 4).take 127 := by
  rw [part35_clauses]
  rfl
theorem part35_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw35.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw36.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part35 := by
  rw [← part35_build]
  apply build_true_of_slice τ part35 (Snake9.LocalWindow.ShareWindow144.raw35 ++ Snake9.LocalWindow.ShareWindow144.raw36) 4 127 part35_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part35_slice
#print axioms part35_true
theorem part36_slice : part36.clauses = (((Snake9.LocalWindow.ShareWindow144.raw36 ++ Snake9.LocalWindow.ShareWindow144.raw37)).drop 5).take 127 := by
  rw [part36_clauses]
  rfl
theorem part36_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw36.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw37.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part36 := by
  rw [← part36_build]
  apply build_true_of_slice τ part36 (Snake9.LocalWindow.ShareWindow144.raw36 ++ Snake9.LocalWindow.ShareWindow144.raw37) 5 127 part36_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part36_slice
#print axioms part36_true
theorem part37_slice : part37.clauses = (((Snake9.LocalWindow.ShareWindow144.raw37 ++ Snake9.LocalWindow.ShareWindow144.raw38)).drop 4).take 127 := by
  rw [part37_clauses]
  rfl
theorem part37_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw37.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw38.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part37 := by
  rw [← part37_build]
  apply build_true_of_slice τ part37 (Snake9.LocalWindow.ShareWindow144.raw37 ++ Snake9.LocalWindow.ShareWindow144.raw38) 4 127 part37_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part37_slice
#print axioms part37_true
theorem part38_slice : part38.clauses = (((Snake9.LocalWindow.ShareWindow144.raw38 ++ Snake9.LocalWindow.ShareWindow144.raw39)).drop 4).take 127 := by
  rw [part38_clauses]
  rfl
theorem part38_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw38.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw39.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part38 := by
  rw [← part38_build]
  apply build_true_of_slice τ part38 (Snake9.LocalWindow.ShareWindow144.raw38 ++ Snake9.LocalWindow.ShareWindow144.raw39) 4 127 part38_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part38_slice
#print axioms part38_true
theorem part39_slice : part39.clauses = (((Snake9.LocalWindow.ShareWindow144.raw39 ++ Snake9.LocalWindow.ShareWindow144.raw40)).drop 3).take 127 := by
  rw [part39_clauses]
  rfl
theorem part39_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw39.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw40.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part39 := by
  rw [← part39_build]
  apply build_true_of_slice τ part39 (Snake9.LocalWindow.ShareWindow144.raw39 ++ Snake9.LocalWindow.ShareWindow144.raw40) 3 127 part39_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part39_slice
#print axioms part39_true
end Snake9.ChunkData145
