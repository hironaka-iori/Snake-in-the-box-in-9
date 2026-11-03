import ChunkParts14506
import ChunkTruthTools145
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace Snake9.ChunkData145
open Snake9.InputTree145 (InputTree)
theorem part48_slice : part48.clauses = (((Snake9.LocalWindow.ShareWindow144.raw48 ++ Snake9.LocalWindow.ShareWindow144.raw49)).drop 5).take 127 := by
  rw [part48_clauses]
  rfl
theorem part48_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw48.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw49.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part48 := by
  rw [← part48_build]
  apply build_true_of_slice τ part48 (Snake9.LocalWindow.ShareWindow144.raw48 ++ Snake9.LocalWindow.ShareWindow144.raw49) 5 127 part48_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part48_slice
#print axioms part48_true
theorem part49_slice : part49.clauses = (((Snake9.LocalWindow.ShareWindow144.raw49 ++ Snake9.LocalWindow.ShareWindow144.raw50)).drop 4).take 127 := by
  rw [part49_clauses]
  rfl
theorem part49_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw49.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw50.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part49 := by
  rw [← part49_build]
  apply build_true_of_slice τ part49 (Snake9.LocalWindow.ShareWindow144.raw49 ++ Snake9.LocalWindow.ShareWindow144.raw50) 4 127 part49_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part49_slice
#print axioms part49_true
theorem part50_slice : part50.clauses = (((Snake9.LocalWindow.ShareWindow144.raw50 ++ Snake9.LocalWindow.ShareWindow144.raw51)).drop 4).take 127 := by
  rw [part50_clauses]
  rfl
theorem part50_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw50.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw51.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part50 := by
  rw [← part50_build]
  apply build_true_of_slice τ part50 (Snake9.LocalWindow.ShareWindow144.raw50 ++ Snake9.LocalWindow.ShareWindow144.raw51) 4 127 part50_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part50_slice
#print axioms part50_true
theorem part51_slice : part51.clauses = (((Snake9.LocalWindow.ShareWindow144.raw51 ++ Snake9.LocalWindow.ShareWindow144.raw52)).drop 3).take 127 := by
  rw [part51_clauses]
  rfl
theorem part51_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw51.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw52.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part51 := by
  rw [← part51_build]
  apply build_true_of_slice τ part51 (Snake9.LocalWindow.ShareWindow144.raw51 ++ Snake9.LocalWindow.ShareWindow144.raw52) 3 127 part51_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part51_slice
#print axioms part51_true
theorem part52_slice : part52.clauses = (((Snake9.LocalWindow.ShareWindow144.raw52 ++ Snake9.LocalWindow.ShareWindow144.raw53)).drop 4).take 127 := by
  rw [part52_clauses]
  rfl
theorem part52_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw52.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw53.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part52 := by
  rw [← part52_build]
  apply build_true_of_slice τ part52 (Snake9.LocalWindow.ShareWindow144.raw52 ++ Snake9.LocalWindow.ShareWindow144.raw53) 4 127 part52_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part52_slice
#print axioms part52_true
theorem part53_slice : part53.clauses = (((Snake9.LocalWindow.ShareWindow144.raw53 ++ Snake9.LocalWindow.ShareWindow144.raw54)).drop 3).take 127 := by
  rw [part53_clauses]
  rfl
theorem part53_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw53.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw54.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part53 := by
  rw [← part53_build]
  apply build_true_of_slice τ part53 (Snake9.LocalWindow.ShareWindow144.raw53 ++ Snake9.LocalWindow.ShareWindow144.raw54) 3 127 part53_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part53_slice
#print axioms part53_true
theorem part54_slice : part54.clauses = (((Snake9.LocalWindow.ShareWindow144.raw54 ++ Snake9.LocalWindow.ShareWindow144.raw55)).drop 3).take 127 := by
  rw [part54_clauses]
  rfl
theorem part54_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw54.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw55.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part54 := by
  rw [← part54_build]
  apply build_true_of_slice τ part54 (Snake9.LocalWindow.ShareWindow144.raw54 ++ Snake9.LocalWindow.ShareWindow144.raw55) 3 127 part54_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part54_slice
#print axioms part54_true
theorem part55_slice : part55.clauses = (((Snake9.LocalWindow.ShareWindow144.raw55 ++ Snake9.LocalWindow.ShareWindow144.raw56)).drop 2).take 127 := by
  rw [part55_clauses]
  rfl
theorem part55_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw55.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw56.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part55 := by
  rw [← part55_build]
  apply build_true_of_slice τ part55 (Snake9.LocalWindow.ShareWindow144.raw55 ++ Snake9.LocalWindow.ShareWindow144.raw56) 2 127 part55_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part55_slice
#print axioms part55_true
end Snake9.ChunkData145
