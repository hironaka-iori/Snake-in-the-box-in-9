import ChunkParts14505
import ChunkTruthTools145
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace Snake9.ChunkData145
open Snake9.InputTree145 (InputTree)
theorem part40_slice : part40.clauses = (((Snake9.LocalWindow.ShareWindow144.raw40 ++ Snake9.LocalWindow.ShareWindow144.raw41)).drop 5).take 127 := by
  rw [part40_clauses]
  rfl
theorem part40_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw40.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw41.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part40 := by
  rw [← part40_build]
  apply build_true_of_slice τ part40 (Snake9.LocalWindow.ShareWindow144.raw40 ++ Snake9.LocalWindow.ShareWindow144.raw41) 5 127 part40_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part40_slice
#print axioms part40_true
theorem part41_slice : part41.clauses = (((Snake9.LocalWindow.ShareWindow144.raw41 ++ Snake9.LocalWindow.ShareWindow144.raw42)).drop 4).take 127 := by
  rw [part41_clauses]
  rfl
theorem part41_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw41.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw42.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part41 := by
  rw [← part41_build]
  apply build_true_of_slice τ part41 (Snake9.LocalWindow.ShareWindow144.raw41 ++ Snake9.LocalWindow.ShareWindow144.raw42) 4 127 part41_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part41_slice
#print axioms part41_true
theorem part42_slice : part42.clauses = (((Snake9.LocalWindow.ShareWindow144.raw42 ++ Snake9.LocalWindow.ShareWindow144.raw43)).drop 4).take 127 := by
  rw [part42_clauses]
  rfl
theorem part42_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw42.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw43.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part42 := by
  rw [← part42_build]
  apply build_true_of_slice τ part42 (Snake9.LocalWindow.ShareWindow144.raw42 ++ Snake9.LocalWindow.ShareWindow144.raw43) 4 127 part42_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part42_slice
#print axioms part42_true
theorem part43_slice : part43.clauses = (((Snake9.LocalWindow.ShareWindow144.raw43 ++ Snake9.LocalWindow.ShareWindow144.raw44)).drop 3).take 127 := by
  rw [part43_clauses]
  rfl
theorem part43_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw43.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw44.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part43 := by
  rw [← part43_build]
  apply build_true_of_slice τ part43 (Snake9.LocalWindow.ShareWindow144.raw43 ++ Snake9.LocalWindow.ShareWindow144.raw44) 3 127 part43_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part43_slice
#print axioms part43_true
theorem part44_slice : part44.clauses = (((Snake9.LocalWindow.ShareWindow144.raw44 ++ Snake9.LocalWindow.ShareWindow144.raw45)).drop 4).take 127 := by
  rw [part44_clauses]
  rfl
theorem part44_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw44.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw45.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part44 := by
  rw [← part44_build]
  apply build_true_of_slice τ part44 (Snake9.LocalWindow.ShareWindow144.raw44 ++ Snake9.LocalWindow.ShareWindow144.raw45) 4 127 part44_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part44_slice
#print axioms part44_true
theorem part45_slice : part45.clauses = (((Snake9.LocalWindow.ShareWindow144.raw45 ++ Snake9.LocalWindow.ShareWindow144.raw46)).drop 3).take 127 := by
  rw [part45_clauses]
  rfl
theorem part45_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw45.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw46.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part45 := by
  rw [← part45_build]
  apply build_true_of_slice τ part45 (Snake9.LocalWindow.ShareWindow144.raw45 ++ Snake9.LocalWindow.ShareWindow144.raw46) 3 127 part45_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part45_slice
#print axioms part45_true
theorem part46_slice : part46.clauses = (((Snake9.LocalWindow.ShareWindow144.raw46 ++ Snake9.LocalWindow.ShareWindow144.raw47)).drop 3).take 127 := by
  rw [part46_clauses]
  rfl
theorem part46_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw46.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw47.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part46 := by
  rw [← part46_build]
  apply build_true_of_slice τ part46 (Snake9.LocalWindow.ShareWindow144.raw46 ++ Snake9.LocalWindow.ShareWindow144.raw47) 3 127 part46_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part46_slice
#print axioms part46_true
theorem part47_slice : part47.clauses = (((Snake9.LocalWindow.ShareWindow144.raw47 ++ Snake9.LocalWindow.ShareWindow144.raw48)).drop 2).take 127 := by
  rw [part47_clauses]
  rfl
theorem part47_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw47.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw48.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part47 := by
  rw [← part47_build]
  apply build_true_of_slice τ part47 (Snake9.LocalWindow.ShareWindow144.raw47 ++ Snake9.LocalWindow.ShareWindow144.raw48) 2 127 part47_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part47_slice
#print axioms part47_true
end Snake9.ChunkData145
