import ChunkParts14511
import ChunkTruthTools145
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace Snake9.ChunkData145
open Snake9.InputTree145 (InputTree)
theorem part88_slice : part88.clauses = (((Snake9.LocalWindow.ShareWindow144.raw88 ++ Snake9.LocalWindow.ShareWindow144.raw89)).drop 4).take 127 := by
  rw [part88_clauses]
  rfl
theorem part88_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw88.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw89.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part88 := by
  rw [← part88_build]
  apply build_true_of_slice τ part88 (Snake9.LocalWindow.ShareWindow144.raw88 ++ Snake9.LocalWindow.ShareWindow144.raw89) 4 127 part88_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part88_slice
#print axioms part88_true
theorem part89_slice : part89.clauses = (((Snake9.LocalWindow.ShareWindow144.raw89 ++ Snake9.LocalWindow.ShareWindow144.raw90)).drop 3).take 127 := by
  rw [part89_clauses]
  rfl
theorem part89_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw89.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw90.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part89 := by
  rw [← part89_build]
  apply build_true_of_slice τ part89 (Snake9.LocalWindow.ShareWindow144.raw89 ++ Snake9.LocalWindow.ShareWindow144.raw90) 3 127 part89_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part89_slice
#print axioms part89_true
theorem part90_slice : part90.clauses = (((Snake9.LocalWindow.ShareWindow144.raw90 ++ Snake9.LocalWindow.ShareWindow144.raw91)).drop 3).take 127 := by
  rw [part90_clauses]
  rfl
theorem part90_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw90.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw91.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part90 := by
  rw [← part90_build]
  apply build_true_of_slice τ part90 (Snake9.LocalWindow.ShareWindow144.raw90 ++ Snake9.LocalWindow.ShareWindow144.raw91) 3 127 part90_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part90_slice
#print axioms part90_true
theorem part91_slice : part91.clauses = (((Snake9.LocalWindow.ShareWindow144.raw91 ++ Snake9.LocalWindow.ShareWindow144.raw92)).drop 2).take 127 := by
  rw [part91_clauses]
  rfl
theorem part91_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw91.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw92.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part91 := by
  rw [← part91_build]
  apply build_true_of_slice τ part91 (Snake9.LocalWindow.ShareWindow144.raw91 ++ Snake9.LocalWindow.ShareWindow144.raw92) 2 127 part91_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part91_slice
#print axioms part91_true
theorem part92_slice : part92.clauses = (((Snake9.LocalWindow.ShareWindow144.raw92 ++ Snake9.LocalWindow.ShareWindow144.raw93)).drop 3).take 127 := by
  rw [part92_clauses]
  rfl
theorem part92_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw92.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw93.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part92 := by
  rw [← part92_build]
  apply build_true_of_slice τ part92 (Snake9.LocalWindow.ShareWindow144.raw92 ++ Snake9.LocalWindow.ShareWindow144.raw93) 3 127 part92_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part92_slice
#print axioms part92_true
theorem part93_slice : part93.clauses = (((Snake9.LocalWindow.ShareWindow144.raw93 ++ Snake9.LocalWindow.ShareWindow144.raw94)).drop 2).take 127 := by
  rw [part93_clauses]
  rfl
theorem part93_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw93.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw94.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part93 := by
  rw [← part93_build]
  apply build_true_of_slice τ part93 (Snake9.LocalWindow.ShareWindow144.raw93 ++ Snake9.LocalWindow.ShareWindow144.raw94) 2 127 part93_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part93_slice
#print axioms part93_true
theorem part94_slice : part94.clauses = (((Snake9.LocalWindow.ShareWindow144.raw94 ++ Snake9.LocalWindow.ShareWindow144.raw95)).drop 2).take 127 := by
  rw [part94_clauses]
  rfl
theorem part94_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw94.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw95.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part94 := by
  rw [← part94_build]
  apply build_true_of_slice τ part94 (Snake9.LocalWindow.ShareWindow144.raw94 ++ Snake9.LocalWindow.ShareWindow144.raw95) 2 127 part94_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part94_slice
#print axioms part94_true
theorem part95_slice : part95.clauses = ((Snake9.LocalWindow.ShareWindow144.raw95).drop 1).take 127 := by
  rw [part95_clauses]
  rfl
theorem part95_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw95.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part95 := by
  rw [← part95_build]
  apply build_true_of_slice τ part95 Snake9.LocalWindow.ShareWindow144.raw95 1 127 part95_slice
  exact h0
#print axioms part95_slice
#print axioms part95_true
end Snake9.ChunkData145
