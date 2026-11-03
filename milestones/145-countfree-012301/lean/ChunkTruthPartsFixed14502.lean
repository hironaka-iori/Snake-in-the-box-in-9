import ChunkParts14502
import ChunkTruthTools145
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace Snake9.ChunkData145
open Snake9.InputTree145 (InputTree)
theorem part16_slice : part16.clauses = (((Snake9.LocalWindow.ShareWindow144.raw16 ++ Snake9.LocalWindow.ShareWindow144.raw17)).drop 6).take 127 := by
  rw [part16_clauses]
  rfl
theorem part16_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw16.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw17.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part16 := by
  rw [← part16_build]
  apply build_true_of_slice τ part16 (Snake9.LocalWindow.ShareWindow144.raw16 ++ Snake9.LocalWindow.ShareWindow144.raw17) 6 127 part16_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part16_slice
#print axioms part16_true
theorem part17_slice : part17.clauses = (((Snake9.LocalWindow.ShareWindow144.raw17 ++ Snake9.LocalWindow.ShareWindow144.raw18)).drop 5).take 127 := by
  rw [part17_clauses]
  rfl
theorem part17_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw17.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw18.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part17 := by
  rw [← part17_build]
  apply build_true_of_slice τ part17 (Snake9.LocalWindow.ShareWindow144.raw17 ++ Snake9.LocalWindow.ShareWindow144.raw18) 5 127 part17_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part17_slice
#print axioms part17_true
theorem part18_slice : part18.clauses = (((Snake9.LocalWindow.ShareWindow144.raw18 ++ Snake9.LocalWindow.ShareWindow144.raw19)).drop 5).take 127 := by
  rw [part18_clauses]
  rfl
theorem part18_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw18.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw19.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part18 := by
  rw [← part18_build]
  apply build_true_of_slice τ part18 (Snake9.LocalWindow.ShareWindow144.raw18 ++ Snake9.LocalWindow.ShareWindow144.raw19) 5 127 part18_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part18_slice
#print axioms part18_true
theorem part19_slice : part19.clauses = (((Snake9.LocalWindow.ShareWindow144.raw19 ++ Snake9.LocalWindow.ShareWindow144.raw20)).drop 4).take 127 := by
  rw [part19_clauses]
  rfl
theorem part19_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw19.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw20.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part19 := by
  rw [← part19_build]
  apply build_true_of_slice τ part19 (Snake9.LocalWindow.ShareWindow144.raw19 ++ Snake9.LocalWindow.ShareWindow144.raw20) 4 127 part19_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part19_slice
#print axioms part19_true
theorem part20_slice : part20.clauses = (((Snake9.LocalWindow.ShareWindow144.raw20 ++ Snake9.LocalWindow.ShareWindow144.raw21)).drop 5).take 127 := by
  rw [part20_clauses]
  rfl
theorem part20_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw20.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw21.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part20 := by
  rw [← part20_build]
  apply build_true_of_slice τ part20 (Snake9.LocalWindow.ShareWindow144.raw20 ++ Snake9.LocalWindow.ShareWindow144.raw21) 5 127 part20_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part20_slice
#print axioms part20_true
theorem part21_slice : part21.clauses = (((Snake9.LocalWindow.ShareWindow144.raw21 ++ Snake9.LocalWindow.ShareWindow144.raw22)).drop 4).take 127 := by
  rw [part21_clauses]
  rfl
theorem part21_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw21.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw22.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part21 := by
  rw [← part21_build]
  apply build_true_of_slice τ part21 (Snake9.LocalWindow.ShareWindow144.raw21 ++ Snake9.LocalWindow.ShareWindow144.raw22) 4 127 part21_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part21_slice
#print axioms part21_true
theorem part22_slice : part22.clauses = (((Snake9.LocalWindow.ShareWindow144.raw22 ++ Snake9.LocalWindow.ShareWindow144.raw23)).drop 4).take 127 := by
  rw [part22_clauses]
  rfl
theorem part22_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw22.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw23.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part22 := by
  rw [← part22_build]
  apply build_true_of_slice τ part22 (Snake9.LocalWindow.ShareWindow144.raw22 ++ Snake9.LocalWindow.ShareWindow144.raw23) 4 127 part22_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part22_slice
#print axioms part22_true
theorem part23_slice : part23.clauses = (((Snake9.LocalWindow.ShareWindow144.raw23 ++ Snake9.LocalWindow.ShareWindow144.raw24)).drop 3).take 127 := by
  rw [part23_clauses]
  rfl
theorem part23_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw23.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw24.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part23 := by
  rw [← part23_build]
  apply build_true_of_slice τ part23 (Snake9.LocalWindow.ShareWindow144.raw23 ++ Snake9.LocalWindow.ShareWindow144.raw24) 3 127 part23_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part23_slice
#print axioms part23_true
end Snake9.ChunkData145
