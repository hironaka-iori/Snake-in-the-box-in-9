import ChunkParts14500
import ChunkTruthTools145
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace Snake9.ChunkData145
open Snake9.InputTree145 (InputTree)
theorem part0_slice : part0.clauses = (((Snake9.LocalWindow.ShareWindow144.raw0 ++ Snake9.LocalWindow.ShareWindow144.raw1)).drop 7).take 127 := by
  rw [part0_clauses]
  rfl
theorem part0_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw0.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw1.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part0 := by
  rw [← part0_build]
  apply build_true_of_slice τ part0 (Snake9.LocalWindow.ShareWindow144.raw0 ++ Snake9.LocalWindow.ShareWindow144.raw1) 7 127 part0_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part0_slice
#print axioms part0_true
theorem part1_slice : part1.clauses = (((Snake9.LocalWindow.ShareWindow144.raw1 ++ Snake9.LocalWindow.ShareWindow144.raw2)).drop 6).take 127 := by
  rw [part1_clauses]
  rfl
theorem part1_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw1.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw2.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part1 := by
  rw [← part1_build]
  apply build_true_of_slice τ part1 (Snake9.LocalWindow.ShareWindow144.raw1 ++ Snake9.LocalWindow.ShareWindow144.raw2) 6 127 part1_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part1_slice
#print axioms part1_true
theorem part2_slice : part2.clauses = (((Snake9.LocalWindow.ShareWindow144.raw2 ++ Snake9.LocalWindow.ShareWindow144.raw3)).drop 6).take 127 := by
  rw [part2_clauses]
  rfl
theorem part2_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw2.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw3.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part2 := by
  rw [← part2_build]
  apply build_true_of_slice τ part2 (Snake9.LocalWindow.ShareWindow144.raw2 ++ Snake9.LocalWindow.ShareWindow144.raw3) 6 127 part2_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part2_slice
#print axioms part2_true
theorem part3_slice : part3.clauses = (((Snake9.LocalWindow.ShareWindow144.raw3 ++ Snake9.LocalWindow.ShareWindow144.raw4)).drop 5).take 127 := by
  rw [part3_clauses]
  rfl
theorem part3_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw3.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw4.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part3 := by
  rw [← part3_build]
  apply build_true_of_slice τ part3 (Snake9.LocalWindow.ShareWindow144.raw3 ++ Snake9.LocalWindow.ShareWindow144.raw4) 5 127 part3_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part3_slice
#print axioms part3_true
theorem part4_slice : part4.clauses = (((Snake9.LocalWindow.ShareWindow144.raw4 ++ Snake9.LocalWindow.ShareWindow144.raw5)).drop 6).take 127 := by
  rw [part4_clauses]
  rfl
theorem part4_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw4.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw5.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part4 := by
  rw [← part4_build]
  apply build_true_of_slice τ part4 (Snake9.LocalWindow.ShareWindow144.raw4 ++ Snake9.LocalWindow.ShareWindow144.raw5) 6 127 part4_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part4_slice
#print axioms part4_true
theorem part5_slice : part5.clauses = (((Snake9.LocalWindow.ShareWindow144.raw5 ++ Snake9.LocalWindow.ShareWindow144.raw6)).drop 5).take 127 := by
  rw [part5_clauses]
  rfl
theorem part5_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw5.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw6.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part5 := by
  rw [← part5_build]
  apply build_true_of_slice τ part5 (Snake9.LocalWindow.ShareWindow144.raw5 ++ Snake9.LocalWindow.ShareWindow144.raw6) 5 127 part5_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part5_slice
#print axioms part5_true
theorem part6_slice : part6.clauses = (((Snake9.LocalWindow.ShareWindow144.raw6 ++ Snake9.LocalWindow.ShareWindow144.raw7)).drop 5).take 127 := by
  rw [part6_clauses]
  rfl
theorem part6_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw6.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw7.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part6 := by
  rw [← part6_build]
  apply build_true_of_slice τ part6 (Snake9.LocalWindow.ShareWindow144.raw6 ++ Snake9.LocalWindow.ShareWindow144.raw7) 5 127 part6_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part6_slice
#print axioms part6_true
theorem part7_slice : part7.clauses = (((Snake9.LocalWindow.ShareWindow144.raw7 ++ Snake9.LocalWindow.ShareWindow144.raw8)).drop 4).take 127 := by
  rw [part7_clauses]
  rfl
theorem part7_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw7.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw8.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part7 := by
  rw [← part7_build]
  apply build_true_of_slice τ part7 (Snake9.LocalWindow.ShareWindow144.raw7 ++ Snake9.LocalWindow.ShareWindow144.raw8) 4 127 part7_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part7_slice
#print axioms part7_true
end Snake9.ChunkData145
