import ChunkParts14508
import ChunkTruthTools145
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace Snake9.ChunkData145
open Snake9.InputTree145 (InputTree)
theorem part64_slice : part64.clauses = (((Snake9.LocalWindow.ShareWindow144.raw64 ++ Snake9.LocalWindow.ShareWindow144.raw65)).drop 6).take 127 := by
  rw [part64_clauses]
  rfl
theorem part64_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw64.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw65.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part64 := by
  rw [← part64_build]
  apply build_true_of_slice τ part64 (Snake9.LocalWindow.ShareWindow144.raw64 ++ Snake9.LocalWindow.ShareWindow144.raw65) 6 127 part64_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part64_slice
#print axioms part64_true
theorem part65_slice : part65.clauses = (((Snake9.LocalWindow.ShareWindow144.raw65 ++ Snake9.LocalWindow.ShareWindow144.raw66)).drop 5).take 127 := by
  rw [part65_clauses]
  rfl
theorem part65_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw65.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw66.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part65 := by
  rw [← part65_build]
  apply build_true_of_slice τ part65 (Snake9.LocalWindow.ShareWindow144.raw65 ++ Snake9.LocalWindow.ShareWindow144.raw66) 5 127 part65_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part65_slice
#print axioms part65_true
theorem part66_slice : part66.clauses = (((Snake9.LocalWindow.ShareWindow144.raw66 ++ Snake9.LocalWindow.ShareWindow144.raw67)).drop 5).take 127 := by
  rw [part66_clauses]
  rfl
theorem part66_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw66.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw67.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part66 := by
  rw [← part66_build]
  apply build_true_of_slice τ part66 (Snake9.LocalWindow.ShareWindow144.raw66 ++ Snake9.LocalWindow.ShareWindow144.raw67) 5 127 part66_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part66_slice
#print axioms part66_true
theorem part67_slice : part67.clauses = (((Snake9.LocalWindow.ShareWindow144.raw67 ++ Snake9.LocalWindow.ShareWindow144.raw68)).drop 4).take 127 := by
  rw [part67_clauses]
  rfl
theorem part67_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw67.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw68.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part67 := by
  rw [← part67_build]
  apply build_true_of_slice τ part67 (Snake9.LocalWindow.ShareWindow144.raw67 ++ Snake9.LocalWindow.ShareWindow144.raw68) 4 127 part67_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part67_slice
#print axioms part67_true
theorem part68_slice : part68.clauses = (((Snake9.LocalWindow.ShareWindow144.raw68 ++ Snake9.LocalWindow.ShareWindow144.raw69)).drop 5).take 127 := by
  rw [part68_clauses]
  rfl
theorem part68_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw68.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw69.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part68 := by
  rw [← part68_build]
  apply build_true_of_slice τ part68 (Snake9.LocalWindow.ShareWindow144.raw68 ++ Snake9.LocalWindow.ShareWindow144.raw69) 5 127 part68_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part68_slice
#print axioms part68_true
theorem part69_slice : part69.clauses = (((Snake9.LocalWindow.ShareWindow144.raw69 ++ Snake9.LocalWindow.ShareWindow144.raw70)).drop 4).take 127 := by
  rw [part69_clauses]
  rfl
theorem part69_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw69.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw70.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part69 := by
  rw [← part69_build]
  apply build_true_of_slice τ part69 (Snake9.LocalWindow.ShareWindow144.raw69 ++ Snake9.LocalWindow.ShareWindow144.raw70) 4 127 part69_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part69_slice
#print axioms part69_true
theorem part70_slice : part70.clauses = (((Snake9.LocalWindow.ShareWindow144.raw70 ++ Snake9.LocalWindow.ShareWindow144.raw71)).drop 4).take 127 := by
  rw [part70_clauses]
  rfl
theorem part70_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw70.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw71.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part70 := by
  rw [← part70_build]
  apply build_true_of_slice τ part70 (Snake9.LocalWindow.ShareWindow144.raw70 ++ Snake9.LocalWindow.ShareWindow144.raw71) 4 127 part70_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part70_slice
#print axioms part70_true
theorem part71_slice : part71.clauses = (((Snake9.LocalWindow.ShareWindow144.raw71 ++ Snake9.LocalWindow.ShareWindow144.raw72)).drop 3).take 127 := by
  rw [part71_clauses]
  rfl
theorem part71_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw71.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw72.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part71 := by
  rw [← part71_build]
  apply build_true_of_slice τ part71 (Snake9.LocalWindow.ShareWindow144.raw71 ++ Snake9.LocalWindow.ShareWindow144.raw72) 3 127 part71_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part71_slice
#print axioms part71_true
end Snake9.ChunkData145
