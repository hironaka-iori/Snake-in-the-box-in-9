import ChunkParts14510
import ChunkTruthTools145
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace Snake9.ChunkData145
open Snake9.InputTree145 (InputTree)
theorem part80_slice : part80.clauses = (((Snake9.LocalWindow.ShareWindow144.raw80 ++ Snake9.LocalWindow.ShareWindow144.raw81)).drop 5).take 127 := by
  rw [part80_clauses]
  rfl
theorem part80_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw80.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw81.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part80 := by
  rw [← part80_build]
  apply build_true_of_slice τ part80 (Snake9.LocalWindow.ShareWindow144.raw80 ++ Snake9.LocalWindow.ShareWindow144.raw81) 5 127 part80_slice
  rw [List.all_append]
  exact Bool.and_eq_true.mpr ⟨h0, h1⟩
#print axioms part80_slice
#print axioms part80_true
theorem part81_slice : part81.clauses = (((Snake9.LocalWindow.ShareWindow144.raw81 ++ Snake9.LocalWindow.ShareWindow144.raw82)).drop 4).take 127 := by
  rw [part81_clauses]
  rfl
theorem part81_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw81.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw82.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part81 := by
  rw [← part81_build]
  apply build_true_of_slice τ part81 (Snake9.LocalWindow.ShareWindow144.raw81 ++ Snake9.LocalWindow.ShareWindow144.raw82) 4 127 part81_slice
  rw [List.all_append]
  exact Bool.and_eq_true.mpr ⟨h0, h1⟩
#print axioms part81_slice
#print axioms part81_true
theorem part82_slice : part82.clauses = (((Snake9.LocalWindow.ShareWindow144.raw82 ++ Snake9.LocalWindow.ShareWindow144.raw83)).drop 4).take 127 := by
  rw [part82_clauses]
  rfl
theorem part82_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw82.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw83.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part82 := by
  rw [← part82_build]
  apply build_true_of_slice τ part82 (Snake9.LocalWindow.ShareWindow144.raw82 ++ Snake9.LocalWindow.ShareWindow144.raw83) 4 127 part82_slice
  rw [List.all_append]
  exact Bool.and_eq_true.mpr ⟨h0, h1⟩
#print axioms part82_slice
#print axioms part82_true
theorem part83_slice : part83.clauses = (((Snake9.LocalWindow.ShareWindow144.raw83 ++ Snake9.LocalWindow.ShareWindow144.raw84)).drop 3).take 127 := by
  rw [part83_clauses]
  rfl
theorem part83_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw83.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw84.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part83 := by
  rw [← part83_build]
  apply build_true_of_slice τ part83 (Snake9.LocalWindow.ShareWindow144.raw83 ++ Snake9.LocalWindow.ShareWindow144.raw84) 3 127 part83_slice
  rw [List.all_append]
  exact Bool.and_eq_true.mpr ⟨h0, h1⟩
#print axioms part83_slice
#print axioms part83_true
theorem part84_slice : part84.clauses = (((Snake9.LocalWindow.ShareWindow144.raw84 ++ Snake9.LocalWindow.ShareWindow144.raw85)).drop 4).take 127 := by
  rw [part84_clauses]
  rfl
theorem part84_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw84.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw85.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part84 := by
  rw [← part84_build]
  apply build_true_of_slice τ part84 (Snake9.LocalWindow.ShareWindow144.raw84 ++ Snake9.LocalWindow.ShareWindow144.raw85) 4 127 part84_slice
  rw [List.all_append]
  exact Bool.and_eq_true.mpr ⟨h0, h1⟩
#print axioms part84_slice
#print axioms part84_true
theorem part85_slice : part85.clauses = (((Snake9.LocalWindow.ShareWindow144.raw85 ++ Snake9.LocalWindow.ShareWindow144.raw86)).drop 3).take 127 := by
  rw [part85_clauses]
  rfl
theorem part85_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw85.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw86.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part85 := by
  rw [← part85_build]
  apply build_true_of_slice τ part85 (Snake9.LocalWindow.ShareWindow144.raw85 ++ Snake9.LocalWindow.ShareWindow144.raw86) 3 127 part85_slice
  rw [List.all_append]
  exact Bool.and_eq_true.mpr ⟨h0, h1⟩
#print axioms part85_slice
#print axioms part85_true
theorem part86_slice : part86.clauses = (((Snake9.LocalWindow.ShareWindow144.raw86 ++ Snake9.LocalWindow.ShareWindow144.raw87)).drop 3).take 127 := by
  rw [part86_clauses]
  rfl
theorem part86_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw86.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw87.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part86 := by
  rw [← part86_build]
  apply build_true_of_slice τ part86 (Snake9.LocalWindow.ShareWindow144.raw86 ++ Snake9.LocalWindow.ShareWindow144.raw87) 3 127 part86_slice
  rw [List.all_append]
  exact Bool.and_eq_true.mpr ⟨h0, h1⟩
#print axioms part86_slice
#print axioms part86_true
theorem part87_slice : part87.clauses = (((Snake9.LocalWindow.ShareWindow144.raw87 ++ Snake9.LocalWindow.ShareWindow144.raw88)).drop 2).take 127 := by
  rw [part87_clauses]
  rfl
theorem part87_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw87.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw88.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part87 := by
  rw [← part87_build]
  apply build_true_of_slice τ part87 (Snake9.LocalWindow.ShareWindow144.raw87 ++ Snake9.LocalWindow.ShareWindow144.raw88) 2 127 part87_slice
  rw [List.all_append]
  exact Bool.and_eq_true.mpr ⟨h0, h1⟩
#print axioms part87_slice
#print axioms part87_true
end Snake9.ChunkData145
