import ChunkParts14509
import ChunkTruthTools145
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace Snake9.ChunkData145
open Snake9.InputTree145 (InputTree)
theorem part72_slice : part72.clauses = (((Snake9.LocalWindow.ShareWindow144.raw72 ++ Snake9.LocalWindow.ShareWindow144.raw73)).drop 5).take 127 := by
  rw [part72_clauses]
  rfl
theorem part72_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw72.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw73.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part72 := by
  rw [← part72_build]
  apply build_true_of_slice τ part72 (Snake9.LocalWindow.ShareWindow144.raw72 ++ Snake9.LocalWindow.ShareWindow144.raw73) 5 127 part72_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part72_slice
#print axioms part72_true
theorem part73_slice : part73.clauses = (((Snake9.LocalWindow.ShareWindow144.raw73 ++ Snake9.LocalWindow.ShareWindow144.raw74)).drop 4).take 127 := by
  rw [part73_clauses]
  rfl
theorem part73_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw73.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw74.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part73 := by
  rw [← part73_build]
  apply build_true_of_slice τ part73 (Snake9.LocalWindow.ShareWindow144.raw73 ++ Snake9.LocalWindow.ShareWindow144.raw74) 4 127 part73_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part73_slice
#print axioms part73_true
theorem part74_slice : part74.clauses = (((Snake9.LocalWindow.ShareWindow144.raw74 ++ Snake9.LocalWindow.ShareWindow144.raw75)).drop 4).take 127 := by
  rw [part74_clauses]
  rfl
theorem part74_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw74.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw75.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part74 := by
  rw [← part74_build]
  apply build_true_of_slice τ part74 (Snake9.LocalWindow.ShareWindow144.raw74 ++ Snake9.LocalWindow.ShareWindow144.raw75) 4 127 part74_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part74_slice
#print axioms part74_true
theorem part75_slice : part75.clauses = (((Snake9.LocalWindow.ShareWindow144.raw75 ++ Snake9.LocalWindow.ShareWindow144.raw76)).drop 3).take 127 := by
  rw [part75_clauses]
  rfl
theorem part75_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw75.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw76.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part75 := by
  rw [← part75_build]
  apply build_true_of_slice τ part75 (Snake9.LocalWindow.ShareWindow144.raw75 ++ Snake9.LocalWindow.ShareWindow144.raw76) 3 127 part75_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part75_slice
#print axioms part75_true
theorem part76_slice : part76.clauses = (((Snake9.LocalWindow.ShareWindow144.raw76 ++ Snake9.LocalWindow.ShareWindow144.raw77)).drop 4).take 127 := by
  rw [part76_clauses]
  rfl
theorem part76_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw76.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw77.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part76 := by
  rw [← part76_build]
  apply build_true_of_slice τ part76 (Snake9.LocalWindow.ShareWindow144.raw76 ++ Snake9.LocalWindow.ShareWindow144.raw77) 4 127 part76_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part76_slice
#print axioms part76_true
theorem part77_slice : part77.clauses = (((Snake9.LocalWindow.ShareWindow144.raw77 ++ Snake9.LocalWindow.ShareWindow144.raw78)).drop 3).take 127 := by
  rw [part77_clauses]
  rfl
theorem part77_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw77.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw78.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part77 := by
  rw [← part77_build]
  apply build_true_of_slice τ part77 (Snake9.LocalWindow.ShareWindow144.raw77 ++ Snake9.LocalWindow.ShareWindow144.raw78) 3 127 part77_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part77_slice
#print axioms part77_true
theorem part78_slice : part78.clauses = (((Snake9.LocalWindow.ShareWindow144.raw78 ++ Snake9.LocalWindow.ShareWindow144.raw79)).drop 3).take 127 := by
  rw [part78_clauses]
  rfl
theorem part78_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw78.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw79.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part78 := by
  rw [← part78_build]
  apply build_true_of_slice τ part78 (Snake9.LocalWindow.ShareWindow144.raw78 ++ Snake9.LocalWindow.ShareWindow144.raw79) 3 127 part78_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part78_slice
#print axioms part78_true
theorem part79_slice : part79.clauses = (((Snake9.LocalWindow.ShareWindow144.raw79 ++ Snake9.LocalWindow.ShareWindow144.raw80)).drop 2).take 127 := by
  rw [part79_clauses]
  rfl
theorem part79_true (τ : Nat → Bool)
    (h0 : Snake9.LocalWindow.ShareWindow144.raw79.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h1 : Snake9.LocalWindow.ShareWindow144.raw80.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat144.TreeTrue τ Snake9.LiteralData144.part79 := by
  rw [← part79_build]
  apply build_true_of_slice τ part79 (Snake9.LocalWindow.ShareWindow144.raw79 ++ Snake9.LocalWindow.ShareWindow144.raw80) 2 127 part79_slice
  rw [List.all_append]
  rw [h0, h1]
  rfl
#print axioms part79_slice
#print axioms part79_true
end Snake9.ChunkData145
