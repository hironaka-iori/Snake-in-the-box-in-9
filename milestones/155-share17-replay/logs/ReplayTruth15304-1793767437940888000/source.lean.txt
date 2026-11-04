import ReplayParts15304
import ReplayTools153
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayData153
theorem part32_slice : input32.clauses = ((Snake9.LocalWindow.ShareWindow153.raw32 ++ Snake9.LocalWindow.ShareWindow153.raw33).drop 6).take 127 := by
  rw [part32_clauses]
  rfl
theorem part32_true (τ : Nat → Bool)
    (h32 : Snake9.LocalWindow.ShareWindow153.raw32.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h33 : Snake9.LocalWindow.ShareWindow153.raw33.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat153Replay.TreeTrue τ part32 := by
  rw [← part32_build]
  apply build_true_of_slice τ input32 (Snake9.LocalWindow.ShareWindow153.raw32 ++ Snake9.LocalWindow.ShareWindow153.raw33) 6 127 part32_slice
  rw [List.all_append]
  rw [h32, h33]
  rfl
#print axioms part32_true
theorem part33_slice : input33.clauses = ((Snake9.LocalWindow.ShareWindow153.raw33 ++ Snake9.LocalWindow.ShareWindow153.raw34).drop 5).take 127 := by
  rw [part33_clauses]
  rfl
theorem part33_true (τ : Nat → Bool)
    (h33 : Snake9.LocalWindow.ShareWindow153.raw33.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h34 : Snake9.LocalWindow.ShareWindow153.raw34.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat153Replay.TreeTrue τ part33 := by
  rw [← part33_build]
  apply build_true_of_slice τ input33 (Snake9.LocalWindow.ShareWindow153.raw33 ++ Snake9.LocalWindow.ShareWindow153.raw34) 5 127 part33_slice
  rw [List.all_append]
  rw [h33, h34]
  rfl
#print axioms part33_true
theorem part34_slice : input34.clauses = ((Snake9.LocalWindow.ShareWindow153.raw34 ++ Snake9.LocalWindow.ShareWindow153.raw35).drop 5).take 127 := by
  rw [part34_clauses]
  rfl
theorem part34_true (τ : Nat → Bool)
    (h34 : Snake9.LocalWindow.ShareWindow153.raw34.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h35 : Snake9.LocalWindow.ShareWindow153.raw35.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat153Replay.TreeTrue τ part34 := by
  rw [← part34_build]
  apply build_true_of_slice τ input34 (Snake9.LocalWindow.ShareWindow153.raw34 ++ Snake9.LocalWindow.ShareWindow153.raw35) 5 127 part34_slice
  rw [List.all_append]
  rw [h34, h35]
  rfl
#print axioms part34_true
theorem part35_slice : input35.clauses = ((Snake9.LocalWindow.ShareWindow153.raw35 ++ Snake9.LocalWindow.ShareWindow153.raw36).drop 4).take 127 := by
  rw [part35_clauses]
  rfl
theorem part35_true (τ : Nat → Bool)
    (h35 : Snake9.LocalWindow.ShareWindow153.raw35.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h36 : Snake9.LocalWindow.ShareWindow153.raw36.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat153Replay.TreeTrue τ part35 := by
  rw [← part35_build]
  apply build_true_of_slice τ input35 (Snake9.LocalWindow.ShareWindow153.raw35 ++ Snake9.LocalWindow.ShareWindow153.raw36) 4 127 part35_slice
  rw [List.all_append]
  rw [h35, h36]
  rfl
#print axioms part35_true
theorem part36_slice : input36.clauses = ((Snake9.LocalWindow.ShareWindow153.raw36 ++ Snake9.LocalWindow.ShareWindow153.raw37).drop 5).take 127 := by
  rw [part36_clauses]
  rfl
theorem part36_true (τ : Nat → Bool)
    (h36 : Snake9.LocalWindow.ShareWindow153.raw36.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h37 : Snake9.LocalWindow.ShareWindow153.raw37.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat153Replay.TreeTrue τ part36 := by
  rw [← part36_build]
  apply build_true_of_slice τ input36 (Snake9.LocalWindow.ShareWindow153.raw36 ++ Snake9.LocalWindow.ShareWindow153.raw37) 5 127 part36_slice
  rw [List.all_append]
  rw [h36, h37]
  rfl
#print axioms part36_true
theorem part37_slice : input37.clauses = ((Snake9.LocalWindow.ShareWindow153.raw37 ++ Snake9.LocalWindow.ShareWindow153.raw38).drop 4).take 127 := by
  rw [part37_clauses]
  rfl
theorem part37_true (τ : Nat → Bool)
    (h37 : Snake9.LocalWindow.ShareWindow153.raw37.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h38 : Snake9.LocalWindow.ShareWindow153.raw38.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat153Replay.TreeTrue τ part37 := by
  rw [← part37_build]
  apply build_true_of_slice τ input37 (Snake9.LocalWindow.ShareWindow153.raw37 ++ Snake9.LocalWindow.ShareWindow153.raw38) 4 127 part37_slice
  rw [List.all_append]
  rw [h37, h38]
  rfl
#print axioms part37_true
theorem part38_slice : input38.clauses = ((Snake9.LocalWindow.ShareWindow153.raw38 ++ Snake9.LocalWindow.ShareWindow153.raw39).drop 4).take 127 := by
  rw [part38_clauses]
  rfl
theorem part38_true (τ : Nat → Bool)
    (h38 : Snake9.LocalWindow.ShareWindow153.raw38.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h39 : Snake9.LocalWindow.ShareWindow153.raw39.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat153Replay.TreeTrue τ part38 := by
  rw [← part38_build]
  apply build_true_of_slice τ input38 (Snake9.LocalWindow.ShareWindow153.raw38 ++ Snake9.LocalWindow.ShareWindow153.raw39) 4 127 part38_slice
  rw [List.all_append]
  rw [h38, h39]
  rfl
#print axioms part38_true
theorem part39_slice : input39.clauses = ((Snake9.LocalWindow.ShareWindow153.raw39 ++ Snake9.LocalWindow.ShareWindow153.raw40).drop 3).take 127 := by
  rw [part39_clauses]
  rfl
theorem part39_true (τ : Nat → Bool)
    (h39 : Snake9.LocalWindow.ShareWindow153.raw39.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h40 : Snake9.LocalWindow.ShareWindow153.raw40.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat153Replay.TreeTrue τ part39 := by
  rw [← part39_build]
  apply build_true_of_slice τ input39 (Snake9.LocalWindow.ShareWindow153.raw39 ++ Snake9.LocalWindow.ShareWindow153.raw40) 3 127 part39_slice
  rw [List.all_append]
  rw [h39, h40]
  rfl
#print axioms part39_true
end Snake9.ReplayData153
