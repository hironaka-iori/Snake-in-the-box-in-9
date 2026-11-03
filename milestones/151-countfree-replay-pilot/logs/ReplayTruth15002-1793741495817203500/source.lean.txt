import ReplayParts15002
import ReplayTools150
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayData150
theorem part16_slice : input16.clauses = ((Snake9.LocalWindow.ShareWindow150.raw16 ++ Snake9.LocalWindow.ShareWindow150.raw17).drop 6).take 127 := by
  rw [part16_clauses]
  rfl
theorem part16_true (τ : Nat → Bool)
    (h16 : Snake9.LocalWindow.ShareWindow150.raw16.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h17 : Snake9.LocalWindow.ShareWindow150.raw17.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat150Replay.TreeTrue τ part16 := by
  rw [← part16_build]
  apply build_true_of_slice τ input16 (Snake9.LocalWindow.ShareWindow150.raw16 ++ Snake9.LocalWindow.ShareWindow150.raw17) 6 127 part16_slice
  rw [List.all_append]
  rw [h16, h17]
  rfl
#print axioms part16_true
theorem part17_slice : input17.clauses = ((Snake9.LocalWindow.ShareWindow150.raw17 ++ Snake9.LocalWindow.ShareWindow150.raw18).drop 5).take 127 := by
  rw [part17_clauses]
  rfl
theorem part17_true (τ : Nat → Bool)
    (h17 : Snake9.LocalWindow.ShareWindow150.raw17.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h18 : Snake9.LocalWindow.ShareWindow150.raw18.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat150Replay.TreeTrue τ part17 := by
  rw [← part17_build]
  apply build_true_of_slice τ input17 (Snake9.LocalWindow.ShareWindow150.raw17 ++ Snake9.LocalWindow.ShareWindow150.raw18) 5 127 part17_slice
  rw [List.all_append]
  rw [h17, h18]
  rfl
#print axioms part17_true
theorem part18_slice : input18.clauses = ((Snake9.LocalWindow.ShareWindow150.raw18 ++ Snake9.LocalWindow.ShareWindow150.raw19).drop 5).take 127 := by
  rw [part18_clauses]
  rfl
theorem part18_true (τ : Nat → Bool)
    (h18 : Snake9.LocalWindow.ShareWindow150.raw18.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h19 : Snake9.LocalWindow.ShareWindow150.raw19.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat150Replay.TreeTrue τ part18 := by
  rw [← part18_build]
  apply build_true_of_slice τ input18 (Snake9.LocalWindow.ShareWindow150.raw18 ++ Snake9.LocalWindow.ShareWindow150.raw19) 5 127 part18_slice
  rw [List.all_append]
  rw [h18, h19]
  rfl
#print axioms part18_true
theorem part19_slice : input19.clauses = ((Snake9.LocalWindow.ShareWindow150.raw19 ++ Snake9.LocalWindow.ShareWindow150.raw20).drop 4).take 127 := by
  rw [part19_clauses]
  rfl
theorem part19_true (τ : Nat → Bool)
    (h19 : Snake9.LocalWindow.ShareWindow150.raw19.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h20 : Snake9.LocalWindow.ShareWindow150.raw20.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat150Replay.TreeTrue τ part19 := by
  rw [← part19_build]
  apply build_true_of_slice τ input19 (Snake9.LocalWindow.ShareWindow150.raw19 ++ Snake9.LocalWindow.ShareWindow150.raw20) 4 127 part19_slice
  rw [List.all_append]
  rw [h19, h20]
  rfl
#print axioms part19_true
theorem part20_slice : input20.clauses = ((Snake9.LocalWindow.ShareWindow150.raw20 ++ Snake9.LocalWindow.ShareWindow150.raw21).drop 5).take 127 := by
  rw [part20_clauses]
  rfl
theorem part20_true (τ : Nat → Bool)
    (h20 : Snake9.LocalWindow.ShareWindow150.raw20.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h21 : Snake9.LocalWindow.ShareWindow150.raw21.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat150Replay.TreeTrue τ part20 := by
  rw [← part20_build]
  apply build_true_of_slice τ input20 (Snake9.LocalWindow.ShareWindow150.raw20 ++ Snake9.LocalWindow.ShareWindow150.raw21) 5 127 part20_slice
  rw [List.all_append]
  rw [h20, h21]
  rfl
#print axioms part20_true
theorem part21_slice : input21.clauses = ((Snake9.LocalWindow.ShareWindow150.raw21 ++ Snake9.LocalWindow.ShareWindow150.raw22).drop 4).take 127 := by
  rw [part21_clauses]
  rfl
theorem part21_true (τ : Nat → Bool)
    (h21 : Snake9.LocalWindow.ShareWindow150.raw21.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h22 : Snake9.LocalWindow.ShareWindow150.raw22.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat150Replay.TreeTrue τ part21 := by
  rw [← part21_build]
  apply build_true_of_slice τ input21 (Snake9.LocalWindow.ShareWindow150.raw21 ++ Snake9.LocalWindow.ShareWindow150.raw22) 4 127 part21_slice
  rw [List.all_append]
  rw [h21, h22]
  rfl
#print axioms part21_true
theorem part22_slice : input22.clauses = ((Snake9.LocalWindow.ShareWindow150.raw22 ++ Snake9.LocalWindow.ShareWindow150.raw23).drop 4).take 127 := by
  rw [part22_clauses]
  rfl
theorem part22_true (τ : Nat → Bool)
    (h22 : Snake9.LocalWindow.ShareWindow150.raw22.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h23 : Snake9.LocalWindow.ShareWindow150.raw23.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat150Replay.TreeTrue τ part22 := by
  rw [← part22_build]
  apply build_true_of_slice τ input22 (Snake9.LocalWindow.ShareWindow150.raw22 ++ Snake9.LocalWindow.ShareWindow150.raw23) 4 127 part22_slice
  rw [List.all_append]
  rw [h22, h23]
  rfl
#print axioms part22_true
theorem part23_slice : input23.clauses = ((Snake9.LocalWindow.ShareWindow150.raw23 ++ Snake9.LocalWindow.ShareWindow150.raw24).drop 3).take 127 := by
  rw [part23_clauses]
  rfl
theorem part23_true (τ : Nat → Bool)
    (h23 : Snake9.LocalWindow.ShareWindow150.raw23.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    (h24 : Snake9.LocalWindow.ShareWindow150.raw24.all (fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit)) = true)
    : Snake9.Lrat150Replay.TreeTrue τ part23 := by
  rw [← part23_build]
  apply build_true_of_slice τ input23 (Snake9.LocalWindow.ShareWindow150.raw23 ++ Snake9.LocalWindow.ShareWindow150.raw24) 3 127 part23_slice
  rw [List.all_append]
  rw [h23, h24]
  rfl
#print axioms part23_true
end Snake9.ReplayData150
