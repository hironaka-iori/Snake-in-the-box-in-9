import DfsCertificate
import DfsBankData

namespace Snake9.Dfs
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem keep160_43 : search (oriented 43)[159]! (banFrom (fun i => (oriented 43)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_46 : search (oriented 46)[159]! (banFrom (fun i => (oriented 46)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_125 : search (oriented 125)[159]! (banFrom (fun i => (oriented 125)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_129_3_2_1_3_0 : search ((((((oriented 129)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) ^^^ 2 ^ 0) ((((((banFrom (fun i => (oriented 129)[i]!) 159) ||| cnMask (oriented 129)[159]!) ||| cnMask ((oriented 129)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 129)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) ||| cnMask ((((oriented 129)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 129)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3)) 28 = false := by decide +kernel
theorem keep160_129_3_2_1_3_4 : search ((((((oriented 129)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) ^^^ 2 ^ 4) ((((((banFrom (fun i => (oriented 129)[i]!) 159) ||| cnMask (oriented 129)[159]!) ||| cnMask ((oriented 129)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 129)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) ||| cnMask ((((oriented 129)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 129)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3)) 28 = false := by decide +kernel
theorem keep160_129_3_2_1_3 : search (((((oriented 129)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) (((((banFrom (fun i => (oriented 129)[i]!) 159) ||| cnMask (oriented 129)[159]!) ||| cnMask ((oriented 129)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 129)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) ||| cnMask ((((oriented 129)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1)) 29 = false :=
  search_of_children (((((oriented 129)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) (((((banFrom (fun i => (oriented 129)[i]!) 159) ||| cnMask (oriented 129)[159]!) ||| cnMask ((oriented 129)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 129)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) ||| cnMask ((((oriented 129)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1)) 28 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inr keep160_129_3_2_1_3_0
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inr keep160_129_3_2_1_3_4
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_129_3_2_1 : search ((((oriented 129)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ((((banFrom (fun i => (oriented 129)[i]!) 159) ||| cnMask (oriented 129)[159]!) ||| cnMask ((oriented 129)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 129)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) 30 = false :=
  search_of_children ((((oriented 129)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ((((banFrom (fun i => (oriented 129)[i]!) 159) ||| cnMask (oriented 129)[159]!) ||| cnMask ((oriented 129)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 129)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) 29 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inr keep160_129_3_2_1_3
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_129_3_2 : search (((oriented 129)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) (((banFrom (fun i => (oriented 129)[i]!) 159) ||| cnMask (oriented 129)[159]!) ||| cnMask ((oriented 129)[159]! ^^^ 2 ^ 3)) 31 = false :=
  search_of_children (((oriented 129)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) (((banFrom (fun i => (oriented 129)[i]!) 159) ||| cnMask (oriented 129)[159]!) ||| cnMask ((oriented 129)[159]! ^^^ 2 ^ 3)) 30 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inr keep160_129_3_2_1
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_129_3_4 : search (((oriented 129)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 4) (((banFrom (fun i => (oriented 129)[i]!) 159) ||| cnMask (oriented 129)[159]!) ||| cnMask ((oriented 129)[159]! ^^^ 2 ^ 3)) 31 = false := by decide +kernel
theorem keep160_129_3 : search ((oriented 129)[159]! ^^^ 2 ^ 3) ((banFrom (fun i => (oriented 129)[i]!) 159) ||| cnMask (oriented 129)[159]!) 32 = false :=
  search_of_children ((oriented 129)[159]! ^^^ 2 ^ 3) ((banFrom (fun i => (oriented 129)[i]!) 159) ||| cnMask (oriented 129)[159]!) 31 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inr keep160_129_3_2
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inr keep160_129_3_4
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_129_8_1 : search (((oriented 129)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 1) (((banFrom (fun i => (oriented 129)[i]!) 159) ||| cnMask (oriented 129)[159]!) ||| cnMask ((oriented 129)[159]! ^^^ 2 ^ 8)) 31 = false := by decide +kernel
theorem keep160_129_8_2 : search (((oriented 129)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 2) (((banFrom (fun i => (oriented 129)[i]!) 159) ||| cnMask (oriented 129)[159]!) ||| cnMask ((oriented 129)[159]! ^^^ 2 ^ 8)) 31 = false := by decide +kernel
theorem keep160_129_8_4 : search (((oriented 129)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 4) (((banFrom (fun i => (oriented 129)[i]!) 159) ||| cnMask (oriented 129)[159]!) ||| cnMask ((oriented 129)[159]! ^^^ 2 ^ 8)) 31 = false := by decide +kernel
theorem keep160_129_8_6 : search (((oriented 129)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 6) (((banFrom (fun i => (oriented 129)[i]!) 159) ||| cnMask (oriented 129)[159]!) ||| cnMask ((oriented 129)[159]! ^^^ 2 ^ 8)) 31 = false := by decide +kernel
theorem keep160_129_8 : search ((oriented 129)[159]! ^^^ 2 ^ 8) ((banFrom (fun i => (oriented 129)[i]!) 159) ||| cnMask (oriented 129)[159]!) 32 = false :=
  search_of_children ((oriented 129)[159]! ^^^ 2 ^ 8) ((banFrom (fun i => (oriented 129)[i]!) 159) ||| cnMask (oriented 129)[159]!) 31 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inr keep160_129_8_1
    | 2, _ => exact Or.inr keep160_129_8_2
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inr keep160_129_8_4
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inr keep160_129_8_6
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_129 : search (oriented 129)[159]! (banFrom (fun i => (oriented 129)[i]!) 159) 33 = false :=
  search_of_children (oriented 129)[159]! (banFrom (fun i => (oriented 129)[i]!) 159) 32 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inr keep160_129_3
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inr keep160_129_8
    | n + 9, h => exact absurd h (by omega))
theorem keep160_230 : search (oriented 230)[159]! (banFrom (fun i => (oriented 230)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_234 : search (oriented 234)[159]! (banFrom (fun i => (oriented 234)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_250 : search (oriented 250)[159]! (banFrom (fun i => (oriented 250)[i]!) 159) 33 = false := by decide +kernel

end Snake9.Dfs
