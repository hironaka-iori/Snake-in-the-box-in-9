import DfsCertificate
import DfsBankData

namespace Snake9.Dfs
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem keep160_0 : search (oriented 0)[159]! (banFrom (fun i => (oriented 0)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_14 : search (oriented 14)[159]! (banFrom (fun i => (oriented 14)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_29 : search (oriented 29)[159]! (banFrom (fun i => (oriented 29)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_32_8_7_0 : search ((((oriented 32)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 7) ^^^ 2 ^ 0) ((((banFrom (fun i => (oriented 32)[i]!) 159) ||| cnMask (oriented 32)[159]!) ||| cnMask ((oriented 32)[159]! ^^^ 2 ^ 8)) ||| cnMask (((oriented 32)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 7)) 30 = false := by decide +kernel
theorem keep160_32_8_7_3 : search ((((oriented 32)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 7) ^^^ 2 ^ 3) ((((banFrom (fun i => (oriented 32)[i]!) 159) ||| cnMask (oriented 32)[159]!) ||| cnMask ((oriented 32)[159]! ^^^ 2 ^ 8)) ||| cnMask (((oriented 32)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 7)) 30 = false := by decide +kernel
theorem keep160_32_8_7_6 : search ((((oriented 32)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 7) ^^^ 2 ^ 6) ((((banFrom (fun i => (oriented 32)[i]!) 159) ||| cnMask (oriented 32)[159]!) ||| cnMask ((oriented 32)[159]! ^^^ 2 ^ 8)) ||| cnMask (((oriented 32)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 7)) 30 = false := by decide +kernel
theorem keep160_32_8_7 : search (((oriented 32)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 7) (((banFrom (fun i => (oriented 32)[i]!) 159) ||| cnMask (oriented 32)[159]!) ||| cnMask ((oriented 32)[159]! ^^^ 2 ^ 8)) 31 = false :=
  search_of_children (((oriented 32)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 7) (((banFrom (fun i => (oriented 32)[i]!) 159) ||| cnMask (oriented 32)[159]!) ||| cnMask ((oriented 32)[159]! ^^^ 2 ^ 8)) 30 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inr keep160_32_8_7_0
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inr keep160_32_8_7_3
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inr keep160_32_8_7_6
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_32_8 : search ((oriented 32)[159]! ^^^ 2 ^ 8) ((banFrom (fun i => (oriented 32)[i]!) 159) ||| cnMask (oriented 32)[159]!) 32 = false :=
  search_of_children ((oriented 32)[159]! ^^^ 2 ^ 8) ((banFrom (fun i => (oriented 32)[i]!) 159) ||| cnMask (oriented 32)[159]!) 31 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inr keep160_32_8_7
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_32 : search (oriented 32)[159]! (banFrom (fun i => (oriented 32)[i]!) 159) 33 = false :=
  search_of_children (oriented 32)[159]! (banFrom (fun i => (oriented 32)[i]!) 159) 32 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inr keep160_32_8
    | n + 9, h => exact absurd h (by omega))
theorem keep160_76 : search (oriented 76)[159]! (banFrom (fun i => (oriented 76)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_99_0 : search ((oriented 99)[159]! ^^^ 2 ^ 0) ((banFrom (fun i => (oriented 99)[i]!) 159) ||| cnMask (oriented 99)[159]!) 32 = false := by decide +kernel
theorem keep160_99_6 : search ((oriented 99)[159]! ^^^ 2 ^ 6) ((banFrom (fun i => (oriented 99)[i]!) 159) ||| cnMask (oriented 99)[159]!) 32 = false := by decide +kernel
theorem keep160_99 : search (oriented 99)[159]! (banFrom (fun i => (oriented 99)[i]!) 159) 33 = false :=
  search_of_children (oriented 99)[159]! (banFrom (fun i => (oriented 99)[i]!) 159) 32 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inr keep160_99_0
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inr keep160_99_6
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_114 : search (oriented 114)[159]! (banFrom (fun i => (oriented 114)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_150 : search (oriented 150)[159]! (banFrom (fun i => (oriented 150)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_224 : search (oriented 224)[159]! (banFrom (fun i => (oriented 224)[i]!) 159) 33 = false := by decide +kernel

end Snake9.Dfs
