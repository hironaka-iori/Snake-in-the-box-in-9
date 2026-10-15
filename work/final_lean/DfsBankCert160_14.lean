import DfsCertificate
import DfsBankData

namespace Snake9.Dfs
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem keep160_40 : search (oriented 40)[159]! (banFrom (fun i => (oriented 40)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_44 : search (oriented 44)[159]! (banFrom (fun i => (oriented 44)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_121 : search (oriented 121)[159]! (banFrom (fun i => (oriented 121)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_123_3_2_1_3_0 : search ((((((oriented 123)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) ^^^ 2 ^ 0) ((((((banFrom (fun i => (oriented 123)[i]!) 159) ||| cnMask (oriented 123)[159]!) ||| cnMask ((oriented 123)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 123)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) ||| cnMask ((((oriented 123)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 123)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3)) 28 = false := by decide +kernel
theorem keep160_123_3_2_1_3_4 : search ((((((oriented 123)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) ^^^ 2 ^ 4) ((((((banFrom (fun i => (oriented 123)[i]!) 159) ||| cnMask (oriented 123)[159]!) ||| cnMask ((oriented 123)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 123)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) ||| cnMask ((((oriented 123)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 123)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3)) 28 = false := by decide +kernel
theorem keep160_123_3_2_1_3 : search (((((oriented 123)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) (((((banFrom (fun i => (oriented 123)[i]!) 159) ||| cnMask (oriented 123)[159]!) ||| cnMask ((oriented 123)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 123)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) ||| cnMask ((((oriented 123)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1)) 29 = false :=
  search_of_children (((((oriented 123)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) (((((banFrom (fun i => (oriented 123)[i]!) 159) ||| cnMask (oriented 123)[159]!) ||| cnMask ((oriented 123)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 123)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) ||| cnMask ((((oriented 123)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1)) 28 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inr keep160_123_3_2_1_3_0
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inr keep160_123_3_2_1_3_4
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_123_3_2_1 : search ((((oriented 123)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ((((banFrom (fun i => (oriented 123)[i]!) 159) ||| cnMask (oriented 123)[159]!) ||| cnMask ((oriented 123)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 123)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) 30 = false :=
  search_of_children ((((oriented 123)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ((((banFrom (fun i => (oriented 123)[i]!) 159) ||| cnMask (oriented 123)[159]!) ||| cnMask ((oriented 123)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 123)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) 29 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inr keep160_123_3_2_1_3
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_123_3_2 : search (((oriented 123)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) (((banFrom (fun i => (oriented 123)[i]!) 159) ||| cnMask (oriented 123)[159]!) ||| cnMask ((oriented 123)[159]! ^^^ 2 ^ 3)) 31 = false :=
  search_of_children (((oriented 123)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) (((banFrom (fun i => (oriented 123)[i]!) 159) ||| cnMask (oriented 123)[159]!) ||| cnMask ((oriented 123)[159]! ^^^ 2 ^ 3)) 30 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inr keep160_123_3_2_1
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_123_3_4 : search (((oriented 123)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 4) (((banFrom (fun i => (oriented 123)[i]!) 159) ||| cnMask (oriented 123)[159]!) ||| cnMask ((oriented 123)[159]! ^^^ 2 ^ 3)) 31 = false := by decide +kernel
theorem keep160_123_3 : search ((oriented 123)[159]! ^^^ 2 ^ 3) ((banFrom (fun i => (oriented 123)[i]!) 159) ||| cnMask (oriented 123)[159]!) 32 = false :=
  search_of_children ((oriented 123)[159]! ^^^ 2 ^ 3) ((banFrom (fun i => (oriented 123)[i]!) 159) ||| cnMask (oriented 123)[159]!) 31 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inr keep160_123_3_2
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inr keep160_123_3_4
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_123_8_1 : search (((oriented 123)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 1) (((banFrom (fun i => (oriented 123)[i]!) 159) ||| cnMask (oriented 123)[159]!) ||| cnMask ((oriented 123)[159]! ^^^ 2 ^ 8)) 31 = false := by decide +kernel
theorem keep160_123_8_2 : search (((oriented 123)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 2) (((banFrom (fun i => (oriented 123)[i]!) 159) ||| cnMask (oriented 123)[159]!) ||| cnMask ((oriented 123)[159]! ^^^ 2 ^ 8)) 31 = false := by decide +kernel
theorem keep160_123_8_4 : search (((oriented 123)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 4) (((banFrom (fun i => (oriented 123)[i]!) 159) ||| cnMask (oriented 123)[159]!) ||| cnMask ((oriented 123)[159]! ^^^ 2 ^ 8)) 31 = false := by decide +kernel
theorem keep160_123_8_6 : search (((oriented 123)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 6) (((banFrom (fun i => (oriented 123)[i]!) 159) ||| cnMask (oriented 123)[159]!) ||| cnMask ((oriented 123)[159]! ^^^ 2 ^ 8)) 31 = false := by decide +kernel
theorem keep160_123_8 : search ((oriented 123)[159]! ^^^ 2 ^ 8) ((banFrom (fun i => (oriented 123)[i]!) 159) ||| cnMask (oriented 123)[159]!) 32 = false :=
  search_of_children ((oriented 123)[159]! ^^^ 2 ^ 8) ((banFrom (fun i => (oriented 123)[i]!) 159) ||| cnMask (oriented 123)[159]!) 31 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inr keep160_123_8_1
    | 2, _ => exact Or.inr keep160_123_8_2
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inr keep160_123_8_4
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inr keep160_123_8_6
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_123 : search (oriented 123)[159]! (banFrom (fun i => (oriented 123)[i]!) 159) 33 = false :=
  search_of_children (oriented 123)[159]! (banFrom (fun i => (oriented 123)[i]!) 159) 32 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inr keep160_123_3
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inr keep160_123_8
    | n + 9, h => exact absurd h (by omega))
theorem keep160_180 : search (oriented 180)[159]! (banFrom (fun i => (oriented 180)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_228 : search (oriented 228)[159]! (banFrom (fun i => (oriented 228)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_248 : search (oriented 248)[159]! (banFrom (fun i => (oriented 248)[i]!) 159) 33 = false := by decide +kernel

end Snake9.Dfs
