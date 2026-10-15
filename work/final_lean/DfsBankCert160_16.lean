import DfsCertificate
import DfsBankData

namespace Snake9.Dfs
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem keep160_45 : search (oriented 45)[159]! (banFrom (fun i => (oriented 45)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_48 : search (oriented 48)[159]! (banFrom (fun i => (oriented 48)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_131_3_2_1_3_0 : search ((((((oriented 131)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) ^^^ 2 ^ 0) ((((((banFrom (fun i => (oriented 131)[i]!) 159) ||| cnMask (oriented 131)[159]!) ||| cnMask ((oriented 131)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 131)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) ||| cnMask ((((oriented 131)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 131)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3)) 28 = false := by decide +kernel
theorem keep160_131_3_2_1_3_4 : search ((((((oriented 131)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) ^^^ 2 ^ 4) ((((((banFrom (fun i => (oriented 131)[i]!) 159) ||| cnMask (oriented 131)[159]!) ||| cnMask ((oriented 131)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 131)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) ||| cnMask ((((oriented 131)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 131)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3)) 28 = false := by decide +kernel
theorem keep160_131_3_2_1_3 : search (((((oriented 131)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) (((((banFrom (fun i => (oriented 131)[i]!) 159) ||| cnMask (oriented 131)[159]!) ||| cnMask ((oriented 131)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 131)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) ||| cnMask ((((oriented 131)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1)) 29 = false :=
  search_of_children (((((oriented 131)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) (((((banFrom (fun i => (oriented 131)[i]!) 159) ||| cnMask (oriented 131)[159]!) ||| cnMask ((oriented 131)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 131)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) ||| cnMask ((((oriented 131)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1)) 28 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inr keep160_131_3_2_1_3_0
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inr keep160_131_3_2_1_3_4
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_131_3_2_1 : search ((((oriented 131)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ((((banFrom (fun i => (oriented 131)[i]!) 159) ||| cnMask (oriented 131)[159]!) ||| cnMask ((oriented 131)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 131)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) 30 = false :=
  search_of_children ((((oriented 131)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ((((banFrom (fun i => (oriented 131)[i]!) 159) ||| cnMask (oriented 131)[159]!) ||| cnMask ((oriented 131)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 131)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) 29 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inr keep160_131_3_2_1_3
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_131_3_2 : search (((oriented 131)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) (((banFrom (fun i => (oriented 131)[i]!) 159) ||| cnMask (oriented 131)[159]!) ||| cnMask ((oriented 131)[159]! ^^^ 2 ^ 3)) 31 = false :=
  search_of_children (((oriented 131)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) (((banFrom (fun i => (oriented 131)[i]!) 159) ||| cnMask (oriented 131)[159]!) ||| cnMask ((oriented 131)[159]! ^^^ 2 ^ 3)) 30 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inr keep160_131_3_2_1
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_131_3_4 : search (((oriented 131)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 4) (((banFrom (fun i => (oriented 131)[i]!) 159) ||| cnMask (oriented 131)[159]!) ||| cnMask ((oriented 131)[159]! ^^^ 2 ^ 3)) 31 = false := by decide +kernel
theorem keep160_131_3 : search ((oriented 131)[159]! ^^^ 2 ^ 3) ((banFrom (fun i => (oriented 131)[i]!) 159) ||| cnMask (oriented 131)[159]!) 32 = false :=
  search_of_children ((oriented 131)[159]! ^^^ 2 ^ 3) ((banFrom (fun i => (oriented 131)[i]!) 159) ||| cnMask (oriented 131)[159]!) 31 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inr keep160_131_3_2
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inr keep160_131_3_4
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_131_8_1 : search (((oriented 131)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 1) (((banFrom (fun i => (oriented 131)[i]!) 159) ||| cnMask (oriented 131)[159]!) ||| cnMask ((oriented 131)[159]! ^^^ 2 ^ 8)) 31 = false := by decide +kernel
theorem keep160_131_8_2 : search (((oriented 131)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 2) (((banFrom (fun i => (oriented 131)[i]!) 159) ||| cnMask (oriented 131)[159]!) ||| cnMask ((oriented 131)[159]! ^^^ 2 ^ 8)) 31 = false := by decide +kernel
theorem keep160_131_8_4 : search (((oriented 131)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 4) (((banFrom (fun i => (oriented 131)[i]!) 159) ||| cnMask (oriented 131)[159]!) ||| cnMask ((oriented 131)[159]! ^^^ 2 ^ 8)) 31 = false := by decide +kernel
theorem keep160_131_8_6 : search (((oriented 131)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 6) (((banFrom (fun i => (oriented 131)[i]!) 159) ||| cnMask (oriented 131)[159]!) ||| cnMask ((oriented 131)[159]! ^^^ 2 ^ 8)) 31 = false := by decide +kernel
theorem keep160_131_8 : search ((oriented 131)[159]! ^^^ 2 ^ 8) ((banFrom (fun i => (oriented 131)[i]!) 159) ||| cnMask (oriented 131)[159]!) 32 = false :=
  search_of_children ((oriented 131)[159]! ^^^ 2 ^ 8) ((banFrom (fun i => (oriented 131)[i]!) 159) ||| cnMask (oriented 131)[159]!) 31 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inr keep160_131_8_1
    | 2, _ => exact Or.inr keep160_131_8_2
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inr keep160_131_8_4
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inr keep160_131_8_6
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_131 : search (oriented 131)[159]! (banFrom (fun i => (oriented 131)[i]!) 159) 33 = false :=
  search_of_children (oriented 131)[159]! (banFrom (fun i => (oriented 131)[i]!) 159) 32 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inr keep160_131_3
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inr keep160_131_8
    | n + 9, h => exact absurd h (by omega))
theorem keep160_133 : search (oriented 133)[159]! (banFrom (fun i => (oriented 133)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_232 : search (oriented 232)[159]! (banFrom (fun i => (oriented 232)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_236 : search (oriented 236)[159]! (banFrom (fun i => (oriented 236)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_252 : search (oriented 252)[159]! (banFrom (fun i => (oriented 252)[i]!) 159) 33 = false := by decide +kernel

end Snake9.Dfs
