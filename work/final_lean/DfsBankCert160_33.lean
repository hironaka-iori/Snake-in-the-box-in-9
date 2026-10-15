import DfsCertificate
import DfsBankData

namespace Snake9.Dfs
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem keep160_10 : search (oriented 10)[159]! (banFrom (fun i => (oriented 10)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_19 : search (oriented 19)[159]! (banFrom (fun i => (oriented 19)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_37 : search (oriented 37)[159]! (banFrom (fun i => (oriented 37)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_56 : search (oriented 56)[159]! (banFrom (fun i => (oriented 56)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_84 : search (oriented 84)[159]! (banFrom (fun i => (oriented 84)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_127_3 : search ((oriented 127)[159]! ^^^ 2 ^ 3) ((banFrom (fun i => (oriented 127)[i]!) 159) ||| cnMask (oriented 127)[159]!) 32 = false := by decide +kernel
theorem keep160_127_8 : search ((oriented 127)[159]! ^^^ 2 ^ 8) ((banFrom (fun i => (oriented 127)[i]!) 159) ||| cnMask (oriented 127)[159]!) 32 = false := by decide +kernel
theorem keep160_127 : search (oriented 127)[159]! (banFrom (fun i => (oriented 127)[i]!) 159) 33 = false :=
  search_of_children (oriented 127)[159]! (banFrom (fun i => (oriented 127)[i]!) 159) 32 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inr keep160_127_3
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inr keep160_127_8
    | n + 9, h => exact absurd h (by omega))
theorem keep160_138 : search (oriented 138)[159]! (banFrom (fun i => (oriented 138)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_166_8_4 : search (((oriented 166)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 4) (((banFrom (fun i => (oriented 166)[i]!) 159) ||| cnMask (oriented 166)[159]!) ||| cnMask ((oriented 166)[159]! ^^^ 2 ^ 8)) 31 = false := by decide +kernel
theorem keep160_166_8_7_0 : search ((((oriented 166)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 7) ^^^ 2 ^ 0) ((((banFrom (fun i => (oriented 166)[i]!) 159) ||| cnMask (oriented 166)[159]!) ||| cnMask ((oriented 166)[159]! ^^^ 2 ^ 8)) ||| cnMask (((oriented 166)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 7)) 30 = false := by decide +kernel
theorem keep160_166_8_7_3 : search ((((oriented 166)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 7) ^^^ 2 ^ 3) ((((banFrom (fun i => (oriented 166)[i]!) 159) ||| cnMask (oriented 166)[159]!) ||| cnMask ((oriented 166)[159]! ^^^ 2 ^ 8)) ||| cnMask (((oriented 166)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 7)) 30 = false := by decide +kernel
theorem keep160_166_8_7_6 : search ((((oriented 166)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 7) ^^^ 2 ^ 6) ((((banFrom (fun i => (oriented 166)[i]!) 159) ||| cnMask (oriented 166)[159]!) ||| cnMask ((oriented 166)[159]! ^^^ 2 ^ 8)) ||| cnMask (((oriented 166)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 7)) 30 = false := by decide +kernel
theorem keep160_166_8_7 : search (((oriented 166)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 7) (((banFrom (fun i => (oriented 166)[i]!) 159) ||| cnMask (oriented 166)[159]!) ||| cnMask ((oriented 166)[159]! ^^^ 2 ^ 8)) 31 = false :=
  search_of_children (((oriented 166)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 7) (((banFrom (fun i => (oriented 166)[i]!) 159) ||| cnMask (oriented 166)[159]!) ||| cnMask ((oriented 166)[159]! ^^^ 2 ^ 8)) 30 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inr keep160_166_8_7_0
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inr keep160_166_8_7_3
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inr keep160_166_8_7_6
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_166_8 : search ((oriented 166)[159]! ^^^ 2 ^ 8) ((banFrom (fun i => (oriented 166)[i]!) 159) ||| cnMask (oriented 166)[159]!) 32 = false :=
  search_of_children ((oriented 166)[159]! ^^^ 2 ^ 8) ((banFrom (fun i => (oriented 166)[i]!) 159) ||| cnMask (oriented 166)[159]!) 31 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inr keep160_166_8_4
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inr keep160_166_8_7
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_166 : search (oriented 166)[159]! (banFrom (fun i => (oriented 166)[i]!) 159) 33 = false :=
  search_of_children (oriented 166)[159]! (banFrom (fun i => (oriented 166)[i]!) 159) 32 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inr keep160_166_8
    | n + 9, h => exact absurd h (by omega))
theorem keep160_187 : search (oriented 187)[159]! (banFrom (fun i => (oriented 187)[i]!) 159) 33 = false := by decide +kernel

end Snake9.Dfs
