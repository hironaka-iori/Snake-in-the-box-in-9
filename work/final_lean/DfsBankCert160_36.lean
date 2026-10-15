import DfsCertificate
import DfsBankData

namespace Snake9.Dfs
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem keep160_13 : search (oriented 13)[159]! (banFrom (fun i => (oriented 13)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_34_8_7_0 : search ((((oriented 34)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 7) ^^^ 2 ^ 0) ((((banFrom (fun i => (oriented 34)[i]!) 159) ||| cnMask (oriented 34)[159]!) ||| cnMask ((oriented 34)[159]! ^^^ 2 ^ 8)) ||| cnMask (((oriented 34)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 7)) 30 = false := by decide +kernel
theorem keep160_34_8_7_3 : search ((((oriented 34)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 7) ^^^ 2 ^ 3) ((((banFrom (fun i => (oriented 34)[i]!) 159) ||| cnMask (oriented 34)[159]!) ||| cnMask ((oriented 34)[159]! ^^^ 2 ^ 8)) ||| cnMask (((oriented 34)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 7)) 30 = false := by decide +kernel
theorem keep160_34_8_7_6 : search ((((oriented 34)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 7) ^^^ 2 ^ 6) ((((banFrom (fun i => (oriented 34)[i]!) 159) ||| cnMask (oriented 34)[159]!) ||| cnMask ((oriented 34)[159]! ^^^ 2 ^ 8)) ||| cnMask (((oriented 34)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 7)) 30 = false := by decide +kernel
theorem keep160_34_8_7 : search (((oriented 34)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 7) (((banFrom (fun i => (oriented 34)[i]!) 159) ||| cnMask (oriented 34)[159]!) ||| cnMask ((oriented 34)[159]! ^^^ 2 ^ 8)) 31 = false :=
  search_of_children (((oriented 34)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 7) (((banFrom (fun i => (oriented 34)[i]!) 159) ||| cnMask (oriented 34)[159]!) ||| cnMask ((oriented 34)[159]! ^^^ 2 ^ 8)) 30 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inr keep160_34_8_7_0
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inr keep160_34_8_7_3
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inr keep160_34_8_7_6
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_34_8 : search ((oriented 34)[159]! ^^^ 2 ^ 8) ((banFrom (fun i => (oriented 34)[i]!) 159) ||| cnMask (oriented 34)[159]!) 32 = false :=
  search_of_children ((oriented 34)[159]! ^^^ 2 ^ 8) ((banFrom (fun i => (oriented 34)[i]!) 159) ||| cnMask (oriented 34)[159]!) 31 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inr keep160_34_8_7
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_34 : search (oriented 34)[159]! (banFrom (fun i => (oriented 34)[i]!) 159) 33 = false :=
  search_of_children (oriented 34)[159]! (banFrom (fun i => (oriented 34)[i]!) 159) 32 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inr keep160_34_8
    | n + 9, h => exact absurd h (by omega))
theorem keep160_71 : search (oriented 71)[159]! (banFrom (fun i => (oriented 71)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_91 : search (oriented 91)[159]! (banFrom (fun i => (oriented 91)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_92 : search (oriented 92)[159]! (banFrom (fun i => (oriented 92)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_109_0 : search ((oriented 109)[159]! ^^^ 2 ^ 0) ((banFrom (fun i => (oriented 109)[i]!) 159) ||| cnMask (oriented 109)[159]!) 32 = false := by decide +kernel
theorem keep160_109_6 : search ((oriented 109)[159]! ^^^ 2 ^ 6) ((banFrom (fun i => (oriented 109)[i]!) 159) ||| cnMask (oriented 109)[159]!) 32 = false := by decide +kernel
theorem keep160_109 : search (oriented 109)[159]! (banFrom (fun i => (oriented 109)[i]!) 159) 33 = false :=
  search_of_children (oriented 109)[159]! (banFrom (fun i => (oriented 109)[i]!) 159) 32 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inr keep160_109_0
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inr keep160_109_6
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_112 : search (oriented 112)[159]! (banFrom (fun i => (oriented 112)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_181 : search (oriented 181)[159]! (banFrom (fun i => (oriented 181)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_218 : search (oriented 218)[159]! (banFrom (fun i => (oriented 218)[i]!) 159) 33 = false := by decide +kernel

end Snake9.Dfs
