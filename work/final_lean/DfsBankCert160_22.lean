import DfsCertificate
import DfsBankData

namespace Snake9.Dfs
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem keep160_22 : search (oriented 22)[159]! (banFrom (fun i => (oriented 22)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_49 : search (oriented 49)[159]! (banFrom (fun i => (oriented 49)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_68_0_4_1_0_2_3 : search (((((((oriented 68)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) ^^^ 2 ^ 2) ^^^ 2 ^ 3) (((((((banFrom (fun i => (oriented 68)[i]!) 159) ||| cnMask (oriented 68)[159]!) ||| cnMask ((oriented 68)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 68)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) ||| cnMask ((((oriented 68)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 68)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0)) ||| cnMask ((((((oriented 68)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) ^^^ 2 ^ 2)) 27 = false := by decide +kernel
theorem keep160_68_0_4_1_0_2_4 : search (((((((oriented 68)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) ^^^ 2 ^ 2) ^^^ 2 ^ 4) (((((((banFrom (fun i => (oriented 68)[i]!) 159) ||| cnMask (oriented 68)[159]!) ||| cnMask ((oriented 68)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 68)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) ||| cnMask ((((oriented 68)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 68)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0)) ||| cnMask ((((((oriented 68)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) ^^^ 2 ^ 2)) 27 = false := by decide +kernel
theorem keep160_68_0_4_1_0_2 : search ((((((oriented 68)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) ^^^ 2 ^ 2) ((((((banFrom (fun i => (oriented 68)[i]!) 159) ||| cnMask (oriented 68)[159]!) ||| cnMask ((oriented 68)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 68)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) ||| cnMask ((((oriented 68)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 68)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0)) 28 = false :=
  search_of_children ((((((oriented 68)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) ^^^ 2 ^ 2) ((((((banFrom (fun i => (oriented 68)[i]!) 159) ||| cnMask (oriented 68)[159]!) ||| cnMask ((oriented 68)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 68)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) ||| cnMask ((((oriented 68)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 68)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0)) 27 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inr keep160_68_0_4_1_0_2_3
    | 4, _ => exact Or.inr keep160_68_0_4_1_0_2_4
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_68_0_4_1_0 : search (((((oriented 68)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) (((((banFrom (fun i => (oriented 68)[i]!) 159) ||| cnMask (oriented 68)[159]!) ||| cnMask ((oriented 68)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 68)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) ||| cnMask ((((oriented 68)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1)) 29 = false :=
  search_of_children (((((oriented 68)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) (((((banFrom (fun i => (oriented 68)[i]!) 159) ||| cnMask (oriented 68)[159]!) ||| cnMask ((oriented 68)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 68)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) ||| cnMask ((((oriented 68)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1)) 28 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inr keep160_68_0_4_1_0_2
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_68_0_4_1 : search ((((oriented 68)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ((((banFrom (fun i => (oriented 68)[i]!) 159) ||| cnMask (oriented 68)[159]!) ||| cnMask ((oriented 68)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 68)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) 30 = false :=
  search_of_children ((((oriented 68)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ((((banFrom (fun i => (oriented 68)[i]!) 159) ||| cnMask (oriented 68)[159]!) ||| cnMask ((oriented 68)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 68)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) 29 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inr keep160_68_0_4_1_0
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_68_0_4 : search (((oriented 68)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) (((banFrom (fun i => (oriented 68)[i]!) 159) ||| cnMask (oriented 68)[159]!) ||| cnMask ((oriented 68)[159]! ^^^ 2 ^ 0)) 31 = false :=
  search_of_children (((oriented 68)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) (((banFrom (fun i => (oriented 68)[i]!) 159) ||| cnMask (oriented 68)[159]!) ||| cnMask ((oriented 68)[159]! ^^^ 2 ^ 0)) 30 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inr keep160_68_0_4_1
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_68_0 : search ((oriented 68)[159]! ^^^ 2 ^ 0) ((banFrom (fun i => (oriented 68)[i]!) 159) ||| cnMask (oriented 68)[159]!) 32 = false :=
  search_of_children ((oriented 68)[159]! ^^^ 2 ^ 0) ((banFrom (fun i => (oriented 68)[i]!) 159) ||| cnMask (oriented 68)[159]!) 31 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inr keep160_68_0_4
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_68_4 : search ((oriented 68)[159]! ^^^ 2 ^ 4) ((banFrom (fun i => (oriented 68)[i]!) 159) ||| cnMask (oriented 68)[159]!) 32 = false := by decide +kernel
theorem keep160_68 : search (oriented 68)[159]! (banFrom (fun i => (oriented 68)[i]!) 159) 33 = false :=
  search_of_children (oriented 68)[159]! (banFrom (fun i => (oriented 68)[i]!) 159) 32 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inr keep160_68_0
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inr keep160_68_4
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_105 : search (oriented 105)[159]! (banFrom (fun i => (oriented 105)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_179 : search (oriented 179)[159]! (banFrom (fun i => (oriented 179)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_184 : search (oriented 184)[159]! (banFrom (fun i => (oriented 184)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_203 : search (oriented 203)[159]! (banFrom (fun i => (oriented 203)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_240 : search (oriented 240)[159]! (banFrom (fun i => (oriented 240)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_243 : search (oriented 243)[159]! (banFrom (fun i => (oriented 243)[i]!) 159) 33 = false := by decide +kernel

end Snake9.Dfs
