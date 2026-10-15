import DfsCertificate
import DfsBankData

namespace Snake9.Dfs
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem keep160_21 : search (oriented 21)[159]! (banFrom (fun i => (oriented 21)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_41 : search (oriented 41)[159]! (banFrom (fun i => (oriented 41)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_103_0_2 : search (((oriented 103)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 2) (((banFrom (fun i => (oriented 103)[i]!) 159) ||| cnMask (oriented 103)[159]!) ||| cnMask ((oriented 103)[159]! ^^^ 2 ^ 0)) 31 = false := by decide +kernel
theorem keep160_103_0_4_1_0_2 : search ((((((oriented 103)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) ^^^ 2 ^ 2) ((((((banFrom (fun i => (oriented 103)[i]!) 159) ||| cnMask (oriented 103)[159]!) ||| cnMask ((oriented 103)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 103)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) ||| cnMask ((((oriented 103)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 103)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0)) 28 = false := by decide +kernel
theorem keep160_103_0_4_1_0_3 : search ((((((oriented 103)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) ^^^ 2 ^ 3) ((((((banFrom (fun i => (oriented 103)[i]!) 159) ||| cnMask (oriented 103)[159]!) ||| cnMask ((oriented 103)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 103)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) ||| cnMask ((((oriented 103)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 103)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0)) 28 = false := by decide +kernel
theorem keep160_103_0_4_1_0 : search (((((oriented 103)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) (((((banFrom (fun i => (oriented 103)[i]!) 159) ||| cnMask (oriented 103)[159]!) ||| cnMask ((oriented 103)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 103)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) ||| cnMask ((((oriented 103)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1)) 29 = false :=
  search_of_children (((((oriented 103)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) (((((banFrom (fun i => (oriented 103)[i]!) 159) ||| cnMask (oriented 103)[159]!) ||| cnMask ((oriented 103)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 103)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) ||| cnMask ((((oriented 103)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1)) 28 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inr keep160_103_0_4_1_0_2
    | 3, _ => exact Or.inr keep160_103_0_4_1_0_3
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_103_0_4_1 : search ((((oriented 103)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ((((banFrom (fun i => (oriented 103)[i]!) 159) ||| cnMask (oriented 103)[159]!) ||| cnMask ((oriented 103)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 103)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) 30 = false :=
  search_of_children ((((oriented 103)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ((((banFrom (fun i => (oriented 103)[i]!) 159) ||| cnMask (oriented 103)[159]!) ||| cnMask ((oriented 103)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 103)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) 29 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inr keep160_103_0_4_1_0
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_103_0_4 : search (((oriented 103)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) (((banFrom (fun i => (oriented 103)[i]!) 159) ||| cnMask (oriented 103)[159]!) ||| cnMask ((oriented 103)[159]! ^^^ 2 ^ 0)) 31 = false :=
  search_of_children (((oriented 103)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) (((banFrom (fun i => (oriented 103)[i]!) 159) ||| cnMask (oriented 103)[159]!) ||| cnMask ((oriented 103)[159]! ^^^ 2 ^ 0)) 30 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inr keep160_103_0_4_1
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_103_0 : search ((oriented 103)[159]! ^^^ 2 ^ 0) ((banFrom (fun i => (oriented 103)[i]!) 159) ||| cnMask (oriented 103)[159]!) 32 = false :=
  search_of_children ((oriented 103)[159]! ^^^ 2 ^ 0) ((banFrom (fun i => (oriented 103)[i]!) 159) ||| cnMask (oriented 103)[159]!) 31 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inr keep160_103_0_2
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inr keep160_103_0_4
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_103_6_1 : search (((oriented 103)[159]! ^^^ 2 ^ 6) ^^^ 2 ^ 1) (((banFrom (fun i => (oriented 103)[i]!) 159) ||| cnMask (oriented 103)[159]!) ||| cnMask ((oriented 103)[159]! ^^^ 2 ^ 6)) 31 = false := by decide +kernel
theorem keep160_103_6_2 : search (((oriented 103)[159]! ^^^ 2 ^ 6) ^^^ 2 ^ 2) (((banFrom (fun i => (oriented 103)[i]!) 159) ||| cnMask (oriented 103)[159]!) ||| cnMask ((oriented 103)[159]! ^^^ 2 ^ 6)) 31 = false := by decide +kernel
theorem keep160_103_6_4 : search (((oriented 103)[159]! ^^^ 2 ^ 6) ^^^ 2 ^ 4) (((banFrom (fun i => (oriented 103)[i]!) 159) ||| cnMask (oriented 103)[159]!) ||| cnMask ((oriented 103)[159]! ^^^ 2 ^ 6)) 31 = false := by decide +kernel
theorem keep160_103_6_8 : search (((oriented 103)[159]! ^^^ 2 ^ 6) ^^^ 2 ^ 8) (((banFrom (fun i => (oriented 103)[i]!) 159) ||| cnMask (oriented 103)[159]!) ||| cnMask ((oriented 103)[159]! ^^^ 2 ^ 6)) 31 = false := by decide +kernel
theorem keep160_103_6 : search ((oriented 103)[159]! ^^^ 2 ^ 6) ((banFrom (fun i => (oriented 103)[i]!) 159) ||| cnMask (oriented 103)[159]!) 32 = false :=
  search_of_children ((oriented 103)[159]! ^^^ 2 ^ 6) ((banFrom (fun i => (oriented 103)[i]!) 159) ||| cnMask (oriented 103)[159]!) 31 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inr keep160_103_6_1
    | 2, _ => exact Or.inr keep160_103_6_2
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inr keep160_103_6_4
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inr keep160_103_6_8
    | n + 9, h => exact absurd h (by omega))
theorem keep160_103 : search (oriented 103)[159]! (banFrom (fun i => (oriented 103)[i]!) 159) 33 = false :=
  search_of_children (oriented 103)[159]! (banFrom (fun i => (oriented 103)[i]!) 159) 32 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inr keep160_103_0
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inr keep160_103_6
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_128 : search (oriented 128)[159]! (banFrom (fun i => (oriented 128)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_176 : search (oriented 176)[159]! (banFrom (fun i => (oriented 176)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_245 : search (oriented 245)[159]! (banFrom (fun i => (oriented 245)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_253 : search (oriented 253)[159]! (banFrom (fun i => (oriented 253)[i]!) 159) 33 = false := by decide +kernel

end Snake9.Dfs
