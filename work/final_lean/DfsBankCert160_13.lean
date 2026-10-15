import DfsCertificate
import DfsBankData

namespace Snake9.Dfs
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem keep160_23 : search (oriented 23)[159]! (banFrom (fun i => (oriented 23)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_42 : search (oriented 42)[159]! (banFrom (fun i => (oriented 42)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_104 : search (oriented 104)[159]! (banFrom (fun i => (oriented 104)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_107_0_2 : search (((oriented 107)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 2) (((banFrom (fun i => (oriented 107)[i]!) 159) ||| cnMask (oriented 107)[159]!) ||| cnMask ((oriented 107)[159]! ^^^ 2 ^ 0)) 31 = false := by decide +kernel
theorem keep160_107_0_4_1_0_2 : search ((((((oriented 107)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) ^^^ 2 ^ 2) ((((((banFrom (fun i => (oriented 107)[i]!) 159) ||| cnMask (oriented 107)[159]!) ||| cnMask ((oriented 107)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 107)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) ||| cnMask ((((oriented 107)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 107)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0)) 28 = false := by decide +kernel
theorem keep160_107_0_4_1_0_3 : search ((((((oriented 107)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) ^^^ 2 ^ 3) ((((((banFrom (fun i => (oriented 107)[i]!) 159) ||| cnMask (oriented 107)[159]!) ||| cnMask ((oriented 107)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 107)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) ||| cnMask ((((oriented 107)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 107)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0)) 28 = false := by decide +kernel
theorem keep160_107_0_4_1_0 : search (((((oriented 107)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) (((((banFrom (fun i => (oriented 107)[i]!) 159) ||| cnMask (oriented 107)[159]!) ||| cnMask ((oriented 107)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 107)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) ||| cnMask ((((oriented 107)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1)) 29 = false :=
  search_of_children (((((oriented 107)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) (((((banFrom (fun i => (oriented 107)[i]!) 159) ||| cnMask (oriented 107)[159]!) ||| cnMask ((oriented 107)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 107)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) ||| cnMask ((((oriented 107)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1)) 28 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inr keep160_107_0_4_1_0_2
    | 3, _ => exact Or.inr keep160_107_0_4_1_0_3
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_107_0_4_1 : search ((((oriented 107)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ((((banFrom (fun i => (oriented 107)[i]!) 159) ||| cnMask (oriented 107)[159]!) ||| cnMask ((oriented 107)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 107)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) 30 = false :=
  search_of_children ((((oriented 107)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ((((banFrom (fun i => (oriented 107)[i]!) 159) ||| cnMask (oriented 107)[159]!) ||| cnMask ((oriented 107)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 107)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) 29 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inr keep160_107_0_4_1_0
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_107_0_4 : search (((oriented 107)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) (((banFrom (fun i => (oriented 107)[i]!) 159) ||| cnMask (oriented 107)[159]!) ||| cnMask ((oriented 107)[159]! ^^^ 2 ^ 0)) 31 = false :=
  search_of_children (((oriented 107)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) (((banFrom (fun i => (oriented 107)[i]!) 159) ||| cnMask (oriented 107)[159]!) ||| cnMask ((oriented 107)[159]! ^^^ 2 ^ 0)) 30 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inr keep160_107_0_4_1
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_107_0 : search ((oriented 107)[159]! ^^^ 2 ^ 0) ((banFrom (fun i => (oriented 107)[i]!) 159) ||| cnMask (oriented 107)[159]!) 32 = false :=
  search_of_children ((oriented 107)[159]! ^^^ 2 ^ 0) ((banFrom (fun i => (oriented 107)[i]!) 159) ||| cnMask (oriented 107)[159]!) 31 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inr keep160_107_0_2
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inr keep160_107_0_4
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_107_6_1 : search (((oriented 107)[159]! ^^^ 2 ^ 6) ^^^ 2 ^ 1) (((banFrom (fun i => (oriented 107)[i]!) 159) ||| cnMask (oriented 107)[159]!) ||| cnMask ((oriented 107)[159]! ^^^ 2 ^ 6)) 31 = false := by decide +kernel
theorem keep160_107_6_2 : search (((oriented 107)[159]! ^^^ 2 ^ 6) ^^^ 2 ^ 2) (((banFrom (fun i => (oriented 107)[i]!) 159) ||| cnMask (oriented 107)[159]!) ||| cnMask ((oriented 107)[159]! ^^^ 2 ^ 6)) 31 = false := by decide +kernel
theorem keep160_107_6_4 : search (((oriented 107)[159]! ^^^ 2 ^ 6) ^^^ 2 ^ 4) (((banFrom (fun i => (oriented 107)[i]!) 159) ||| cnMask (oriented 107)[159]!) ||| cnMask ((oriented 107)[159]! ^^^ 2 ^ 6)) 31 = false := by decide +kernel
theorem keep160_107_6_8 : search (((oriented 107)[159]! ^^^ 2 ^ 6) ^^^ 2 ^ 8) (((banFrom (fun i => (oriented 107)[i]!) 159) ||| cnMask (oriented 107)[159]!) ||| cnMask ((oriented 107)[159]! ^^^ 2 ^ 6)) 31 = false := by decide +kernel
theorem keep160_107_6 : search ((oriented 107)[159]! ^^^ 2 ^ 6) ((banFrom (fun i => (oriented 107)[i]!) 159) ||| cnMask (oriented 107)[159]!) 32 = false :=
  search_of_children ((oriented 107)[159]! ^^^ 2 ^ 6) ((banFrom (fun i => (oriented 107)[i]!) 159) ||| cnMask (oriented 107)[159]!) 31 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inr keep160_107_6_1
    | 2, _ => exact Or.inr keep160_107_6_2
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inr keep160_107_6_4
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inr keep160_107_6_8
    | n + 9, h => exact absurd h (by omega))
theorem keep160_107 : search (oriented 107)[159]! (banFrom (fun i => (oriented 107)[i]!) 159) 33 = false :=
  search_of_children (oriented 107)[159]! (banFrom (fun i => (oriented 107)[i]!) 159) 32 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inr keep160_107_0
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inr keep160_107_6
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_142 : search (oriented 142)[159]! (banFrom (fun i => (oriented 142)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_178 : search (oriented 178)[159]! (banFrom (fun i => (oriented 178)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_246 : search (oriented 246)[159]! (banFrom (fun i => (oriented 246)[i]!) 159) 33 = false := by decide +kernel

end Snake9.Dfs
