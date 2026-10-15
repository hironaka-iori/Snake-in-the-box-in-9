import DfsCertificate
import DfsBankData

namespace Snake9.Dfs
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem keep160_36 : search (oriented 36)[159]! (banFrom (fun i => (oriented 36)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_77_0_4_1_0_2 : search ((((((oriented 77)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) ^^^ 2 ^ 2) ((((((banFrom (fun i => (oriented 77)[i]!) 159) ||| cnMask (oriented 77)[159]!) ||| cnMask ((oriented 77)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 77)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) ||| cnMask ((((oriented 77)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 77)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0)) 28 = false := by decide +kernel
theorem keep160_77_0_4_1_0_3 : search ((((((oriented 77)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) ^^^ 2 ^ 3) ((((((banFrom (fun i => (oriented 77)[i]!) 159) ||| cnMask (oriented 77)[159]!) ||| cnMask ((oriented 77)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 77)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) ||| cnMask ((((oriented 77)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 77)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0)) 28 = false := by decide +kernel
theorem keep160_77_0_4_1_0 : search (((((oriented 77)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) (((((banFrom (fun i => (oriented 77)[i]!) 159) ||| cnMask (oriented 77)[159]!) ||| cnMask ((oriented 77)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 77)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) ||| cnMask ((((oriented 77)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1)) 29 = false :=
  search_of_children (((((oriented 77)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) (((((banFrom (fun i => (oriented 77)[i]!) 159) ||| cnMask (oriented 77)[159]!) ||| cnMask ((oriented 77)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 77)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) ||| cnMask ((((oriented 77)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1)) 28 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inr keep160_77_0_4_1_0_2
    | 3, _ => exact Or.inr keep160_77_0_4_1_0_3
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_77_0_4_1 : search ((((oriented 77)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ((((banFrom (fun i => (oriented 77)[i]!) 159) ||| cnMask (oriented 77)[159]!) ||| cnMask ((oriented 77)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 77)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) 30 = false :=
  search_of_children ((((oriented 77)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ((((banFrom (fun i => (oriented 77)[i]!) 159) ||| cnMask (oriented 77)[159]!) ||| cnMask ((oriented 77)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 77)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) 29 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inr keep160_77_0_4_1_0
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_77_0_4 : search (((oriented 77)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) (((banFrom (fun i => (oriented 77)[i]!) 159) ||| cnMask (oriented 77)[159]!) ||| cnMask ((oriented 77)[159]! ^^^ 2 ^ 0)) 31 = false :=
  search_of_children (((oriented 77)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) (((banFrom (fun i => (oriented 77)[i]!) 159) ||| cnMask (oriented 77)[159]!) ||| cnMask ((oriented 77)[159]! ^^^ 2 ^ 0)) 30 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inr keep160_77_0_4_1
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_77_0 : search ((oriented 77)[159]! ^^^ 2 ^ 0) ((banFrom (fun i => (oriented 77)[i]!) 159) ||| cnMask (oriented 77)[159]!) 32 = false :=
  search_of_children ((oriented 77)[159]! ^^^ 2 ^ 0) ((banFrom (fun i => (oriented 77)[i]!) 159) ||| cnMask (oriented 77)[159]!) 31 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inr keep160_77_0_4
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_77 : search (oriented 77)[159]! (banFrom (fun i => (oriented 77)[i]!) 159) 33 = false :=
  search_of_children (oriented 77)[159]! (banFrom (fun i => (oriented 77)[i]!) 159) 32 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inr keep160_77_0
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_132 : search (oriented 132)[159]! (banFrom (fun i => (oriented 132)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_160 : search (oriented 160)[159]! (banFrom (fun i => (oriented 160)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_172_8_4 : search (((oriented 172)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 4) (((banFrom (fun i => (oriented 172)[i]!) 159) ||| cnMask (oriented 172)[159]!) ||| cnMask ((oriented 172)[159]! ^^^ 2 ^ 8)) 31 = false := by decide +kernel
theorem keep160_172_8_7_0 : search ((((oriented 172)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 7) ^^^ 2 ^ 0) ((((banFrom (fun i => (oriented 172)[i]!) 159) ||| cnMask (oriented 172)[159]!) ||| cnMask ((oriented 172)[159]! ^^^ 2 ^ 8)) ||| cnMask (((oriented 172)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 7)) 30 = false := by decide +kernel
theorem keep160_172_8_7_3 : search ((((oriented 172)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 7) ^^^ 2 ^ 3) ((((banFrom (fun i => (oriented 172)[i]!) 159) ||| cnMask (oriented 172)[159]!) ||| cnMask ((oriented 172)[159]! ^^^ 2 ^ 8)) ||| cnMask (((oriented 172)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 7)) 30 = false := by decide +kernel
theorem keep160_172_8_7_6 : search ((((oriented 172)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 7) ^^^ 2 ^ 6) ((((banFrom (fun i => (oriented 172)[i]!) 159) ||| cnMask (oriented 172)[159]!) ||| cnMask ((oriented 172)[159]! ^^^ 2 ^ 8)) ||| cnMask (((oriented 172)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 7)) 30 = false := by decide +kernel
theorem keep160_172_8_7 : search (((oriented 172)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 7) (((banFrom (fun i => (oriented 172)[i]!) 159) ||| cnMask (oriented 172)[159]!) ||| cnMask ((oriented 172)[159]! ^^^ 2 ^ 8)) 31 = false :=
  search_of_children (((oriented 172)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 7) (((banFrom (fun i => (oriented 172)[i]!) 159) ||| cnMask (oriented 172)[159]!) ||| cnMask ((oriented 172)[159]! ^^^ 2 ^ 8)) 30 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inr keep160_172_8_7_0
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inr keep160_172_8_7_3
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inr keep160_172_8_7_6
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_172_8 : search ((oriented 172)[159]! ^^^ 2 ^ 8) ((banFrom (fun i => (oriented 172)[i]!) 159) ||| cnMask (oriented 172)[159]!) 32 = false :=
  search_of_children ((oriented 172)[159]! ^^^ 2 ^ 8) ((banFrom (fun i => (oriented 172)[i]!) 159) ||| cnMask (oriented 172)[159]!) 31 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inr keep160_172_8_4
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inr keep160_172_8_7
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_172 : search (oriented 172)[159]! (banFrom (fun i => (oriented 172)[i]!) 159) 33 = false :=
  search_of_children (oriented 172)[159]! (banFrom (fun i => (oriented 172)[i]!) 159) 32 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inr keep160_172_8
    | n + 9, h => exact absurd h (by omega))
theorem keep160_173 : search (oriented 173)[159]! (banFrom (fun i => (oriented 173)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_208 : search (oriented 208)[159]! (banFrom (fun i => (oriented 208)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_260 : search (oriented 260)[159]! (banFrom (fun i => (oriented 260)[i]!) 159) 33 = false := by decide +kernel

end Snake9.Dfs
