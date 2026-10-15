import DfsCertificate
import DfsBankData

namespace Snake9.Dfs
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem keep160_2 : search (oriented 2)[159]! (banFrom (fun i => (oriented 2)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_17 : search (oriented 17)[159]! (banFrom (fun i => (oriented 17)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_31 : search (oriented 31)[159]! (banFrom (fun i => (oriented 31)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_54 : search (oriented 54)[159]! (banFrom (fun i => (oriented 54)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_80 : search (oriented 80)[159]! (banFrom (fun i => (oriented 80)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_95_8_4 : search (((oriented 95)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 4) (((banFrom (fun i => (oriented 95)[i]!) 159) ||| cnMask (oriented 95)[159]!) ||| cnMask ((oriented 95)[159]! ^^^ 2 ^ 8)) 31 = false := by decide +kernel
theorem keep160_95_8_7_0 : search ((((oriented 95)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 7) ^^^ 2 ^ 0) ((((banFrom (fun i => (oriented 95)[i]!) 159) ||| cnMask (oriented 95)[159]!) ||| cnMask ((oriented 95)[159]! ^^^ 2 ^ 8)) ||| cnMask (((oriented 95)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 7)) 30 = false := by decide +kernel
theorem keep160_95_8_7_3 : search ((((oriented 95)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 7) ^^^ 2 ^ 3) ((((banFrom (fun i => (oriented 95)[i]!) 159) ||| cnMask (oriented 95)[159]!) ||| cnMask ((oriented 95)[159]! ^^^ 2 ^ 8)) ||| cnMask (((oriented 95)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 7)) 30 = false := by decide +kernel
theorem keep160_95_8_7_6 : search ((((oriented 95)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 7) ^^^ 2 ^ 6) ((((banFrom (fun i => (oriented 95)[i]!) 159) ||| cnMask (oriented 95)[159]!) ||| cnMask ((oriented 95)[159]! ^^^ 2 ^ 8)) ||| cnMask (((oriented 95)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 7)) 30 = false := by decide +kernel
theorem keep160_95_8_7 : search (((oriented 95)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 7) (((banFrom (fun i => (oriented 95)[i]!) 159) ||| cnMask (oriented 95)[159]!) ||| cnMask ((oriented 95)[159]! ^^^ 2 ^ 8)) 31 = false :=
  search_of_children (((oriented 95)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 7) (((banFrom (fun i => (oriented 95)[i]!) 159) ||| cnMask (oriented 95)[159]!) ||| cnMask ((oriented 95)[159]! ^^^ 2 ^ 8)) 30 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inr keep160_95_8_7_0
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inr keep160_95_8_7_3
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inr keep160_95_8_7_6
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_95_8 : search ((oriented 95)[159]! ^^^ 2 ^ 8) ((banFrom (fun i => (oriented 95)[i]!) 159) ||| cnMask (oriented 95)[159]!) 32 = false :=
  search_of_children ((oriented 95)[159]! ^^^ 2 ^ 8) ((banFrom (fun i => (oriented 95)[i]!) 159) ||| cnMask (oriented 95)[159]!) 31 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inr keep160_95_8_4
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inr keep160_95_8_7
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_95 : search (oriented 95)[159]! (banFrom (fun i => (oriented 95)[i]!) 159) 33 = false :=
  search_of_children (oriented 95)[159]! (banFrom (fun i => (oriented 95)[i]!) 159) 32 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inr keep160_95_8
    | n + 9, h => exact absurd h (by omega))
theorem keep160_116 : search (oriented 116)[159]! (banFrom (fun i => (oriented 116)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_119_3 : search ((oriented 119)[159]! ^^^ 2 ^ 3) ((banFrom (fun i => (oriented 119)[i]!) 159) ||| cnMask (oriented 119)[159]!) 32 = false := by decide +kernel
theorem keep160_119_8 : search ((oriented 119)[159]! ^^^ 2 ^ 8) ((banFrom (fun i => (oriented 119)[i]!) 159) ||| cnMask (oriented 119)[159]!) 32 = false := by decide +kernel
theorem keep160_119 : search (oriented 119)[159]! (banFrom (fun i => (oriented 119)[i]!) 159) 33 = false :=
  search_of_children (oriented 119)[159]! (banFrom (fun i => (oriented 119)[i]!) 159) 32 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inr keep160_119_3
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inr keep160_119_8
    | n + 9, h => exact absurd h (by omega))
theorem keep160_136 : search (oriented 136)[159]! (banFrom (fun i => (oriented 136)[i]!) 159) 33 = false := by decide +kernel

end Snake9.Dfs
