import DfsCertificate
import DfsBankData

namespace Snake9.Dfs
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem keep160_96 : search (oriented 96)[159]! (banFrom (fun i => (oriented 96)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_111 : search (oriented 111)[159]! (banFrom (fun i => (oriented 111)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_117_2 : search ((oriented 117)[159]! ^^^ 2 ^ 2) ((banFrom (fun i => (oriented 117)[i]!) 159) ||| cnMask (oriented 117)[159]!) 32 = false := by decide +kernel
theorem keep160_117_3_2_1_3_4_0 : search (((((((oriented 117)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) ^^^ 2 ^ 4) ^^^ 2 ^ 0) (((((((banFrom (fun i => (oriented 117)[i]!) 159) ||| cnMask (oriented 117)[159]!) ||| cnMask ((oriented 117)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 117)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) ||| cnMask ((((oriented 117)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 117)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3)) ||| cnMask ((((((oriented 117)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) ^^^ 2 ^ 4)) 27 = false := by decide +kernel
theorem keep160_117_3_2_1_3_4_2 : search (((((((oriented 117)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) ^^^ 2 ^ 4) ^^^ 2 ^ 2) (((((((banFrom (fun i => (oriented 117)[i]!) 159) ||| cnMask (oriented 117)[159]!) ||| cnMask ((oriented 117)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 117)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) ||| cnMask ((((oriented 117)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 117)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3)) ||| cnMask ((((((oriented 117)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) ^^^ 2 ^ 4)) 27 = false := by decide +kernel
theorem keep160_117_3_2_1_3_4 : search ((((((oriented 117)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) ^^^ 2 ^ 4) ((((((banFrom (fun i => (oriented 117)[i]!) 159) ||| cnMask (oriented 117)[159]!) ||| cnMask ((oriented 117)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 117)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) ||| cnMask ((((oriented 117)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 117)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3)) 28 = false :=
  search_of_children ((((((oriented 117)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) ^^^ 2 ^ 4) ((((((banFrom (fun i => (oriented 117)[i]!) 159) ||| cnMask (oriented 117)[159]!) ||| cnMask ((oriented 117)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 117)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) ||| cnMask ((((oriented 117)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 117)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3)) 27 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inr keep160_117_3_2_1_3_4_0
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inr keep160_117_3_2_1_3_4_2
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_117_3_2_1_3 : search (((((oriented 117)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) (((((banFrom (fun i => (oriented 117)[i]!) 159) ||| cnMask (oriented 117)[159]!) ||| cnMask ((oriented 117)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 117)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) ||| cnMask ((((oriented 117)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1)) 29 = false :=
  search_of_children (((((oriented 117)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 3) (((((banFrom (fun i => (oriented 117)[i]!) 159) ||| cnMask (oriented 117)[159]!) ||| cnMask ((oriented 117)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 117)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) ||| cnMask ((((oriented 117)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1)) 28 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inr keep160_117_3_2_1_3_4
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_117_3_2_1 : search ((((oriented 117)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ((((banFrom (fun i => (oriented 117)[i]!) 159) ||| cnMask (oriented 117)[159]!) ||| cnMask ((oriented 117)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 117)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) 30 = false :=
  search_of_children ((((oriented 117)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) ^^^ 2 ^ 1) ((((banFrom (fun i => (oriented 117)[i]!) 159) ||| cnMask (oriented 117)[159]!) ||| cnMask ((oriented 117)[159]! ^^^ 2 ^ 3)) ||| cnMask (((oriented 117)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2)) 29 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inr keep160_117_3_2_1_3
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_117_3_2 : search (((oriented 117)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) (((banFrom (fun i => (oriented 117)[i]!) 159) ||| cnMask (oriented 117)[159]!) ||| cnMask ((oriented 117)[159]! ^^^ 2 ^ 3)) 31 = false :=
  search_of_children (((oriented 117)[159]! ^^^ 2 ^ 3) ^^^ 2 ^ 2) (((banFrom (fun i => (oriented 117)[i]!) 159) ||| cnMask (oriented 117)[159]!) ||| cnMask ((oriented 117)[159]! ^^^ 2 ^ 3)) 30 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inr keep160_117_3_2_1
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_117_3 : search ((oriented 117)[159]! ^^^ 2 ^ 3) ((banFrom (fun i => (oriented 117)[i]!) 159) ||| cnMask (oriented 117)[159]!) 32 = false :=
  search_of_children ((oriented 117)[159]! ^^^ 2 ^ 3) ((banFrom (fun i => (oriented 117)[i]!) 159) ||| cnMask (oriented 117)[159]!) 31 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inr keep160_117_3_2
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_117 : search (oriented 117)[159]! (banFrom (fun i => (oriented 117)[i]!) 159) 33 = false :=
  search_of_children (oriented 117)[159]! (banFrom (fun i => (oriented 117)[i]!) 159) 32 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inr keep160_117_2
    | 3, _ => exact Or.inr keep160_117_3
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_170 : search (oriented 170)[159]! (banFrom (fun i => (oriented 170)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_177 : search (oriented 177)[159]! (banFrom (fun i => (oriented 177)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_192 : search (oriented 192)[159]! (banFrom (fun i => (oriented 192)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_204 : search (oriented 204)[159]! (banFrom (fun i => (oriented 204)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_214 : search (oriented 214)[159]! (banFrom (fun i => (oriented 214)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_221 : search (oriented 221)[159]! (banFrom (fun i => (oriented 221)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_239 : search (oriented 239)[159]! (banFrom (fun i => (oriented 239)[i]!) 159) 33 = false := by decide +kernel

end Snake9.Dfs
