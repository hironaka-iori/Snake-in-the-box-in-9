import DfsCertificate
import DfsBankData

namespace Snake9.Dfs
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem keep160_171_4_0_3_7_1 : search ((((((oriented 171)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 0) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 1) ((((((banFrom (fun i => (oriented 171)[i]!) 159) ||| cnMask (oriented 171)[159]!) ||| cnMask ((oriented 171)[159]! ^^^ 2 ^ 4)) ||| cnMask (((oriented 171)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 0)) ||| cnMask ((((oriented 171)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 0) ^^^ 2 ^ 3)) ||| cnMask (((((oriented 171)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 0) ^^^ 2 ^ 3) ^^^ 2 ^ 7)) 28 = false := by decide +kernel
theorem keep160_171_4_0_3_7_2 : search ((((((oriented 171)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 0) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 2) ((((((banFrom (fun i => (oriented 171)[i]!) 159) ||| cnMask (oriented 171)[159]!) ||| cnMask ((oriented 171)[159]! ^^^ 2 ^ 4)) ||| cnMask (((oriented 171)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 0)) ||| cnMask ((((oriented 171)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 0) ^^^ 2 ^ 3)) ||| cnMask (((((oriented 171)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 0) ^^^ 2 ^ 3) ^^^ 2 ^ 7)) 28 = false := by decide +kernel
theorem keep160_171_4_0_3_7_6 : search ((((((oriented 171)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 0) ^^^ 2 ^ 3) ^^^ 2 ^ 7) ^^^ 2 ^ 6) ((((((banFrom (fun i => (oriented 171)[i]!) 159) ||| cnMask (oriented 171)[159]!) ||| cnMask ((oriented 171)[159]! ^^^ 2 ^ 4)) ||| cnMask (((oriented 171)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 0)) ||| cnMask ((((oriented 171)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 0) ^^^ 2 ^ 3)) ||| cnMask (((((oriented 171)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 0) ^^^ 2 ^ 3) ^^^ 2 ^ 7)) 28 = false := by decide +kernel
theorem keep160_171_4_0_3_7 : search (((((oriented 171)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 0) ^^^ 2 ^ 3) ^^^ 2 ^ 7) (((((banFrom (fun i => (oriented 171)[i]!) 159) ||| cnMask (oriented 171)[159]!) ||| cnMask ((oriented 171)[159]! ^^^ 2 ^ 4)) ||| cnMask (((oriented 171)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 0)) ||| cnMask ((((oriented 171)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 0) ^^^ 2 ^ 3)) 29 = false :=
  search_of_children (((((oriented 171)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 0) ^^^ 2 ^ 3) ^^^ 2 ^ 7) (((((banFrom (fun i => (oriented 171)[i]!) 159) ||| cnMask (oriented 171)[159]!) ||| cnMask ((oriented 171)[159]! ^^^ 2 ^ 4)) ||| cnMask (((oriented 171)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 0)) ||| cnMask ((((oriented 171)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 0) ^^^ 2 ^ 3)) 28 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inr keep160_171_4_0_3_7_1
    | 2, _ => exact Or.inr keep160_171_4_0_3_7_2
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inr keep160_171_4_0_3_7_6
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_171_4_0_3 : search ((((oriented 171)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 0) ^^^ 2 ^ 3) ((((banFrom (fun i => (oriented 171)[i]!) 159) ||| cnMask (oriented 171)[159]!) ||| cnMask ((oriented 171)[159]! ^^^ 2 ^ 4)) ||| cnMask (((oriented 171)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 0)) 30 = false :=
  search_of_children ((((oriented 171)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 0) ^^^ 2 ^ 3) ((((banFrom (fun i => (oriented 171)[i]!) 159) ||| cnMask (oriented 171)[159]!) ||| cnMask ((oriented 171)[159]! ^^^ 2 ^ 4)) ||| cnMask (((oriented 171)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 0)) 29 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inr keep160_171_4_0_3_7
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_171_4_0_7_1 : search (((((oriented 171)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 0) ^^^ 2 ^ 7) ^^^ 2 ^ 1) (((((banFrom (fun i => (oriented 171)[i]!) 159) ||| cnMask (oriented 171)[159]!) ||| cnMask ((oriented 171)[159]! ^^^ 2 ^ 4)) ||| cnMask (((oriented 171)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 0)) ||| cnMask ((((oriented 171)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 0) ^^^ 2 ^ 7)) 29 = false := by decide +kernel
theorem keep160_171_4_0_7_2 : search (((((oriented 171)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 0) ^^^ 2 ^ 7) ^^^ 2 ^ 2) (((((banFrom (fun i => (oriented 171)[i]!) 159) ||| cnMask (oriented 171)[159]!) ||| cnMask ((oriented 171)[159]! ^^^ 2 ^ 4)) ||| cnMask (((oriented 171)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 0)) ||| cnMask ((((oriented 171)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 0) ^^^ 2 ^ 7)) 29 = false := by decide +kernel
theorem keep160_171_4_0_7_3 : search (((((oriented 171)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 0) ^^^ 2 ^ 7) ^^^ 2 ^ 3) (((((banFrom (fun i => (oriented 171)[i]!) 159) ||| cnMask (oriented 171)[159]!) ||| cnMask ((oriented 171)[159]! ^^^ 2 ^ 4)) ||| cnMask (((oriented 171)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 0)) ||| cnMask ((((oriented 171)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 0) ^^^ 2 ^ 7)) 29 = false := by decide +kernel
theorem keep160_171_4_0_7_6 : search (((((oriented 171)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 0) ^^^ 2 ^ 7) ^^^ 2 ^ 6) (((((banFrom (fun i => (oriented 171)[i]!) 159) ||| cnMask (oriented 171)[159]!) ||| cnMask ((oriented 171)[159]! ^^^ 2 ^ 4)) ||| cnMask (((oriented 171)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 0)) ||| cnMask ((((oriented 171)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 0) ^^^ 2 ^ 7)) 29 = false := by decide +kernel
theorem keep160_171_4_0_7_8 : search (((((oriented 171)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 0) ^^^ 2 ^ 7) ^^^ 2 ^ 8) (((((banFrom (fun i => (oriented 171)[i]!) 159) ||| cnMask (oriented 171)[159]!) ||| cnMask ((oriented 171)[159]! ^^^ 2 ^ 4)) ||| cnMask (((oriented 171)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 0)) ||| cnMask ((((oriented 171)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 0) ^^^ 2 ^ 7)) 29 = false := by decide +kernel
theorem keep160_171_4_0_7 : search ((((oriented 171)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 0) ^^^ 2 ^ 7) ((((banFrom (fun i => (oriented 171)[i]!) 159) ||| cnMask (oriented 171)[159]!) ||| cnMask ((oriented 171)[159]! ^^^ 2 ^ 4)) ||| cnMask (((oriented 171)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 0)) 30 = false :=
  search_of_children ((((oriented 171)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 0) ^^^ 2 ^ 7) ((((banFrom (fun i => (oriented 171)[i]!) 159) ||| cnMask (oriented 171)[159]!) ||| cnMask ((oriented 171)[159]! ^^^ 2 ^ 4)) ||| cnMask (((oriented 171)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 0)) 29 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inr keep160_171_4_0_7_1
    | 2, _ => exact Or.inr keep160_171_4_0_7_2
    | 3, _ => exact Or.inr keep160_171_4_0_7_3
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inr keep160_171_4_0_7_6
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inr keep160_171_4_0_7_8
    | n + 9, h => exact absurd h (by omega))
theorem keep160_171_4_0 : search (((oriented 171)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 0) (((banFrom (fun i => (oriented 171)[i]!) 159) ||| cnMask (oriented 171)[159]!) ||| cnMask ((oriented 171)[159]! ^^^ 2 ^ 4)) 31 = false :=
  search_of_children (((oriented 171)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 0) (((banFrom (fun i => (oriented 171)[i]!) 159) ||| cnMask (oriented 171)[159]!) ||| cnMask ((oriented 171)[159]! ^^^ 2 ^ 4)) 30 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inr keep160_171_4_0_3
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inr keep160_171_4_0_7
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_171_4_7 : search (((oriented 171)[159]! ^^^ 2 ^ 4) ^^^ 2 ^ 7) (((banFrom (fun i => (oriented 171)[i]!) 159) ||| cnMask (oriented 171)[159]!) ||| cnMask ((oriented 171)[159]! ^^^ 2 ^ 4)) 31 = false := by decide +kernel
theorem keep160_171_4 : search ((oriented 171)[159]! ^^^ 2 ^ 4) ((banFrom (fun i => (oriented 171)[i]!) 159) ||| cnMask (oriented 171)[159]!) 32 = false :=
  search_of_children ((oriented 171)[159]! ^^^ 2 ^ 4) ((banFrom (fun i => (oriented 171)[i]!) 159) ||| cnMask (oriented 171)[159]!) 31 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inr keep160_171_4_0
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inr keep160_171_4_7
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_171_7_2 : search (((oriented 171)[159]! ^^^ 2 ^ 7) ^^^ 2 ^ 2) (((banFrom (fun i => (oriented 171)[i]!) 159) ||| cnMask (oriented 171)[159]!) ||| cnMask ((oriented 171)[159]! ^^^ 2 ^ 7)) 31 = false := by decide +kernel
theorem keep160_171_7_3 : search (((oriented 171)[159]! ^^^ 2 ^ 7) ^^^ 2 ^ 3) (((banFrom (fun i => (oriented 171)[i]!) 159) ||| cnMask (oriented 171)[159]!) ||| cnMask ((oriented 171)[159]! ^^^ 2 ^ 7)) 31 = false := by decide +kernel
theorem keep160_171_7_4 : search (((oriented 171)[159]! ^^^ 2 ^ 7) ^^^ 2 ^ 4) (((banFrom (fun i => (oriented 171)[i]!) 159) ||| cnMask (oriented 171)[159]!) ||| cnMask ((oriented 171)[159]! ^^^ 2 ^ 7)) 31 = false := by decide +kernel
theorem keep160_171_7_6 : search (((oriented 171)[159]! ^^^ 2 ^ 7) ^^^ 2 ^ 6) (((banFrom (fun i => (oriented 171)[i]!) 159) ||| cnMask (oriented 171)[159]!) ||| cnMask ((oriented 171)[159]! ^^^ 2 ^ 7)) 31 = false := by decide +kernel
theorem keep160_171_7 : search ((oriented 171)[159]! ^^^ 2 ^ 7) ((banFrom (fun i => (oriented 171)[i]!) 159) ||| cnMask (oriented 171)[159]!) 32 = false :=
  search_of_children ((oriented 171)[159]! ^^^ 2 ^ 7) ((banFrom (fun i => (oriented 171)[i]!) 159) ||| cnMask (oriented 171)[159]!) 31 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inr keep160_171_7_2
    | 3, _ => exact Or.inr keep160_171_7_3
    | 4, _ => exact Or.inr keep160_171_7_4
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inr keep160_171_7_6
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_171 : search (oriented 171)[159]! (banFrom (fun i => (oriented 171)[i]!) 159) 33 = false :=
  search_of_children (oriented 171)[159]! (banFrom (fun i => (oriented 171)[i]!) 159) 32 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inr keep160_171_4
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inr keep160_171_7
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))

end Snake9.Dfs
