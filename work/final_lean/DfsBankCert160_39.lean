import DfsCertificate
import DfsBankData

namespace Snake9.Dfs
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem keep160_7 : search (oriented 7)[159]! (banFrom (fun i => (oriented 7)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_8 : search (oriented 8)[159]! (banFrom (fun i => (oriented 8)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_79 : search (oriented 79)[159]! (banFrom (fun i => (oriented 79)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_81_0_4_1_0_2 : search ((((((oriented 81)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) ^^^ 2 ^ 2) ((((((banFrom (fun i => (oriented 81)[i]!) 159) ||| cnMask (oriented 81)[159]!) ||| cnMask ((oriented 81)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 81)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) ||| cnMask ((((oriented 81)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 81)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0)) 28 = false := by decide +kernel
theorem keep160_81_0_4_1_0_3 : search ((((((oriented 81)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) ^^^ 2 ^ 3) ((((((banFrom (fun i => (oriented 81)[i]!) 159) ||| cnMask (oriented 81)[159]!) ||| cnMask ((oriented 81)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 81)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) ||| cnMask ((((oriented 81)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 81)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0)) 28 = false := by decide +kernel
theorem keep160_81_0_4_1_0 : search (((((oriented 81)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) (((((banFrom (fun i => (oriented 81)[i]!) 159) ||| cnMask (oriented 81)[159]!) ||| cnMask ((oriented 81)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 81)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) ||| cnMask ((((oriented 81)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1)) 29 = false :=
  search_of_children (((((oriented 81)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) (((((banFrom (fun i => (oriented 81)[i]!) 159) ||| cnMask (oriented 81)[159]!) ||| cnMask ((oriented 81)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 81)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) ||| cnMask ((((oriented 81)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1)) 28 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inr keep160_81_0_4_1_0_2
    | 3, _ => exact Or.inr keep160_81_0_4_1_0_3
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_81_0_4_1 : search ((((oriented 81)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ((((banFrom (fun i => (oriented 81)[i]!) 159) ||| cnMask (oriented 81)[159]!) ||| cnMask ((oriented 81)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 81)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) 30 = false :=
  search_of_children ((((oriented 81)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ((((banFrom (fun i => (oriented 81)[i]!) 159) ||| cnMask (oriented 81)[159]!) ||| cnMask ((oriented 81)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 81)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) 29 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inr keep160_81_0_4_1_0
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_81_0_4 : search (((oriented 81)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) (((banFrom (fun i => (oriented 81)[i]!) 159) ||| cnMask (oriented 81)[159]!) ||| cnMask ((oriented 81)[159]! ^^^ 2 ^ 0)) 31 = false :=
  search_of_children (((oriented 81)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) (((banFrom (fun i => (oriented 81)[i]!) 159) ||| cnMask (oriented 81)[159]!) ||| cnMask ((oriented 81)[159]! ^^^ 2 ^ 0)) 30 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inr keep160_81_0_4_1
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_81_0 : search ((oriented 81)[159]! ^^^ 2 ^ 0) ((banFrom (fun i => (oriented 81)[i]!) 159) ||| cnMask (oriented 81)[159]!) 32 = false :=
  search_of_children ((oriented 81)[159]! ^^^ 2 ^ 0) ((banFrom (fun i => (oriented 81)[i]!) 159) ||| cnMask (oriented 81)[159]!) 31 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inr keep160_81_0_4
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_81 : search (oriented 81)[159]! (banFrom (fun i => (oriented 81)[i]!) 159) 33 = false :=
  search_of_children (oriented 81)[159]! (banFrom (fun i => (oriented 81)[i]!) 159) 32 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inr keep160_81_0
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_87_0_4_1_0_2 : search ((((((oriented 87)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) ^^^ 2 ^ 2) ((((((banFrom (fun i => (oriented 87)[i]!) 159) ||| cnMask (oriented 87)[159]!) ||| cnMask ((oriented 87)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 87)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) ||| cnMask ((((oriented 87)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 87)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0)) 28 = false := by decide +kernel
theorem keep160_87_0_4_1_0_3 : search ((((((oriented 87)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) ^^^ 2 ^ 3) ((((((banFrom (fun i => (oriented 87)[i]!) 159) ||| cnMask (oriented 87)[159]!) ||| cnMask ((oriented 87)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 87)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) ||| cnMask ((((oriented 87)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1)) ||| cnMask (((((oriented 87)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0)) 28 = false := by decide +kernel
theorem keep160_87_0_4_1_0 : search (((((oriented 87)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) (((((banFrom (fun i => (oriented 87)[i]!) 159) ||| cnMask (oriented 87)[159]!) ||| cnMask ((oriented 87)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 87)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) ||| cnMask ((((oriented 87)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1)) 29 = false :=
  search_of_children (((((oriented 87)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ^^^ 2 ^ 0) (((((banFrom (fun i => (oriented 87)[i]!) 159) ||| cnMask (oriented 87)[159]!) ||| cnMask ((oriented 87)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 87)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) ||| cnMask ((((oriented 87)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1)) 28 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inr keep160_87_0_4_1_0_2
    | 3, _ => exact Or.inr keep160_87_0_4_1_0_3
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_87_0_4_1 : search ((((oriented 87)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ((((banFrom (fun i => (oriented 87)[i]!) 159) ||| cnMask (oriented 87)[159]!) ||| cnMask ((oriented 87)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 87)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) 30 = false :=
  search_of_children ((((oriented 87)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) ^^^ 2 ^ 1) ((((banFrom (fun i => (oriented 87)[i]!) 159) ||| cnMask (oriented 87)[159]!) ||| cnMask ((oriented 87)[159]! ^^^ 2 ^ 0)) ||| cnMask (((oriented 87)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4)) 29 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inr keep160_87_0_4_1_0
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_87_0_4 : search (((oriented 87)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) (((banFrom (fun i => (oriented 87)[i]!) 159) ||| cnMask (oriented 87)[159]!) ||| cnMask ((oriented 87)[159]! ^^^ 2 ^ 0)) 31 = false :=
  search_of_children (((oriented 87)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) (((banFrom (fun i => (oriented 87)[i]!) 159) ||| cnMask (oriented 87)[159]!) ||| cnMask ((oriented 87)[159]! ^^^ 2 ^ 0)) 30 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inr keep160_87_0_4_1
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_87_0 : search ((oriented 87)[159]! ^^^ 2 ^ 0) ((banFrom (fun i => (oriented 87)[i]!) 159) ||| cnMask (oriented 87)[159]!) 32 = false :=
  search_of_children ((oriented 87)[159]! ^^^ 2 ^ 0) ((banFrom (fun i => (oriented 87)[i]!) 159) ||| cnMask (oriented 87)[159]!) 31 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inr keep160_87_0_4
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_87 : search (oriented 87)[159]! (banFrom (fun i => (oriented 87)[i]!) 159) 33 = false :=
  search_of_children (oriented 87)[159]! (banFrom (fun i => (oriented 87)[i]!) 159) 32 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inr keep160_87_0
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_145 : search (oriented 145)[159]! (banFrom (fun i => (oriented 145)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_226 : search (oriented 226)[159]! (banFrom (fun i => (oriented 226)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_231 : search (oriented 231)[159]! (banFrom (fun i => (oriented 231)[i]!) 159) 33 = false := by decide +kernel

end Snake9.Dfs
