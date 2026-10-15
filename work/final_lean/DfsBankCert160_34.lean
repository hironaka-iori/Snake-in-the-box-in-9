import DfsCertificate
import DfsBankData

namespace Snake9.Dfs
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem keep160_5 : search (oriented 5)[159]! (banFrom (fun i => (oriented 5)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_15_8_7_0 : search ((((oriented 15)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 7) ^^^ 2 ^ 0) ((((banFrom (fun i => (oriented 15)[i]!) 159) ||| cnMask (oriented 15)[159]!) ||| cnMask ((oriented 15)[159]! ^^^ 2 ^ 8)) ||| cnMask (((oriented 15)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 7)) 30 = false := by decide +kernel
theorem keep160_15_8_7_3 : search ((((oriented 15)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 7) ^^^ 2 ^ 3) ((((banFrom (fun i => (oriented 15)[i]!) 159) ||| cnMask (oriented 15)[159]!) ||| cnMask ((oriented 15)[159]! ^^^ 2 ^ 8)) ||| cnMask (((oriented 15)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 7)) 30 = false := by decide +kernel
theorem keep160_15_8_7_6 : search ((((oriented 15)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 7) ^^^ 2 ^ 6) ((((banFrom (fun i => (oriented 15)[i]!) 159) ||| cnMask (oriented 15)[159]!) ||| cnMask ((oriented 15)[159]! ^^^ 2 ^ 8)) ||| cnMask (((oriented 15)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 7)) 30 = false := by decide +kernel
theorem keep160_15_8_7 : search (((oriented 15)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 7) (((banFrom (fun i => (oriented 15)[i]!) 159) ||| cnMask (oriented 15)[159]!) ||| cnMask ((oriented 15)[159]! ^^^ 2 ^ 8)) 31 = false :=
  search_of_children (((oriented 15)[159]! ^^^ 2 ^ 8) ^^^ 2 ^ 7) (((banFrom (fun i => (oriented 15)[i]!) 159) ||| cnMask (oriented 15)[159]!) ||| cnMask ((oriented 15)[159]! ^^^ 2 ^ 8)) 30 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inr keep160_15_8_7_0
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inr keep160_15_8_7_3
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inr keep160_15_8_7_6
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_15_8 : search ((oriented 15)[159]! ^^^ 2 ^ 8) ((banFrom (fun i => (oriented 15)[i]!) 159) ||| cnMask (oriented 15)[159]!) 32 = false :=
  search_of_children ((oriented 15)[159]! ^^^ 2 ^ 8) ((banFrom (fun i => (oriented 15)[i]!) 159) ||| cnMask (oriented 15)[159]!) 31 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inr keep160_15_8_7
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_15 : search (oriented 15)[159]! (banFrom (fun i => (oriented 15)[i]!) 159) 33 = false :=
  search_of_children (oriented 15)[159]! (banFrom (fun i => (oriented 15)[i]!) 159) 32 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inl (by decide +kernel)
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inr keep160_15_8
    | n + 9, h => exact absurd h (by omega))
theorem keep160_38 : search (oriented 38)[159]! (banFrom (fun i => (oriented 38)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_66_0_2 : search (((oriented 66)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 2) (((banFrom (fun i => (oriented 66)[i]!) 159) ||| cnMask (oriented 66)[159]!) ||| cnMask ((oriented 66)[159]! ^^^ 2 ^ 0)) 31 = false := by decide +kernel
theorem keep160_66_0_4 : search (((oriented 66)[159]! ^^^ 2 ^ 0) ^^^ 2 ^ 4) (((banFrom (fun i => (oriented 66)[i]!) 159) ||| cnMask (oriented 66)[159]!) ||| cnMask ((oriented 66)[159]! ^^^ 2 ^ 0)) 31 = false := by decide +kernel
theorem keep160_66_0 : search ((oriented 66)[159]! ^^^ 2 ^ 0) ((banFrom (fun i => (oriented 66)[i]!) 159) ||| cnMask (oriented 66)[159]!) 32 = false :=
  search_of_children ((oriented 66)[159]! ^^^ 2 ^ 0) ((banFrom (fun i => (oriented 66)[i]!) 159) ||| cnMask (oriented 66)[159]!) 31 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inl (by decide +kernel)
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inr keep160_66_0_2
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inr keep160_66_0_4
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_66_4 : search ((oriented 66)[159]! ^^^ 2 ^ 4) ((banFrom (fun i => (oriented 66)[i]!) 159) ||| cnMask (oriented 66)[159]!) 32 = false := by decide +kernel
theorem keep160_66 : search (oriented 66)[159]! (banFrom (fun i => (oriented 66)[i]!) 159) 33 = false :=
  search_of_children (oriented 66)[159]! (banFrom (fun i => (oriented 66)[i]!) 159) 32 (fun k hk => by
    match k, hk with
    | 0, _ => exact Or.inr keep160_66_0
    | 1, _ => exact Or.inl (by decide +kernel)
    | 2, _ => exact Or.inl (by decide +kernel)
    | 3, _ => exact Or.inl (by decide +kernel)
    | 4, _ => exact Or.inr keep160_66_4
    | 5, _ => exact Or.inl (by decide +kernel)
    | 6, _ => exact Or.inl (by decide +kernel)
    | 7, _ => exact Or.inl (by decide +kernel)
    | 8, _ => exact Or.inl (by decide +kernel)
    | n + 9, h => exact absurd h (by omega))
theorem keep160_124 : search (oriented 124)[159]! (banFrom (fun i => (oriented 124)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_202 : search (oriented 202)[159]! (banFrom (fun i => (oriented 202)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_227 : search (oriented 227)[159]! (banFrom (fun i => (oriented 227)[i]!) 159) 33 = false := by decide +kernel
theorem keep160_244 : search (oriented 244)[159]! (banFrom (fun i => (oriented 244)[i]!) 159) 33 = false := by decide +kernel

end Snake9.Dfs
