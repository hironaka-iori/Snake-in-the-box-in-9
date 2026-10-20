/-
Elaboration-time helper of WindowAutomatonLit for 16-bit fields: `spreadBlocks16 C n2 n3 lo hi`
places the blocks `lo .. hi-1` of `n2` 16-bit fields of `C` `n3` fields apart.  Used only inside
`nat_lit%` (the kernel sees the resulting numeral and checks it with `consD16`).
-/
import WindowAutomatonLit

namespace Snake9.WindowAutomaton

partial def spreadBlocks16 (C n2 n3 lo hi : Nat) : Nat :=
  if hi ≤ lo then 0
  else if hi = lo + 1 then (C >>> (16 * n2 * lo)) &&& (2 ^ (16 * n2) - 1)
  else
    let mid := (lo + hi) / 2
    spreadBlocks16 C n2 n3 lo mid ||| (spreadBlocks16 C n2 n3 mid hi <<< (16 * n3 * (mid - lo)))

end Snake9.WindowAutomaton
