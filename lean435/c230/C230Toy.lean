module

public import C230Cover
import LocalWindowCert.V012034A2H644

/-! Toy instance of the K7 cover (milestone 37 pilot): the published pilot certificate
`LocalWindowCert.V012034A2H644` consumed through `C230Cover`, and a main-style lumped key derived from
it by narrowing. No sorry; the certificate module is a private import. -/

@[expose] public section

namespace Snake9.C230Toy
open Snake9 Snake9.LocalWindow Snake9.LocalWindow.Families Snake9.C230

def toyKeys : List (List Nat × List (Nat × Nat)) :=
  [([0, 1, 2, 0, 3, 4], [(2, 2), (8, 21), (6, 6), (4, 4), (4, 4)])]

theorem toy_all : AllRefutedIV toyKeys :=
  ⟨Snake9.LocalWindow.V012034A2H644.refuted, trivial⟩

/-- On every snake, a window with directions `0,1,2,0,3,4` (after relabelling) cannot carry the
counts 2, 8+, 6, 4, 4. -/
theorem toy_window {m : Nat} (p : Snake m) (r : Nat) (hr : r + 6 ≤ m) {u : List Nat}
    (hu : u.Nodup) (hu9 : ∀ d ∈ u, d < 9)
    (hcs : ∀ j, j < 6 → [0, 1, 2, 0, 3, 4].getD j 0 < u.length ∧
      u.getD ([0, 1, 2, 0, 3, 4].getD j 0) 0 = dir p (r + j))
    (hb : ∀ i, i < 5 → ([(2, 2), (8, 21), (6, 6), (4, 4), (4, 4)].getD i (0, 21)).1 ≤ coreAlpha p (r + i + 1) ∧
      coreAlpha p (r + i + 1) ≤ ([(2, 2), (8, 21), (6, 6), (4, 4), (4, 4)].getD i (0, 21)).2) : False :=
  no_window_of_list toy_all (List.mem_singleton.2 rfl) p r rfl hr hu hu9 hcs hb

/-- Narrowing an interval certificate: the exact counts 2, 9, 6, 4, 4 are excluded too. -/
theorem toy_narrow : Refuted (winOf [0, 1, 2, 0, 3, 4]) [(2, 2), (9, 9), (6, 6), (4, 4), (4, 4)] :=
  refuted_narrow Snake9.LocalWindow.V012034A2H644.refuted (by decide)

end Snake9.C230Toy

#print axioms Snake9.C230Toy.toy_window
#print axioms Snake9.C230Toy.toy_narrow
#print axioms Snake9.C230.refutedIV_of_main
