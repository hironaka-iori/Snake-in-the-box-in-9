import LocalWindowUnsat.CycleWindow381.Data0

/-! LRAT refutation of the core of `cycle381`: segment 1 of 1 (generated). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Snake9.LocalWindow.CycleWindow381
open Snake9.LratFast
open Snake9.Lrat (Tree TreeTrue andB)

noncomputable def proof1 : List Nat := [
  nat_lit 0x2801000400600012c6004,
  nat_lit 0x3801000600100012ca008,
  nat_lit 0x10020000012004,
  nat_lit 0x30020000014004,
  nat_lit 0x50020000016004,
  nat_lit 0x70020000018004,
  nat_lit 0x9002000001a004,
  nat_lit 0xb002000001c004,
  nat_lit 0xd0020020000008]

end Snake9.LocalWindow.CycleWindow381
