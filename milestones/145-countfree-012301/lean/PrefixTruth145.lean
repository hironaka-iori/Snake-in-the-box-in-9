import ChunkTruthAssemblyFixed145
import LiteralProbe144

namespace Snake9.PrefixTruth145

theorem checked_prefix_true (τ : Nat → Bool)
    (h : Snake9.LocalWindow.cnfTrue τ Snake9.LocalWindow.ShareWindow144.cnf = true) :
    Snake9.Lrat144.TreeTrue τ
      (Snake9.LratFast144.replay Snake9.LiteralData144.start Snake9.LiteralProbe144.proof) := by
  exact Snake9.LratFast144.replay_true τ
    Snake9.LiteralProbe144.first_segment (Snake9.ChunkData145.start_true τ h)

#print axioms checked_prefix_true

end Snake9.PrefixTruth145
