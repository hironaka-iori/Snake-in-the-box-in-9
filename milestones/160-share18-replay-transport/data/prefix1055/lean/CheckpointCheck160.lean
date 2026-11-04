import CheckpointData160
import LiteralProbe144
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace Snake9.Checkpoint160
theorem checkpoint_ok : Snake9.LratFast144.cpOk
    (Snake9.LratFast144.replay Snake9.LiteralData144.start Snake9.LiteralProbe144.proof)
    afterPrefix = true := by
  decide +kernel
#print axioms checkpoint_ok
end Snake9.Checkpoint160
