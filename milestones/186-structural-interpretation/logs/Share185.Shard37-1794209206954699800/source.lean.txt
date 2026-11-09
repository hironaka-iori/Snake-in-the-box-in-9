import Share186.ClauseAppend
import Share186.Clause37Left
import Share186.Clause37Right
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.ShareWindow185
open Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185
theorem shard37 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags37 raw37 = true := by
  have hlen : (tags37.take 64).length = (raw37.take 64).length := by decide +kernel
  have h := ckAllS_append_true meaningDirect smeaningDirect resolution ctrs tots window cap (tags37.take 64) (tags37.drop 64)
    (raw37.take 64) (raw37.drop 64) hlen clause37Left clause37Right
  simpa only [List.take_append_drop] using h
#print axioms shard37
end Snake9.LocalWindow.ShareWindow185
