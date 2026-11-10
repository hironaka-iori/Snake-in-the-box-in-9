import Share187.Split
import Share187.Piece56_0
import Share187.Piece56_1
import Share187.Piece56_2
import Share187.Piece56_3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.ShareWindow185
open Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185
theorem shard56 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags56 raw56 = true := by
  have h2 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags56.drop 64) (raw56.drop 64) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags56.drop 64) (raw56.drop 64)
    · decide +kernel
    · exact piece56_2
    · simpa only [List.drop_drop,Nat.reduceAdd] using piece56_3
  have h1 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags56.drop 32) (raw56.drop 32) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags56.drop 32) (raw56.drop 32)
    · decide +kernel
    · exact piece56_1
    · simpa only [List.drop_drop,Nat.reduceAdd] using h2
  have h0 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags56 raw56 = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 tags56 raw56
    · decide +kernel
    · exact piece56_0
    · simpa only [List.drop_drop,Nat.reduceAdd] using h1
  exact h0
#print axioms shard56
end Snake9.LocalWindow.ShareWindow185
