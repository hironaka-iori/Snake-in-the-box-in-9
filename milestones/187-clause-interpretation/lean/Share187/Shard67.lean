import Share187.Split
import Share187.Piece67_0
import Share187.Piece67_1
import Share187.Piece67_2
import Share187.Piece67_3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.ShareWindow185
open Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185
theorem shard67 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags67 raw67 = true := by
  have h2 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags67.drop 64) (raw67.drop 64) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags67.drop 64) (raw67.drop 64)
    · decide +kernel
    · exact piece67_2
    · simpa only [List.drop_drop,Nat.reduceAdd] using piece67_3
  have h1 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags67.drop 32) (raw67.drop 32) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags67.drop 32) (raw67.drop 32)
    · decide +kernel
    · exact piece67_1
    · simpa only [List.drop_drop,Nat.reduceAdd] using h2
  have h0 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags67 raw67 = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 tags67 raw67
    · decide +kernel
    · exact piece67_0
    · simpa only [List.drop_drop,Nat.reduceAdd] using h1
  exact h0
#print axioms shard67
end Snake9.LocalWindow.ShareWindow185
