import Share187.Split
import Share187.Piece40_0
import Share187.Piece40_1
import Share187.Piece40_2
import Share187.Piece40_3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.ShareWindow185
open Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185
theorem shard40 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags40 raw40 = true := by
  have h2 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags40.drop 64) (raw40.drop 64) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags40.drop 64) (raw40.drop 64)
    · decide +kernel
    · exact piece40_2
    · simpa only [List.drop_drop,Nat.reduceAdd] using piece40_3
  have h1 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags40.drop 32) (raw40.drop 32) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags40.drop 32) (raw40.drop 32)
    · decide +kernel
    · exact piece40_1
    · simpa only [List.drop_drop,Nat.reduceAdd] using h2
  have h0 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags40 raw40 = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 tags40 raw40
    · decide +kernel
    · exact piece40_0
    · simpa only [List.drop_drop,Nat.reduceAdd] using h1
  exact h0
#print axioms shard40
end Snake9.LocalWindow.ShareWindow185
