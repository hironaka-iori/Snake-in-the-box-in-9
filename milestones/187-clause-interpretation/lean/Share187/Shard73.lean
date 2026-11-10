import Share187.Split
import Share187.Piece73_0
import Share187.Piece73_1
import Share187.Piece73_2
import Share187.Piece73_3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.ShareWindow185
open Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185
theorem shard73 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags73 raw73 = true := by
  have h2 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags73.drop 64) (raw73.drop 64) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags73.drop 64) (raw73.drop 64)
    · decide +kernel
    · exact piece73_2
    · simpa only [List.drop_drop,Nat.reduceAdd] using piece73_3
  have h1 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags73.drop 32) (raw73.drop 32) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags73.drop 32) (raw73.drop 32)
    · decide +kernel
    · exact piece73_1
    · simpa only [List.drop_drop,Nat.reduceAdd] using h2
  have h0 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags73 raw73 = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 tags73 raw73
    · decide +kernel
    · exact piece73_0
    · simpa only [List.drop_drop,Nat.reduceAdd] using h1
  exact h0
#print axioms shard73
end Snake9.LocalWindow.ShareWindow185
