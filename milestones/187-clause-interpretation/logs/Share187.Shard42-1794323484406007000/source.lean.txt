import Share187.Split
import Share187.Piece42_0
import Share187.Piece42_1
import Share187.Piece42_2
import Share187.Piece42_3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.ShareWindow185
open Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185
theorem shard42 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags42 raw42 = true := by
  have h2 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags42.drop 64) (raw42.drop 64) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags42.drop 64) (raw42.drop 64)
    · decide +kernel
    · exact piece42_2
    · simpa only [List.drop_drop,Nat.reduceAdd] using piece42_3
  have h1 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags42.drop 32) (raw42.drop 32) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags42.drop 32) (raw42.drop 32)
    · decide +kernel
    · exact piece42_1
    · simpa only [List.drop_drop,Nat.reduceAdd] using h2
  have h0 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags42 raw42 = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 tags42 raw42
    · decide +kernel
    · exact piece42_0
    · simpa only [List.drop_drop,Nat.reduceAdd] using h1
  exact h0
#print axioms shard42
end Snake9.LocalWindow.ShareWindow185
