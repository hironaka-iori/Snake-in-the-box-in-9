import Share187.Split
import Share187.Piece82_0
import Share187.Piece82_1
import Share187.Piece82_2
import Share187.Piece82_3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.ShareWindow185
open Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185
theorem shard82 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags82 raw82 = true := by
  have h2 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags82.drop 64) (raw82.drop 64) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags82.drop 64) (raw82.drop 64)
    · decide +kernel
    · exact piece82_2
    · simpa only [List.drop_drop,Nat.reduceAdd] using piece82_3
  have h1 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags82.drop 32) (raw82.drop 32) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags82.drop 32) (raw82.drop 32)
    · decide +kernel
    · exact piece82_1
    · simpa only [List.drop_drop,Nat.reduceAdd] using h2
  have h0 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags82 raw82 = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 tags82 raw82
    · decide +kernel
    · exact piece82_0
    · simpa only [List.drop_drop,Nat.reduceAdd] using h1
  exact h0
#print axioms shard82
end Snake9.LocalWindow.ShareWindow185
