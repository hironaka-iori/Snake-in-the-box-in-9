import Share187.Split
import Share187.Piece83_0
import Share187.Piece83_1
import Share187.Piece83_2
import Share187.Piece83_3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.ShareWindow185
open Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185
theorem shard83 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags83 raw83 = true := by
  have h2 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags83.drop 64) (raw83.drop 64) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags83.drop 64) (raw83.drop 64)
    · decide +kernel
    · exact piece83_2
    · simpa only [List.drop_drop,Nat.reduceAdd] using piece83_3
  have h1 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags83.drop 32) (raw83.drop 32) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags83.drop 32) (raw83.drop 32)
    · decide +kernel
    · exact piece83_1
    · simpa only [List.drop_drop,Nat.reduceAdd] using h2
  have h0 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags83 raw83 = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 tags83 raw83
    · decide +kernel
    · exact piece83_0
    · simpa only [List.drop_drop,Nat.reduceAdd] using h1
  exact h0
#print axioms shard83
end Snake9.LocalWindow.ShareWindow185
