import Share187.Split
import Share187.Piece93_0
import Share187.Piece93_1
import Share187.Piece93_2
import Share187.Piece93_3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.ShareWindow185
open Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185
theorem shard93 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags93 raw93 = true := by
  have h2 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags93.drop 64) (raw93.drop 64) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags93.drop 64) (raw93.drop 64)
    · decide +kernel
    · exact piece93_2
    · simpa only [List.drop_drop,Nat.reduceAdd] using piece93_3
  have h1 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags93.drop 32) (raw93.drop 32) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags93.drop 32) (raw93.drop 32)
    · decide +kernel
    · exact piece93_1
    · simpa only [List.drop_drop,Nat.reduceAdd] using h2
  have h0 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags93 raw93 = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 tags93 raw93
    · decide +kernel
    · exact piece93_0
    · simpa only [List.drop_drop,Nat.reduceAdd] using h1
  exact h0
#print axioms shard93
end Snake9.LocalWindow.ShareWindow185
