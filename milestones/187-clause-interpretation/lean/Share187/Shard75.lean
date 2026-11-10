import Share187.Split
import Share187.Piece75_0
import Share187.Piece75_1
import Share187.Piece75_2
import Share187.Piece75_3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.ShareWindow185
open Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185
theorem shard75 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags75 raw75 = true := by
  have h2 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags75.drop 64) (raw75.drop 64) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags75.drop 64) (raw75.drop 64)
    · decide +kernel
    · exact piece75_2
    · simpa only [List.drop_drop,Nat.reduceAdd] using piece75_3
  have h1 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags75.drop 32) (raw75.drop 32) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags75.drop 32) (raw75.drop 32)
    · decide +kernel
    · exact piece75_1
    · simpa only [List.drop_drop,Nat.reduceAdd] using h2
  have h0 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags75 raw75 = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 tags75 raw75
    · decide +kernel
    · exact piece75_0
    · simpa only [List.drop_drop,Nat.reduceAdd] using h1
  exact h0
#print axioms shard75
end Snake9.LocalWindow.ShareWindow185
