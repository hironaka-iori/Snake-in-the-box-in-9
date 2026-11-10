import Share187.Split
import Share187.Piece60_0
import Share187.Piece60_1
import Share187.Piece60_2
import Share187.Piece60_3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.ShareWindow185
open Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185
theorem shard60 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags60 raw60 = true := by
  have h2 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags60.drop 64) (raw60.drop 64) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags60.drop 64) (raw60.drop 64)
    · decide +kernel
    · exact piece60_2
    · simpa only [List.drop_drop,Nat.reduceAdd] using piece60_3
  have h1 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags60.drop 32) (raw60.drop 32) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags60.drop 32) (raw60.drop 32)
    · decide +kernel
    · exact piece60_1
    · simpa only [List.drop_drop,Nat.reduceAdd] using h2
  have h0 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags60 raw60 = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 tags60 raw60
    · decide +kernel
    · exact piece60_0
    · simpa only [List.drop_drop,Nat.reduceAdd] using h1
  exact h0
#print axioms shard60
end Snake9.LocalWindow.ShareWindow185
