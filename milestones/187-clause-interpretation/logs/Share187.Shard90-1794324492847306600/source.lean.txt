import Share187.Split
import Share187.Piece90_0
import Share187.Piece90_1
import Share187.Piece90_2
import Share187.Piece90_3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.ShareWindow185
open Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185
theorem shard90 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags90 raw90 = true := by
  have h2 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags90.drop 64) (raw90.drop 64) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags90.drop 64) (raw90.drop 64)
    · decide +kernel
    · exact piece90_2
    · simpa only [List.drop_drop,Nat.reduceAdd] using piece90_3
  have h1 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags90.drop 32) (raw90.drop 32) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags90.drop 32) (raw90.drop 32)
    · decide +kernel
    · exact piece90_1
    · simpa only [List.drop_drop,Nat.reduceAdd] using h2
  have h0 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags90 raw90 = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 tags90 raw90
    · decide +kernel
    · exact piece90_0
    · simpa only [List.drop_drop,Nat.reduceAdd] using h1
  exact h0
#print axioms shard90
end Snake9.LocalWindow.ShareWindow185
