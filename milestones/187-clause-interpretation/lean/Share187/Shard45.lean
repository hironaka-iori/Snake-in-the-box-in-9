import Share187.Split
import Share187.Piece45_0
import Share187.Piece45_1
import Share187.Piece45_2
import Share187.Piece45_3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.ShareWindow185
open Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185
theorem shard45 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags45 raw45 = true := by
  have h2 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags45.drop 64) (raw45.drop 64) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags45.drop 64) (raw45.drop 64)
    · decide +kernel
    · exact piece45_2
    · simpa only [List.drop_drop,Nat.reduceAdd] using piece45_3
  have h1 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags45.drop 32) (raw45.drop 32) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags45.drop 32) (raw45.drop 32)
    · decide +kernel
    · exact piece45_1
    · simpa only [List.drop_drop,Nat.reduceAdd] using h2
  have h0 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags45 raw45 = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 tags45 raw45
    · decide +kernel
    · exact piece45_0
    · simpa only [List.drop_drop,Nat.reduceAdd] using h1
  exact h0
#print axioms shard45
end Snake9.LocalWindow.ShareWindow185
