import Share187.Split
import Share187.Piece52_0
import Share187.Piece52_1
import Share187.Piece52_2
import Share187.Piece52_3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.ShareWindow185
open Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185
theorem shard52 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags52 raw52 = true := by
  have h2 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags52.drop 64) (raw52.drop 64) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags52.drop 64) (raw52.drop 64)
    · decide +kernel
    · exact piece52_2
    · simpa only [List.drop_drop,Nat.reduceAdd] using piece52_3
  have h1 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags52.drop 32) (raw52.drop 32) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags52.drop 32) (raw52.drop 32)
    · decide +kernel
    · exact piece52_1
    · simpa only [List.drop_drop,Nat.reduceAdd] using h2
  have h0 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags52 raw52 = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 tags52 raw52
    · decide +kernel
    · exact piece52_0
    · simpa only [List.drop_drop,Nat.reduceAdd] using h1
  exact h0
#print axioms shard52
end Snake9.LocalWindow.ShareWindow185
