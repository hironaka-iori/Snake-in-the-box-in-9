import Share187.Split
import Share187.Piece41_0
import Share187.Piece41_1
import Share187.Piece41_2
import Share187.Piece41_3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.ShareWindow185
open Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185
theorem shard41 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags41 raw41 = true := by
  have h2 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags41.drop 64) (raw41.drop 64) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags41.drop 64) (raw41.drop 64)
    · decide +kernel
    · exact piece41_2
    · simpa only [List.drop_drop,Nat.reduceAdd] using piece41_3
  have h1 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags41.drop 32) (raw41.drop 32) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags41.drop 32) (raw41.drop 32)
    · decide +kernel
    · exact piece41_1
    · simpa only [List.drop_drop,Nat.reduceAdd] using h2
  have h0 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags41 raw41 = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 tags41 raw41
    · decide +kernel
    · exact piece41_0
    · simpa only [List.drop_drop,Nat.reduceAdd] using h1
  exact h0
#print axioms shard41
end Snake9.LocalWindow.ShareWindow185
