import Share187.Split
import Share187.Piece61_0
import Share187.Piece61_1
import Share187.Piece61_2
import Share187.Piece61_3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.ShareWindow185
open Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185
theorem shard61 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags61 raw61 = true := by
  have h2 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags61.drop 64) (raw61.drop 64) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags61.drop 64) (raw61.drop 64)
    · decide +kernel
    · exact piece61_2
    · simpa only [List.drop_drop,Nat.reduceAdd] using piece61_3
  have h1 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags61.drop 32) (raw61.drop 32) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags61.drop 32) (raw61.drop 32)
    · decide +kernel
    · exact piece61_1
    · simpa only [List.drop_drop,Nat.reduceAdd] using h2
  have h0 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags61 raw61 = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 tags61 raw61
    · decide +kernel
    · exact piece61_0
    · simpa only [List.drop_drop,Nat.reduceAdd] using h1
  exact h0
#print axioms shard61
end Snake9.LocalWindow.ShareWindow185
