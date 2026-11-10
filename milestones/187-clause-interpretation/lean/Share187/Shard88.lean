import Share187.Split
import Share187.Piece88_0
import Share187.Piece88_1
import Share187.Piece88_2
import Share187.Piece88_3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.ShareWindow185
open Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185
theorem shard88 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags88 raw88 = true := by
  have h2 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags88.drop 64) (raw88.drop 64) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags88.drop 64) (raw88.drop 64)
    · decide +kernel
    · exact piece88_2
    · simpa only [List.drop_drop,Nat.reduceAdd] using piece88_3
  have h1 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags88.drop 32) (raw88.drop 32) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags88.drop 32) (raw88.drop 32)
    · decide +kernel
    · exact piece88_1
    · simpa only [List.drop_drop,Nat.reduceAdd] using h2
  have h0 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags88 raw88 = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 tags88 raw88
    · decide +kernel
    · exact piece88_0
    · simpa only [List.drop_drop,Nat.reduceAdd] using h1
  exact h0
#print axioms shard88
end Snake9.LocalWindow.ShareWindow185
