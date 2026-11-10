import Share187.Split
import Share187.Piece59_0
import Share187.Piece59_1
import Share187.Piece59_2
import Share187.Piece59_3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.ShareWindow185
open Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185
theorem shard59 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags59 raw59 = true := by
  have h2 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags59.drop 64) (raw59.drop 64) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags59.drop 64) (raw59.drop 64)
    · decide +kernel
    · exact piece59_2
    · simpa only [List.drop_drop,Nat.reduceAdd] using piece59_3
  have h1 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags59.drop 32) (raw59.drop 32) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags59.drop 32) (raw59.drop 32)
    · decide +kernel
    · exact piece59_1
    · simpa only [List.drop_drop,Nat.reduceAdd] using h2
  have h0 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags59 raw59 = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 tags59 raw59
    · decide +kernel
    · exact piece59_0
    · simpa only [List.drop_drop,Nat.reduceAdd] using h1
  exact h0
#print axioms shard59
end Snake9.LocalWindow.ShareWindow185
