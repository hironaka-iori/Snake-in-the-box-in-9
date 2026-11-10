import Share187.Split
import Share187.Piece51_0
import Share187.Piece51_1
import Share187.Piece51_2
import Share187.Piece51_3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.ShareWindow185
open Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185
theorem shard51 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags51 raw51 = true := by
  have h2 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags51.drop 64) (raw51.drop 64) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags51.drop 64) (raw51.drop 64)
    · decide +kernel
    · exact piece51_2
    · simpa only [List.drop_drop,Nat.reduceAdd] using piece51_3
  have h1 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags51.drop 32) (raw51.drop 32) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags51.drop 32) (raw51.drop 32)
    · decide +kernel
    · exact piece51_1
    · simpa only [List.drop_drop,Nat.reduceAdd] using h2
  have h0 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags51 raw51 = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 tags51 raw51
    · decide +kernel
    · exact piece51_0
    · simpa only [List.drop_drop,Nat.reduceAdd] using h1
  exact h0
#print axioms shard51
end Snake9.LocalWindow.ShareWindow185
