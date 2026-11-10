import Share187.Split
import Share187.Piece57_0
import Share187.Piece57_1
import Share187.Piece57_2
import Share187.Piece57_3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.ShareWindow185
open Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185
theorem shard57 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags57 raw57 = true := by
  have h2 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags57.drop 64) (raw57.drop 64) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags57.drop 64) (raw57.drop 64)
    · decide +kernel
    · exact piece57_2
    · simpa only [List.drop_drop,Nat.reduceAdd] using piece57_3
  have h1 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags57.drop 32) (raw57.drop 32) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags57.drop 32) (raw57.drop 32)
    · decide +kernel
    · exact piece57_1
    · simpa only [List.drop_drop,Nat.reduceAdd] using h2
  have h0 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags57 raw57 = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 tags57 raw57
    · decide +kernel
    · exact piece57_0
    · simpa only [List.drop_drop,Nat.reduceAdd] using h1
  exact h0
#print axioms shard57
end Snake9.LocalWindow.ShareWindow185
