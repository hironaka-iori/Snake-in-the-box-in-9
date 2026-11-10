import Share187.Split
import Share187.Piece89_0
import Share187.Piece89_1
import Share187.Piece89_2
import Share187.Piece89_3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.ShareWindow185
open Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185
theorem shard89 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags89 raw89 = true := by
  have h2 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags89.drop 64) (raw89.drop 64) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags89.drop 64) (raw89.drop 64)
    · decide +kernel
    · exact piece89_2
    · simpa only [List.drop_drop,Nat.reduceAdd] using piece89_3
  have h1 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags89.drop 32) (raw89.drop 32) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags89.drop 32) (raw89.drop 32)
    · decide +kernel
    · exact piece89_1
    · simpa only [List.drop_drop,Nat.reduceAdd] using h2
  have h0 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags89 raw89 = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 tags89 raw89
    · decide +kernel
    · exact piece89_0
    · simpa only [List.drop_drop,Nat.reduceAdd] using h1
  exact h0
#print axioms shard89
end Snake9.LocalWindow.ShareWindow185
