import Share187.Split
import Share187.Piece85_0
import Share187.Piece85_1
import Share187.Piece85_2
import Share187.Piece85_3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.ShareWindow185
open Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185
theorem shard85 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags85 raw85 = true := by
  have h2 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags85.drop 64) (raw85.drop 64) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags85.drop 64) (raw85.drop 64)
    · decide +kernel
    · exact piece85_2
    · simpa only [List.drop_drop,Nat.reduceAdd] using piece85_3
  have h1 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags85.drop 32) (raw85.drop 32) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags85.drop 32) (raw85.drop 32)
    · decide +kernel
    · exact piece85_1
    · simpa only [List.drop_drop,Nat.reduceAdd] using h2
  have h0 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags85 raw85 = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 tags85 raw85
    · decide +kernel
    · exact piece85_0
    · simpa only [List.drop_drop,Nat.reduceAdd] using h1
  exact h0
#print axioms shard85
end Snake9.LocalWindow.ShareWindow185
