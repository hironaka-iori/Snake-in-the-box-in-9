import Share187.Split
import Share187.Piece86_0
import Share187.Piece86_1
import Share187.Piece86_2
import Share187.Piece86_3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.ShareWindow185
open Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185
theorem shard86 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags86 raw86 = true := by
  have h2 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags86.drop 64) (raw86.drop 64) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags86.drop 64) (raw86.drop 64)
    · decide +kernel
    · exact piece86_2
    · simpa only [List.drop_drop,Nat.reduceAdd] using piece86_3
  have h1 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags86.drop 32) (raw86.drop 32) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags86.drop 32) (raw86.drop 32)
    · decide +kernel
    · exact piece86_1
    · simpa only [List.drop_drop,Nat.reduceAdd] using h2
  have h0 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags86 raw86 = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 tags86 raw86
    · decide +kernel
    · exact piece86_0
    · simpa only [List.drop_drop,Nat.reduceAdd] using h1
  exact h0
#print axioms shard86
end Snake9.LocalWindow.ShareWindow185
