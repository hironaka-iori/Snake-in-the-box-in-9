import Share187.Split
import Share187.Piece92_0
import Share187.Piece92_1
import Share187.Piece92_2
import Share187.Piece92_3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.ShareWindow185
open Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185
theorem shard92 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags92 raw92 = true := by
  have h2 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags92.drop 64) (raw92.drop 64) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags92.drop 64) (raw92.drop 64)
    · decide +kernel
    · exact piece92_2
    · simpa only [List.drop_drop,Nat.reduceAdd] using piece92_3
  have h1 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags92.drop 32) (raw92.drop 32) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags92.drop 32) (raw92.drop 32)
    · decide +kernel
    · exact piece92_1
    · simpa only [List.drop_drop,Nat.reduceAdd] using h2
  have h0 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags92 raw92 = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 tags92 raw92
    · decide +kernel
    · exact piece92_0
    · simpa only [List.drop_drop,Nat.reduceAdd] using h1
  exact h0
#print axioms shard92
end Snake9.LocalWindow.ShareWindow185
