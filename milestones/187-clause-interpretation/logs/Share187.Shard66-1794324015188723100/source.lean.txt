import Share187.Split
import Share187.Piece66_0
import Share187.Piece66_1
import Share187.Piece66_2
import Share187.Piece66_3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.ShareWindow185
open Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185
theorem shard66 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags66 raw66 = true := by
  have h2 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags66.drop 64) (raw66.drop 64) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags66.drop 64) (raw66.drop 64)
    · decide +kernel
    · exact piece66_2
    · simpa only [List.drop_drop,Nat.reduceAdd] using piece66_3
  have h1 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags66.drop 32) (raw66.drop 32) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags66.drop 32) (raw66.drop 32)
    · decide +kernel
    · exact piece66_1
    · simpa only [List.drop_drop,Nat.reduceAdd] using h2
  have h0 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags66 raw66 = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 tags66 raw66
    · decide +kernel
    · exact piece66_0
    · simpa only [List.drop_drop,Nat.reduceAdd] using h1
  exact h0
#print axioms shard66
end Snake9.LocalWindow.ShareWindow185
