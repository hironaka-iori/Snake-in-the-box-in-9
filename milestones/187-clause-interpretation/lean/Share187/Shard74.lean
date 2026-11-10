import Share187.Split
import Share187.Piece74_0
import Share187.Piece74_1
import Share187.Piece74_2
import Share187.Piece74_3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.ShareWindow185
open Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185
theorem shard74 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags74 raw74 = true := by
  have h2 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags74.drop 64) (raw74.drop 64) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags74.drop 64) (raw74.drop 64)
    · decide +kernel
    · exact piece74_2
    · simpa only [List.drop_drop,Nat.reduceAdd] using piece74_3
  have h1 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags74.drop 32) (raw74.drop 32) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags74.drop 32) (raw74.drop 32)
    · decide +kernel
    · exact piece74_1
    · simpa only [List.drop_drop,Nat.reduceAdd] using h2
  have h0 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags74 raw74 = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 tags74 raw74
    · decide +kernel
    · exact piece74_0
    · simpa only [List.drop_drop,Nat.reduceAdd] using h1
  exact h0
#print axioms shard74
end Snake9.LocalWindow.ShareWindow185
