import Share187.Split
import Share187.Piece47_0
import Share187.Piece47_1
import Share187.Piece47_2
import Share187.Piece47_3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.ShareWindow185
open Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185
theorem shard47 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags47 raw47 = true := by
  have h2 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags47.drop 64) (raw47.drop 64) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags47.drop 64) (raw47.drop 64)
    · decide +kernel
    · exact piece47_2
    · simpa only [List.drop_drop,Nat.reduceAdd] using piece47_3
  have h1 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags47.drop 32) (raw47.drop 32) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags47.drop 32) (raw47.drop 32)
    · decide +kernel
    · exact piece47_1
    · simpa only [List.drop_drop,Nat.reduceAdd] using h2
  have h0 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags47 raw47 = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 tags47 raw47
    · decide +kernel
    · exact piece47_0
    · simpa only [List.drop_drop,Nat.reduceAdd] using h1
  exact h0
#print axioms shard47
end Snake9.LocalWindow.ShareWindow185
