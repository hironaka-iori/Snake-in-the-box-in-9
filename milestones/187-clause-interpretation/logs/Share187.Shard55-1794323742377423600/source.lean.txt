import Share187.Split
import Share187.Piece55_0
import Share187.Piece55_1
import Share187.Piece55_2
import Share187.Piece55_3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.ShareWindow185
open Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185
theorem shard55 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags55 raw55 = true := by
  have h2 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags55.drop 64) (raw55.drop 64) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags55.drop 64) (raw55.drop 64)
    · decide +kernel
    · exact piece55_2
    · simpa only [List.drop_drop,Nat.reduceAdd] using piece55_3
  have h1 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags55.drop 32) (raw55.drop 32) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags55.drop 32) (raw55.drop 32)
    · decide +kernel
    · exact piece55_1
    · simpa only [List.drop_drop,Nat.reduceAdd] using h2
  have h0 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags55 raw55 = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 tags55 raw55
    · decide +kernel
    · exact piece55_0
    · simpa only [List.drop_drop,Nat.reduceAdd] using h1
  exact h0
#print axioms shard55
end Snake9.LocalWindow.ShareWindow185
