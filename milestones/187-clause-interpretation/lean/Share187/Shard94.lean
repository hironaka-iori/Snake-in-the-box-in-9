import Share187.Split
import Share187.Piece94_0
import Share187.Piece94_1
import Share187.Piece94_2
import Share187.Piece94_3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.ShareWindow185
open Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185
theorem shard94 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags94 raw94 = true := by
  have h2 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags94.drop 64) (raw94.drop 64) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags94.drop 64) (raw94.drop 64)
    · decide +kernel
    · exact piece94_2
    · simpa only [List.drop_drop,Nat.reduceAdd] using piece94_3
  have h1 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags94.drop 32) (raw94.drop 32) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags94.drop 32) (raw94.drop 32)
    · decide +kernel
    · exact piece94_1
    · simpa only [List.drop_drop,Nat.reduceAdd] using h2
  have h0 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags94 raw94 = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 tags94 raw94
    · decide +kernel
    · exact piece94_0
    · simpa only [List.drop_drop,Nat.reduceAdd] using h1
  exact h0
#print axioms shard94
end Snake9.LocalWindow.ShareWindow185
