import Share187.Split
import Share187.Piece87_0
import Share187.Piece87_1
import Share187.Piece87_2
import Share187.Piece87_3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.ShareWindow185
open Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185
theorem shard87 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags87 raw87 = true := by
  have h2 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags87.drop 64) (raw87.drop 64) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags87.drop 64) (raw87.drop 64)
    · decide +kernel
    · exact piece87_2
    · simpa only [List.drop_drop,Nat.reduceAdd] using piece87_3
  have h1 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags87.drop 32) (raw87.drop 32) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags87.drop 32) (raw87.drop 32)
    · decide +kernel
    · exact piece87_1
    · simpa only [List.drop_drop,Nat.reduceAdd] using h2
  have h0 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags87 raw87 = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 tags87 raw87
    · decide +kernel
    · exact piece87_0
    · simpa only [List.drop_drop,Nat.reduceAdd] using h1
  exact h0
#print axioms shard87
end Snake9.LocalWindow.ShareWindow185
