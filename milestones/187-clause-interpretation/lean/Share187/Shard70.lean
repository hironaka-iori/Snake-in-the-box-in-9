import Share187.Split
import Share187.Piece70_0
import Share187.Piece70_1
import Share187.Piece70_2
import Share187.Piece70_3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.ShareWindow185
open Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185
theorem shard70 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags70 raw70 = true := by
  have h2 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags70.drop 64) (raw70.drop 64) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags70.drop 64) (raw70.drop 64)
    · decide +kernel
    · exact piece70_2
    · simpa only [List.drop_drop,Nat.reduceAdd] using piece70_3
  have h1 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags70.drop 32) (raw70.drop 32) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags70.drop 32) (raw70.drop 32)
    · decide +kernel
    · exact piece70_1
    · simpa only [List.drop_drop,Nat.reduceAdd] using h2
  have h0 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags70 raw70 = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 tags70 raw70
    · decide +kernel
    · exact piece70_0
    · simpa only [List.drop_drop,Nat.reduceAdd] using h1
  exact h0
#print axioms shard70
end Snake9.LocalWindow.ShareWindow185
