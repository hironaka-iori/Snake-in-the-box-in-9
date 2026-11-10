import Share187.Split
import Share187.Piece96_0
import Share187.Piece96_1
import Share187.Piece96_2
import Share187.Piece96_3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.ShareWindow185
open Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185
theorem shard96 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags96 raw96 = true := by
  have h2 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags96.drop 64) (raw96.drop 64) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags96.drop 64) (raw96.drop 64)
    · decide +kernel
    · exact piece96_2
    · simpa only [List.drop_drop,Nat.reduceAdd] using piece96_3
  have h1 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags96.drop 32) (raw96.drop 32) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 (tags96.drop 32) (raw96.drop 32)
    · decide +kernel
    · exact piece96_1
    · simpa only [List.drop_drop,Nat.reduceAdd] using h2
  have h0 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags96 raw96 = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 32 tags96 raw96
    · decide +kernel
    · exact piece96_0
    · simpa only [List.drop_drop,Nat.reduceAdd] using h1
  exact h0
#print axioms shard96
end Snake9.LocalWindow.ShareWindow185
