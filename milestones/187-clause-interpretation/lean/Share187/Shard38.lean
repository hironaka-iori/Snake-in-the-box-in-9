import Share187.Split
import Share187.Cut38_00
import Share187.Cut38_01
import Share187.Cut38_02
import Share187.Cut38_03
import Share187.Cut38_04
import Share187.Cut38_05
import Share187.Cut38_06
import Share187.Cut38_07
import Share187.Cut38_08
import Share187.Cut38_09
import Share187.Cut38_10
import Share187.Cut38_11
import Share187.Cut38_12
import Share187.Cut38_13
import Share187.Cut38_14
import Share187.Cut38_15
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.ShareWindow185
open Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185
theorem shard38 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags38 raw38 = true := by
  have h14 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags38.drop 112) (raw38.drop 112) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 8 (tags38.drop 112) (raw38.drop 112)
    · decide +kernel
    · exact cut38_14
    · simpa only [List.drop_drop,Nat.reduceAdd] using cut38_15
  have h13 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags38.drop 104) (raw38.drop 104) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 8 (tags38.drop 104) (raw38.drop 104)
    · decide +kernel
    · exact cut38_13
    · simpa only [List.drop_drop,Nat.reduceAdd] using h14
  have h12 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags38.drop 96) (raw38.drop 96) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 8 (tags38.drop 96) (raw38.drop 96)
    · decide +kernel
    · exact cut38_12
    · simpa only [List.drop_drop,Nat.reduceAdd] using h13
  have h11 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags38.drop 88) (raw38.drop 88) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 8 (tags38.drop 88) (raw38.drop 88)
    · decide +kernel
    · exact cut38_11
    · simpa only [List.drop_drop,Nat.reduceAdd] using h12
  have h10 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags38.drop 80) (raw38.drop 80) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 8 (tags38.drop 80) (raw38.drop 80)
    · decide +kernel
    · exact cut38_10
    · simpa only [List.drop_drop,Nat.reduceAdd] using h11
  have h9 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags38.drop 72) (raw38.drop 72) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 8 (tags38.drop 72) (raw38.drop 72)
    · decide +kernel
    · exact cut38_9
    · simpa only [List.drop_drop,Nat.reduceAdd] using h10
  have h8 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags38.drop 64) (raw38.drop 64) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 8 (tags38.drop 64) (raw38.drop 64)
    · decide +kernel
    · exact cut38_8
    · simpa only [List.drop_drop,Nat.reduceAdd] using h9
  have h7 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags38.drop 56) (raw38.drop 56) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 8 (tags38.drop 56) (raw38.drop 56)
    · decide +kernel
    · exact cut38_7
    · simpa only [List.drop_drop,Nat.reduceAdd] using h8
  have h6 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags38.drop 48) (raw38.drop 48) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 8 (tags38.drop 48) (raw38.drop 48)
    · decide +kernel
    · exact cut38_6
    · simpa only [List.drop_drop,Nat.reduceAdd] using h7
  have h5 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags38.drop 40) (raw38.drop 40) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 8 (tags38.drop 40) (raw38.drop 40)
    · decide +kernel
    · exact cut38_5
    · simpa only [List.drop_drop,Nat.reduceAdd] using h6
  have h4 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags38.drop 32) (raw38.drop 32) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 8 (tags38.drop 32) (raw38.drop 32)
    · decide +kernel
    · exact cut38_4
    · simpa only [List.drop_drop,Nat.reduceAdd] using h5
  have h3 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags38.drop 24) (raw38.drop 24) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 8 (tags38.drop 24) (raw38.drop 24)
    · decide +kernel
    · exact cut38_3
    · simpa only [List.drop_drop,Nat.reduceAdd] using h4
  have h2 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags38.drop 16) (raw38.drop 16) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 8 (tags38.drop 16) (raw38.drop 16)
    · decide +kernel
    · exact cut38_2
    · simpa only [List.drop_drop,Nat.reduceAdd] using h3
  have h1 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap (tags38.drop 8) (raw38.drop 8) = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 8 (tags38.drop 8) (raw38.drop 8)
    · decide +kernel
    · exact cut38_1
    · simpa only [List.drop_drop,Nat.reduceAdd] using h2
  have h0 : ckAllS meaningDirect smeaningDirect resolution ctrs tots window cap tags38 raw38 = true := by
    apply ckAllS_of_split meaningDirect smeaningDirect resolution ctrs tots window cap 8 tags38 raw38
    · decide +kernel
    · exact cut38_0
    · simpa only [List.drop_drop,Nat.reduceAdd] using h1
  exact h0
#print axioms shard38
end Snake9.LocalWindow.ShareWindow185
