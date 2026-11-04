import ReplayCheck161_00864
import ReplayCheck161_00868
import ReplayCheck161_00872
import ReplayCheck161_00876
import ReplayCheck161_00880
import ReplayCheck161_00884
import ReplayCheck161_00888
import ReplayCheck161_00892
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps27 (τ : Nat → Bool) (h864 : TreeTrue τ start864) : TreeTrue τ start896 := by
  have h865 : TreeTrue τ start865 := replay_true τ ok864 h864
  have h866 : TreeTrue τ start866 := replay_true τ ok865 h865
  have h867 : TreeTrue τ start867 := replay_true τ ok866 h866
  have h868 : TreeTrue τ start868 := replay_true τ ok867 h867
  have h869 : TreeTrue τ start869 := replay_true τ ok868 h868
  have h870 : TreeTrue τ start870 := replay_true τ ok869 h869
  have h871 : TreeTrue τ start871 := replay_true τ ok870 h870
  have h872 : TreeTrue τ start872 := replay_true τ ok871 h871
  have h873 : TreeTrue τ start873 := replay_true τ ok872 h872
  have h874 : TreeTrue τ start874 := replay_true τ ok873 h873
  have h875 : TreeTrue τ start875 := replay_true τ ok874 h874
  have h876 : TreeTrue τ start876 := replay_true τ ok875 h875
  have h877 : TreeTrue τ start877 := replay_true τ ok876 h876
  have h878 : TreeTrue τ start878 := replay_true τ ok877 h877
  have h879 : TreeTrue τ start879 := replay_true τ ok878 h878
  have h880 : TreeTrue τ start880 := replay_true τ ok879 h879
  have h881 : TreeTrue τ start881 := replay_true τ ok880 h880
  have h882 : TreeTrue τ start882 := replay_true τ ok881 h881
  have h883 : TreeTrue τ start883 := replay_true τ ok882 h882
  have h884 : TreeTrue τ start884 := replay_true τ ok883 h883
  have h885 : TreeTrue τ start885 := replay_true τ ok884 h884
  have h886 : TreeTrue τ start886 := replay_true τ ok885 h885
  have h887 : TreeTrue τ start887 := replay_true τ ok886 h886
  have h888 : TreeTrue τ start888 := replay_true τ ok887 h887
  have h889 : TreeTrue τ start889 := replay_true τ ok888 h888
  have h890 : TreeTrue τ start890 := replay_true τ ok889 h889
  have h891 : TreeTrue τ start891 := replay_true τ ok890 h890
  have h892 : TreeTrue τ start892 := replay_true τ ok891 h891
  have h893 : TreeTrue τ start893 := replay_true τ ok892 h892
  have h894 : TreeTrue τ start894 := replay_true τ ok893 h893
  have h895 : TreeTrue τ start895 := replay_true τ ok894 h894
  have h896 : TreeTrue τ start896 := cp_true τ ok895 h895
  exact h896
#print axioms steps27
end Snake9.ReplayFull161
