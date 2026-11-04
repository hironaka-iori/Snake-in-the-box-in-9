import ReplayCheck161_00928
import ReplayCheck161_00932
import ReplayCheck161_00936
import ReplayCheck161_00940
import ReplayCheck161_00944
import ReplayCheck161_00948
import ReplayCheck161_00952
import ReplayCheck161_00956
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps29 (τ : Nat → Bool) (h928 : TreeTrue τ start928) : TreeTrue τ start960 := by
  have h929 : TreeTrue τ start929 := replay_true τ ok928 h928
  have h930 : TreeTrue τ start930 := replay_true τ ok929 h929
  have h931 : TreeTrue τ start931 := replay_true τ ok930 h930
  have h932 : TreeTrue τ start932 := replay_true τ ok931 h931
  have h933 : TreeTrue τ start933 := replay_true τ ok932 h932
  have h934 : TreeTrue τ start934 := replay_true τ ok933 h933
  have h935 : TreeTrue τ start935 := replay_true τ ok934 h934
  have h936 : TreeTrue τ start936 := replay_true τ ok935 h935
  have h937 : TreeTrue τ start937 := replay_true τ ok936 h936
  have h938 : TreeTrue τ start938 := replay_true τ ok937 h937
  have h939 : TreeTrue τ start939 := replay_true τ ok938 h938
  have h940 : TreeTrue τ start940 := replay_true τ ok939 h939
  have h941 : TreeTrue τ start941 := replay_true τ ok940 h940
  have h942 : TreeTrue τ start942 := replay_true τ ok941 h941
  have h943 : TreeTrue τ start943 := replay_true τ ok942 h942
  have h944 : TreeTrue τ start944 := replay_true τ ok943 h943
  have h945 : TreeTrue τ start945 := replay_true τ ok944 h944
  have h946 : TreeTrue τ start946 := replay_true τ ok945 h945
  have h947 : TreeTrue τ start947 := replay_true τ ok946 h946
  have h948 : TreeTrue τ start948 := replay_true τ ok947 h947
  have h949 : TreeTrue τ start949 := replay_true τ ok948 h948
  have h950 : TreeTrue τ start950 := replay_true τ ok949 h949
  have h951 : TreeTrue τ start951 := replay_true τ ok950 h950
  have h952 : TreeTrue τ start952 := replay_true τ ok951 h951
  have h953 : TreeTrue τ start953 := replay_true τ ok952 h952
  have h954 : TreeTrue τ start954 := replay_true τ ok953 h953
  have h955 : TreeTrue τ start955 := replay_true τ ok954 h954
  have h956 : TreeTrue τ start956 := replay_true τ ok955 h955
  have h957 : TreeTrue τ start957 := replay_true τ ok956 h956
  have h958 : TreeTrue τ start958 := replay_true τ ok957 h957
  have h959 : TreeTrue τ start959 := replay_true τ ok958 h958
  have h960 : TreeTrue τ start960 := cp_true τ ok959 h959
  exact h960
#print axioms steps29
end Snake9.ReplayFull161
