import ReplayCheck161_00896
import ReplayCheck161_00900
import ReplayCheck161_00904
import ReplayCheck161_00908
import ReplayCheck161_00912
import ReplayCheck161_00916
import ReplayCheck161_00920
import ReplayCheck161_00924
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps28 (τ : Nat → Bool) (h896 : TreeTrue τ start896) : TreeTrue τ start928 := by
  have h897 : TreeTrue τ start897 := replay_true τ ok896 h896
  have h898 : TreeTrue τ start898 := replay_true τ ok897 h897
  have h899 : TreeTrue τ start899 := replay_true τ ok898 h898
  have h900 : TreeTrue τ start900 := replay_true τ ok899 h899
  have h901 : TreeTrue τ start901 := replay_true τ ok900 h900
  have h902 : TreeTrue τ start902 := replay_true τ ok901 h901
  have h903 : TreeTrue τ start903 := replay_true τ ok902 h902
  have h904 : TreeTrue τ start904 := replay_true τ ok903 h903
  have h905 : TreeTrue τ start905 := replay_true τ ok904 h904
  have h906 : TreeTrue τ start906 := replay_true τ ok905 h905
  have h907 : TreeTrue τ start907 := replay_true τ ok906 h906
  have h908 : TreeTrue τ start908 := replay_true τ ok907 h907
  have h909 : TreeTrue τ start909 := replay_true τ ok908 h908
  have h910 : TreeTrue τ start910 := replay_true τ ok909 h909
  have h911 : TreeTrue τ start911 := replay_true τ ok910 h910
  have h912 : TreeTrue τ start912 := replay_true τ ok911 h911
  have h913 : TreeTrue τ start913 := replay_true τ ok912 h912
  have h914 : TreeTrue τ start914 := replay_true τ ok913 h913
  have h915 : TreeTrue τ start915 := replay_true τ ok914 h914
  have h916 : TreeTrue τ start916 := replay_true τ ok915 h915
  have h917 : TreeTrue τ start917 := replay_true τ ok916 h916
  have h918 : TreeTrue τ start918 := replay_true τ ok917 h917
  have h919 : TreeTrue τ start919 := replay_true τ ok918 h918
  have h920 : TreeTrue τ start920 := replay_true τ ok919 h919
  have h921 : TreeTrue τ start921 := replay_true τ ok920 h920
  have h922 : TreeTrue τ start922 := replay_true τ ok921 h921
  have h923 : TreeTrue τ start923 := replay_true τ ok922 h922
  have h924 : TreeTrue τ start924 := replay_true τ ok923 h923
  have h925 : TreeTrue τ start925 := replay_true τ ok924 h924
  have h926 : TreeTrue τ start926 := replay_true τ ok925 h925
  have h927 : TreeTrue τ start927 := replay_true τ ok926 h926
  have h928 : TreeTrue τ start928 := cp_true τ ok927 h927
  exact h928
#print axioms steps28
end Snake9.ReplayFull161
