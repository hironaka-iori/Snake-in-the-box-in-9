import ReplayCheck161_02016
import ReplayCheck161_02020
import ReplayCheck161_02024
import ReplayCheck161_02028
import ReplayCheck161_02032
import ReplayCheck161_02036
import ReplayCheck161_02040
import ReplayCheck161_02044
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayFull161
open Snake9.Lrat144 (TreeTrue)
open Snake9.LratFast144
theorem steps63 (τ : Nat → Bool) (h2016 : TreeTrue τ start2016) : TreeTrue τ start2048 := by
  have h2017 : TreeTrue τ start2017 := replay_true τ ok2016 h2016
  have h2018 : TreeTrue τ start2018 := replay_true τ ok2017 h2017
  have h2019 : TreeTrue τ start2019 := replay_true τ ok2018 h2018
  have h2020 : TreeTrue τ start2020 := replay_true τ ok2019 h2019
  have h2021 : TreeTrue τ start2021 := replay_true τ ok2020 h2020
  have h2022 : TreeTrue τ start2022 := replay_true τ ok2021 h2021
  have h2023 : TreeTrue τ start2023 := replay_true τ ok2022 h2022
  have h2024 : TreeTrue τ start2024 := replay_true τ ok2023 h2023
  have h2025 : TreeTrue τ start2025 := replay_true τ ok2024 h2024
  have h2026 : TreeTrue τ start2026 := replay_true τ ok2025 h2025
  have h2027 : TreeTrue τ start2027 := replay_true τ ok2026 h2026
  have h2028 : TreeTrue τ start2028 := replay_true τ ok2027 h2027
  have h2029 : TreeTrue τ start2029 := replay_true τ ok2028 h2028
  have h2030 : TreeTrue τ start2030 := replay_true τ ok2029 h2029
  have h2031 : TreeTrue τ start2031 := replay_true τ ok2030 h2030
  have h2032 : TreeTrue τ start2032 := replay_true τ ok2031 h2031
  have h2033 : TreeTrue τ start2033 := replay_true τ ok2032 h2032
  have h2034 : TreeTrue τ start2034 := replay_true τ ok2033 h2033
  have h2035 : TreeTrue τ start2035 := replay_true τ ok2034 h2034
  have h2036 : TreeTrue τ start2036 := replay_true τ ok2035 h2035
  have h2037 : TreeTrue τ start2037 := replay_true τ ok2036 h2036
  have h2038 : TreeTrue τ start2038 := replay_true τ ok2037 h2037
  have h2039 : TreeTrue τ start2039 := replay_true τ ok2038 h2038
  have h2040 : TreeTrue τ start2040 := replay_true τ ok2039 h2039
  have h2041 : TreeTrue τ start2041 := replay_true τ ok2040 h2040
  have h2042 : TreeTrue τ start2042 := replay_true τ ok2041 h2041
  have h2043 : TreeTrue τ start2043 := replay_true τ ok2042 h2042
  have h2044 : TreeTrue τ start2044 := replay_true τ ok2043 h2043
  have h2045 : TreeTrue τ start2045 := replay_true τ ok2044 h2044
  have h2046 : TreeTrue τ start2046 := replay_true τ ok2045 h2045
  have h2047 : TreeTrue τ start2047 := replay_true τ ok2046 h2046
  have h2048 : TreeTrue τ start2048 := cp_true τ ok2047 h2047
  exact h2048
#print axioms steps63
end Snake9.ReplayFull161
