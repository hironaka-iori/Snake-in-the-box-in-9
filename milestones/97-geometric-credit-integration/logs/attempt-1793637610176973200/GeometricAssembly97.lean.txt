import GeometricTransport97
import GeometricLookup97Batch00
import GeometricLookup97Batch01
import GeometricLookup97Batch02
import GeometricLookup97Batch03
import GeometricLookup97Batch04
import GeometricLookup97Batch05
import GeometricLookup97Batch06
import GeometricLookup97Batch07
import GeometricLookup97Batch08
import GeometricLookup97Batch09
import GeometricLookup97Batch10
import GeometricLookup97Batch11
import GeometricLookup97Batch12
import GeometricLookup97Batch13
import GeometricLookup97Batch14
import GeometricLookup97Batch15
import GeometricLookup97Batch16
import GeometricLookup97Batch17
import GeometricLookup97Batch18
import GeometricLookup97Batch19
import GeometricLookup97Batch20
import GeometricLookup97Batch21
import GeometricLookup97Batch22
import GeometricLookup97Batch23
import GeometricLookup97Batch24
import GeometricLookup97Batch25

namespace Snake9.GeometricCredit97
open Snake9.LocalWindow Snake9.CreditTransport95 Snake9.Direction77
open Snake9.GraphWalk78 Snake9.HistoryCredit95 Snake9.ConcreteCatalogue95
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem geometric_catalogue_valid (i : Nat) (hi : i < 505) :
    LocalNineShare (extensions.getD i []) (geometricCredits.getD i 0) := by
  by_cases h0 : i < 20
  · exact valid_00 i (by omega) h0
  by_cases h1 : i < 40
  · exact valid_01 i (by omega) h1
  by_cases h2 : i < 60
  · exact valid_02 i (by omega) h2
  by_cases h3 : i < 80
  · exact valid_03 i (by omega) h3
  by_cases h4 : i < 100
  · exact valid_04 i (by omega) h4
  by_cases h5 : i < 120
  · exact valid_05 i (by omega) h5
  by_cases h6 : i < 140
  · exact valid_06 i (by omega) h6
  by_cases h7 : i < 160
  · exact valid_07 i (by omega) h7
  by_cases h8 : i < 180
  · exact valid_08 i (by omega) h8
  by_cases h9 : i < 200
  · exact valid_09 i (by omega) h9
  by_cases h10 : i < 220
  · exact valid_10 i (by omega) h10
  by_cases h11 : i < 240
  · exact valid_11 i (by omega) h11
  by_cases h12 : i < 260
  · exact valid_12 i (by omega) h12
  by_cases h13 : i < 280
  · exact valid_13 i (by omega) h13
  by_cases h14 : i < 300
  · exact valid_14 i (by omega) h14
  by_cases h15 : i < 320
  · exact valid_15 i (by omega) h15
  by_cases h16 : i < 340
  · exact valid_16 i (by omega) h16
  by_cases h17 : i < 360
  · exact valid_17 i (by omega) h17
  by_cases h18 : i < 380
  · exact valid_18 i (by omega) h18
  by_cases h19 : i < 400
  · exact valid_19 i (by omega) h19
  by_cases h20 : i < 420
  · exact valid_20 i (by omega) h20
  by_cases h21 : i < 440
  · exact valid_21 i (by omega) h21
  by_cases h22 : i < 460
  · exact valid_22 i (by omega) h22
  by_cases h23 : i < 480
  · exact valid_23 i (by omega) h23
  by_cases h24 : i < 500
  · exact valid_24 i (by omega) h24
  exact valid_25 i (by omega) hi

theorem actual_geometric_credit {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+9 ≤ m) :
    geometricCredits.getD (directionId p r) 0 ≤
      ((List.range 5).map fun i => coreShare 12 p (r+(i+4))).sum :=
  actual_geometric_credit_from_catalogue geometric_catalogue_valid p r hr

theorem actual_geometric_history_credit {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+9 ≤ m) :
    max (geometricCredits.getD (directionId p r) 0)
      (historyCredit concreteRules (actualHistory p r) (directionId p r) (sixCode p r)) ≤
      ((List.range 5).map fun i => coreShare 12 p (r+(i+4))).sum :=
  actual_geometric_history_credit_from_catalogue geometric_catalogue_valid p r hr

theorem actual_geometric_history_weight {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+9 ≤ m) :
    120 * (sixCode p r % 6 + 1) +
      max (geometricCredits.getD (directionId p r) 0)
        (historyCredit concreteRules (actualHistory p r) (directionId p r) (sixCode p r)) ≤
      120 * coreAlpha p (r+8) +
        ((List.range 5).map fun i => coreShare 12 p (r+(i+4))).sum :=
  actual_geometric_history_weight_from_catalogue geometric_catalogue_valid p r hr

#print axioms geometric_catalogue_valid
#print axioms actual_geometric_credit
#print axioms actual_geometric_history_credit
#print axioms actual_geometric_history_weight
end Snake9.GeometricCredit97
