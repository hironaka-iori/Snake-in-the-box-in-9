import ConcreteRules95Batch00
import ConcreteRules95Batch01
import ConcreteRules95Batch02
import ConcreteRules95Batch03
import ConcreteRules95Batch04
import ConcreteRules95Batch05
import ConcreteRules95Batch06
import ConcreteRules95Batch07
import ConcreteRules95Batch08
import ConcreteRules95Batch09
import ConcreteRules95Batch10
import HistoryShareAssembly
import DefinedProofGraph

namespace Snake9.ConcreteCatalogue95
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Direction77 Snake9.Guards79 Snake9.GraphWalk78
open Snake9.HistoryShare94 Snake9.CreditTransport95 Snake9.HistoryCredit95

set_option maxHeartbeats 2000000

def concreteRules : List Rule :=
  [rule000, rule001, rule002, rule003, rule004, rule005, rule006, rule007, rule008, rule009, rule010, rule011, rule012, rule013, rule014, rule015, rule016, rule017, rule018, rule019, rule020, rule021, rule022, rule023, rule024, rule025, rule026, rule027, rule028, rule029, rule030, rule031, rule032, rule033, rule034, rule035, rule036, rule037, rule038, rule039, rule040, rule041, rule042, rule043, rule044, rule045, rule046, rule047, rule048, rule049, rule050, rule051, rule052, rule053, rule054]

def concreteModelIndices : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57]

def concreteEdgeNumbers : List Nat :=
  [7, 10, 11, 44, 45, 57, 58, 91, 2000, 2001, 2002, 2003, 2004, 2005, 2006, 2007, 2008, 2009, 2010, 2011, 2012, 2013, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021, 2022, 2023, 2024, 2025, 2026, 2027, 2028, 2029, 2030, 2031, 2032, 2033, 2034, 2035, 2036, 2037, 2038, 2039, 2040, 2041, 2042, 2043, 2044, 2045, 2046]

theorem concrete_rules_length : concreteRules.length = 55 := rfl

theorem concrete_rule_shapes :
    concreteRules.map (fun r => (r.sig, r.words)) = savedShareRules := rfl

theorem concrete_rules_valid : ∀ rule ∈ concreteRules, RuleValid rule := by
  intro rule h
  simp only [concreteRules, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rule_valid_000
  · exact rule_valid_001
  · exact rule_valid_002
  · exact rule_valid_003
  · exact rule_valid_004
  · exact rule_valid_005
  · exact rule_valid_006
  · exact rule_valid_007
  · exact rule_valid_008
  · exact rule_valid_009
  · exact rule_valid_010
  · exact rule_valid_011
  · exact rule_valid_012
  · exact rule_valid_013
  · exact rule_valid_014
  · exact rule_valid_015
  · exact rule_valid_016
  · exact rule_valid_017
  · exact rule_valid_018
  · exact rule_valid_019
  · exact rule_valid_020
  · exact rule_valid_021
  · exact rule_valid_022
  · exact rule_valid_023
  · exact rule_valid_024
  · exact rule_valid_025
  · exact rule_valid_026
  · exact rule_valid_027
  · exact rule_valid_028
  · exact rule_valid_029
  · exact rule_valid_030
  · exact rule_valid_031
  · exact rule_valid_032
  · exact rule_valid_033
  · exact rule_valid_034
  · exact rule_valid_035
  · exact rule_valid_036
  · exact rule_valid_037
  · exact rule_valid_038
  · exact rule_valid_039
  · exact rule_valid_040
  · exact rule_valid_041
  · exact rule_valid_042
  · exact rule_valid_043
  · exact rule_valid_044
  · exact rule_valid_045
  · exact rule_valid_046
  · exact rule_valid_047
  · exact rule_valid_048
  · exact rule_valid_049
  · exact rule_valid_050
  · exact rule_valid_051
  · exact rule_valid_052
  · exact rule_valid_053
  · exact rule_valid_054

theorem concrete_actual_history_credit {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+9 ≤ m) :
    historyCredit concreteRules (actualHistory p r) (directionId p r) (sixCode p r) ≤
      ((List.range 5).map fun i => coreShare 12 p (r+(i+4))).sum :=
  actual_history_credit_le p r concreteRules hr concrete_rules_valid

#print axioms concrete_rules_length
#print axioms concrete_rule_shapes
#print axioms concrete_rules_valid
#print axioms concrete_actual_history_credit

end Snake9.ConcreteCatalogue95
