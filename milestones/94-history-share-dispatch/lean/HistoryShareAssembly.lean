import ShareCover00
import ShareCover01
import ShareCover02
import ShareCover03
import ShareCover04
import ShareCover05
import ShareCover06
import ShareCover07
import ShareCover08
import ShareCover09
import ShareCover10

/-!
Assembly of the ordered saved history-share rules.
Coverage is obtained from the named finite certificates; no cover table is
recomputed here. Concrete per-word geometric bounds remain explicit premises.
This source awaits compilation.
-/

namespace Snake9.HistoryShare94
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Direction77 Snake9.Guards79 Snake9.GraphInterpretation74
open Snake9.CountFreeAdapter73 Snake9.History84

set_option maxHeartbeats 2000000

/-- The ordered (signature, compatible words) pairs used for later model linking.
Both components and their order are retained without normalization or lookup. -/
def savedShareRules : List (List Nat × List (List Nat)) := [
  (signature000, variants000),
  (signature001, variants001),
  (signature002, variants002),
  (signature003, variants003),
  (signature004, variants004),
  (signature005, variants005),
  (signature006, variants006),
  (signature007, variants007),
  (signature008, variants008),
  (signature009, variants009),
  (signature010, variants010),
  (signature011, variants011),
  (signature012, variants012),
  (signature013, variants013),
  (signature014, variants014),
  (signature015, variants015),
  (signature016, variants016),
  (signature017, variants017),
  (signature018, variants018),
  (signature019, variants019),
  (signature020, variants020),
  (signature021, variants021),
  (signature022, variants022),
  (signature023, variants023),
  (signature024, variants024),
  (signature025, variants025),
  (signature026, variants026),
  (signature027, variants027),
  (signature028, variants028),
  (signature029, variants029),
  (signature030, variants030),
  (signature031, variants031),
  (signature032, variants032),
  (signature033, variants033),
  (signature034, variants034),
  (signature035, variants035),
  (signature036, variants036),
  (signature037, variants037),
  (signature038, variants038),
  (signature039, variants039),
  (signature040, variants040),
  (signature041, variants041),
  (signature042, variants042),
  (signature043, variants043),
  (signature044, variants044),
  (signature045, variants045),
  (signature046, variants046),
  (signature047, variants047),
  (signature048, variants048),
  (signature049, variants049),
  (signature050, variants050),
  (signature051, variants051),
  (signature052, variants052),
  (signature053, variants053),
  (signature054, variants054)
]

theorem saved_share_rules_length : savedShareRules.length = 55 := by
  rfl

/-- Each saved pair has a three-ID signature and its named checked cover.
This proof uses certificate references rather than evaluating the predicate. -/
theorem saved_share_rule_spec (rule : List Nat × List (List Nat))
    (hrule : rule ∈ savedShareRules) :
    rule.1.length = 3 ∧ shareCoverTable rule.1 rule.2 = true := by
  simp only [savedShareRules, List.mem_cons, List.not_mem_nil, or_false] at hrule
  rcases hrule with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨rfl, share_cover_000⟩
  · exact ⟨rfl, share_cover_001⟩
  · exact ⟨rfl, share_cover_002⟩
  · exact ⟨rfl, share_cover_003⟩
  · exact ⟨rfl, share_cover_004⟩
  · exact ⟨rfl, share_cover_005⟩
  · exact ⟨rfl, share_cover_006⟩
  · exact ⟨rfl, share_cover_007⟩
  · exact ⟨rfl, share_cover_008⟩
  · exact ⟨rfl, share_cover_009⟩
  · exact ⟨rfl, share_cover_010⟩
  · exact ⟨rfl, share_cover_011⟩
  · exact ⟨rfl, share_cover_012⟩
  · exact ⟨rfl, share_cover_013⟩
  · exact ⟨rfl, share_cover_014⟩
  · exact ⟨rfl, share_cover_015⟩
  · exact ⟨rfl, share_cover_016⟩
  · exact ⟨rfl, share_cover_017⟩
  · exact ⟨rfl, share_cover_018⟩
  · exact ⟨rfl, share_cover_019⟩
  · exact ⟨rfl, share_cover_020⟩
  · exact ⟨rfl, share_cover_021⟩
  · exact ⟨rfl, share_cover_022⟩
  · exact ⟨rfl, share_cover_023⟩
  · exact ⟨rfl, share_cover_024⟩
  · exact ⟨rfl, share_cover_025⟩
  · exact ⟨rfl, share_cover_026⟩
  · exact ⟨rfl, share_cover_027⟩
  · exact ⟨rfl, share_cover_028⟩
  · exact ⟨rfl, share_cover_029⟩
  · exact ⟨rfl, share_cover_030⟩
  · exact ⟨rfl, share_cover_031⟩
  · exact ⟨rfl, share_cover_032⟩
  · exact ⟨rfl, share_cover_033⟩
  · exact ⟨rfl, share_cover_034⟩
  · exact ⟨rfl, share_cover_035⟩
  · exact ⟨rfl, share_cover_036⟩
  · exact ⟨rfl, share_cover_037⟩
  · exact ⟨rfl, share_cover_038⟩
  · exact ⟨rfl, share_cover_039⟩
  · exact ⟨rfl, share_cover_040⟩
  · exact ⟨rfl, share_cover_041⟩
  · exact ⟨rfl, share_cover_042⟩
  · exact ⟨rfl, share_cover_043⟩
  · exact ⟨rfl, share_cover_044⟩
  · exact ⟨rfl, share_cover_045⟩
  · exact ⟨rfl, share_cover_046⟩
  · exact ⟨rfl, share_cover_047⟩
  · exact ⟨rfl, share_cover_048⟩
  · exact ⟨rfl, share_cover_049⟩
  · exact ⟨rfl, share_cover_050⟩
  · exact ⟨rfl, share_cover_051⟩
  · exact ⟨rfl, share_cover_052⟩
  · exact ⟨rfl, share_cover_053⟩
  · exact ⟨rfl, share_cover_054⟩

/-- Actual emitted-window membership for any exact saved pair. -/
theorem saved_rule_emitted_word_mem {m : Nat} (p : Snake m) (r : Nat)
    (rule : List Nat × List (List Nat)) (hrule : rule ∈ savedShareRules)
    (hr : r+9 ≤ m)
    (hemit : rule.1 <:+ Snake9.History75.prefixes.getD (actualHistory p r) [] ++
      [directionId p r]) :
    2 ≤ r ∧ canon (dsOf p (r-2) 11) ∈ rule.2 := by
  obtain ⟨hlen,hcover⟩ := saved_share_rule_spec rule hrule
  exact emitted_word_mem p r rule.1 rule.2 hr hlen hcover hemit

/-- Actual five-centre credit dispatch. Every word in the exact saved pair
must carry the supplied geometric bound, including all ambiguous variants. -/
theorem saved_rule_five_centre_share {m : Nat} (p : Snake m) (r : Nat)
    (rule : List Nat × List (List Nat)) (L : Nat)
    (hrule : rule ∈ savedShareRules) (hr : r+9 ≤ m)
    (hemit : rule.1 <:+ Snake9.History75.prefixes.getD (actualHistory p r) [] ++
      [directionId p r])
    (hwords : ∀ cs ∈ rule.2, WordShareBound cs L) :
    L ≤ ((List.range 5).map fun i => coreShare 12 p (r+(i+4))).sum := by
  obtain ⟨hlen,hcover⟩ := saved_share_rule_spec rule hrule
  exact emitted_five_centre_share p r rule.1 rule.2 L hr hlen hcover hemit hwords

#print axioms saved_share_rules_length
#print axioms saved_share_rule_spec
#print axioms saved_rule_emitted_word_mem
#print axioms saved_rule_five_centre_share

end Snake9.HistoryShare94

