import HistoryShareAssembly

namespace Snake9.HistoryShare94

theorem saved_signatures_distinct :
    (savedShareRules.map Prod.fst).Nodup := by decide +kernel

theorem saved_variant_count :
    ((savedShareRules.map fun r => r.2.length).sum) = 69 := by decide +kernel

theorem saved_singleton_count :
    (savedShareRules.filter fun r => decide (r.2.length = 1)).length = 41 := by
  decide +kernel

theorem saved_doubleton_count :
    (savedShareRules.filter fun r => decide (r.2.length = 2)).length = 14 := by
  decide +kernel

#print axioms saved_signatures_distinct
#print axioms saved_variant_count
#print axioms saved_singleton_count
#print axioms saved_doubleton_count
end Snake9.HistoryShare94
