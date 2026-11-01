"""Assemble semantic batches using the generated count, preserving association."""
from pathlib import Path
import json
HERE=Path(__file__).resolve().parents[1];OUT=HERE/'share-proof'
n=json.loads((OUT/'data/share12.json').read_text())['shards']
s='import Share12.Compose\nimport Share12.Structure\n'
s+=''.join(f'import Share12.Shard{i:02d}\n' for i in range(n))
s+='set_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace Snake9.LocalWindow.ShareWindow12\nopen Snake9.LocalWindow.Tags\n'
s+='theorem all_clauses : ckAllS meaning smeaning resolution ctrs tots window cap tags raw = true := by\n  have h0 := shard0\n'
for i in range(1,n):s+=f'  have h{i} := ckAllS_append_true12 meaning smeaning resolution ctrs tots window cap _ tags{i} _ raw{i} h{i-1} shard{i}\n'
s+=f'  have h{n} := ckAllS_append_true12 meaning smeaning resolution ctrs tots window cap _ [] _ [] h{n-1} rfl\n  exact h{n}\n'
s+='''theorem check : checkAllS meaning smeaning resolution ctrs tots window bounds cap tags raw = true := by
  simp only [checkAllS, counts_ok, totals_ok, all_clauses, Bool.and_self]
theorem sat : ∀ S E : Nat → Bool, AxiomsS S E window (centresOf window bounds) resolution cap → ∃ τ, cnfTrue τ cnf = true :=
  fun S E h => ⟨_, soundS meaning smeaning resolution ctrs tots window bounds cap tags raw check S E h⟩
#print axioms sat
end Snake9.LocalWindow.ShareWindow12
'''
(OUT/'lean/Share12/Sat.lean').write_text(s,encoding='utf-8',newline='\n')
print('Assembled',n,'semantic batches.')
