"""Extract the existing count identity into a small separately checked module."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
src=ROOT/'work/spectral/stronger/AggregateWindowUnconditional.lean'
old=src.read_text();body=old[old.index('theorem inPath_iff_sel'):old.index('/-- At an internal vertex')]
text='''import AggregateSingletonBound
import LocalWindowDirBridge
namespace Snake9.CountGeometry78
open SquareIncidence Finset Classical LocalWindow
noncomputable section
set_option maxHeartbeats 1000000
'''+body+'''
theorem core_count_positive {m : Nat} (p : Snake m) (k : Nat) (hk : k < m+1) :
    1 ≤ coreAlpha p k := by
  rw [← localAlpha_eq_coreAlpha p k hk]
  exact localAlpha_positive p _

def truncatedCount {m : Nat} (p : Snake m) (k : Nat) : Nat :=
  min 6 (coreAlpha p k)

theorem truncatedCount_range {m : Nat} (p : Snake m) (k : Nat) (hk : k < m+1) :
    1 ≤ truncatedCount p k ∧ truncatedCount p k ≤ 6 := by
  have h := core_count_positive p k hk
  unfold truncatedCount
  omega

#print axioms inPath_iff_sel
#print axioms flip_val
#print axioms localAlpha_eq_coreAlpha
#print axioms core_count_positive
#print axioms truncatedCount_range
end
end Snake9.CountGeometry78
'''
(HERE/'lean/CountGeometry.lean').write_text(text,encoding='utf-8')
support=ROOT/'work/spectral/.verification/strengthened-n8g3mwjy'
records=[]
for base,module in [(support,'AggregateSingletonBound'),(ROOT/'milestones/75-exact-history-bridge/numeric','CountStateCode')]:
    sp=base/(module+'.lean') if base==support else base/'lean'/(module+'.lean')
    op=base/(module+'.olean') if base==support else base/'build'/(module+'.olean')
    records.append(dict(module=module,source=str(sp),source_sha256=sha(sp),object=str(op),object_sha256=sha(op)))
(HERE/'data/count-support.json').write_text(json.dumps(dict(adapted_from=str(src),adapted_source_sha256=sha(src),
    modules=records,scope='Existing positivity and count-code support pinned; complete inherited dependency closure is not rebuilt.'),indent=2)+'\n')
print('Count identity extracted; positivity and encoding support pinned')
