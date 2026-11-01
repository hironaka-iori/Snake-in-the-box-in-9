"""Pin contributor share sources and extract a minimal dependency bridge."""
from pathlib import Path
import hashlib,json,subprocess
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[2]
for d in ['lean','upstream','data','logs','build']:(HERE/d).mkdir(parents=True,exist_ok=True)
sha=lambda b:hashlib.sha256(b).hexdigest()
def git(*args):return subprocess.check_output(['git','-C',str(ROOT),'-c','core.commitGraph=false',*args])
commit='cd0c90fddf12170d735ee34fcc501e99c60632a6'
paths=['work/spectral/stronger/ShareBridge.lean','work/spectral/ShareCharge.lean','work/spectral/stronger/AggregateWindowUnconditional.lean']
sources={};records=[]
for path in paths:
    raw=git('show',f'{commit}:{path}');name=Path(path).name
    (HERE/'upstream'/name).write_bytes(raw);sources[name]=raw.decode()
    records.append(dict(commit=commit,path=path,sha256=sha(raw)))
old=(ROOT/'milestones/27-empty-square-packing/upstream/ShareCharge.lean').read_bytes()
meta=dict(contributor_commit=commit,checkpoint=git('rev-parse','HEAD').decode().strip(),sources=records,
    share_charge_matches_milestone27_after_lf=old.replace(b'\r\n',b'\n')==sources['ShareCharge.lean'].encode(),
    scope='Pinned existing contributor proofs; bridge compilation must be checked separately.')
(HERE/'data/provenance.json').write_text(json.dumps(meta,indent=2)+'\n')
aggregate=sources['AggregateWindowUnconditional.lean'];bridge=sources['ShareBridge.lean']
identity=aggregate[aggregate.index('theorem inPath_iff_sel'):aggregate.index('/-- `localAlpha`')]
body=bridge[bridge.index('/-! ## Sums'):bridge.index('/-! ## Path-indexed form')]
out='''import ShareCharge
import LocalWindowShareBridge

/-!
The coordinate and square-count identifications below are extracted from the
contributor's ShareBridge.lean and AggregateWindowUnconditional.lean. Exact source
commit and hashes are in ../data/provenance.json. The independent namespace avoids
collisions with the contributor's full aggregate module.
-/
namespace Snake9.CountFreeBridge
open SquareIncidence Finset Classical LocalWindow
noncomputable section
set_option maxHeartbeats 1600000
'''+identity+body+'''
theorem core_share_path_sum {m : Nat} (M : Nat) (p : Snake m) :
    (∑ x, selected p x * shareN M p x) =
      ((List.range (m+1)).map fun k => coreShare M p k).sum := by
  rw [sum_selected_mul]
  calc
    (∑ i : Fin (m+1), shareN M p (p.vertex i)) =
        ∑ i : Fin (m+1), coreShare M p i.val := by
      apply Finset.sum_congr rfl
      intro i _
      exact shareN_eq_coreShare M p i.val i.isLt
    _ = _ := sum_fin_eq_list_sum (coreShare M p) (m+1)

/-- The global empty-square budget in exactly the core representation used by
the local share certificates. The anchored count counts each empty square four times. -/
theorem core_share_total_le {m : Nat} (M : Nat) (p : Snake m) :
    ((List.range (m+1)).map fun k => coreShare M p k).sum ≤
      M * totalEmptyAnchored p := by
  rw [← core_share_path_sum]
  exact share_total_le M p

theorem core_share_charge_le {m : Nat} (M : Nat) (p : Snake m) (hm : 1 ≤ m) :
    2*M*totalSingleton p + ((List.range (m+1)).map fun k => coreShare M p k).sum
      + 70*M*(m+1) ≤ 18428*M := by
  have hs := core_share_total_le M p
  have hi := Nat.mul_le_mul_left M (incidence_bound_with_empty p hm)
  calc
    _ ≤ 2*M*totalSingleton p + M*totalEmptyAnchored p + 70*M*(m+1) :=
      Nat.add_le_add_right (Nat.add_le_add_left hs _) _
    _ = M*(totalEmptyAnchored p + 2*totalSingleton p + 70*(m+1)) := by ring
    _ ≤ 18428*M := by simpa [Nat.mul_comm] using hi

theorem core_share12_charge_le {m : Nat} (p : Snake m) (hm : 1 ≤ m) :
    24*totalSingleton p + ((List.range (m+1)).map fun k => coreShare 12 p k).sum
      + 840*(m+1) ≤ 221136 := by
  simpa using core_share_charge_le 12 p hm

#print axioms emptyAt_eq_emptyCount
#print axioms selDeg_eq_cnt
#print axioms shareN_eq_coreShare
#print axioms core_share_path_sum
#print axioms core_share_total_le
#print axioms core_share_charge_le
#print axioms core_share12_charge_le
end
end Snake9.CountFreeBridge
'''
(HERE/'lean/CoreShareBudget.lean').write_text(out,encoding='utf-8',newline='\n')
print(meta,flush=True)
