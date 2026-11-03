"""Pin the next coupled-count test without constructing or running its solver input."""
from pathlib import Path
from collections import Counter
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
cs=read(H/'data/direct-clauses.json')['corner_lists'];pair=cs[1]+cs[3]
assert len(pair)==42
old=R/'milestones/121-replacement-window-pressure';r=read(old/'data/ActualPair121-audit.json')
assert r['exit_code']==0 and not r['timeout'] and sha(old/'lean/ActualPair121.lean')==r['source_sha256']
pins={p.relative_to(R).as_posix():sha(p) for p in [H/'work/reduced.cnf',H/'data/reduced.json',H/'data/direct-clauses.json',old/'lean/ActualPair121.lean',old/'data/ActualPair121-audit.json',old/'build-isolated/ActualPair121.olean',old/r['log']]}
out=dict(status='PROPOSED_NOT_ENCODED_OR_SEARCHED',pattern='0120324',sum_cap=22,known_pair_positions=[2,4],known_pair_sum_lower=8,pair_corner_occurrences=42,pair_distinct_corners=len(set(pair)),multiplicity_histogram=dict(sorted(Counter(Counter(pair).values()).items())),pair_vertices=pair,selected_literal_occurrences=[v+1 for v in pair],selected_sum_upper=34,proposal='Expose the already-proved prefix pair inequality as an at-most34 constraint on42 selected-corner occurrences. Preserve duplicates. The current reduced formula exposes individual lower bounds but no dedicated coupled pair counter.',proof_obligations=['Derive the canonical six-transition prefix of0120324.','Connect its second/fourth singleton counts to42 absent corner occurrences.','Use the checked actual_pair_sum theorem; selected and absent occurrences sum to42.','Give the new counter its ordinary threshold semantics and validate every clause.','A contradiction requires the new semantic proof, complete native replay and actual-snake transfer.','Do not present the added pair counter as RUP-derived from the original106348 inputs unless a separate derivation is supplied.'],source_pins=pins,scope='Next-task specification only. The geometric inequality is proved; its additional counter encoding and any new search are not implemented.')
p=H/'data/next-pair-task.json';assert not p.exists();p.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print('Next pair test:',len(pair),'occurrences,',len(set(pair)),'distinct corners; no input or search created.')
