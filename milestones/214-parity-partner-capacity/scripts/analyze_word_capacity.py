"""Evaluate finite distinct-word capacities in the saved unfinished regions."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];F=H/'data/case-22'
assert not (H/'data/history-search.lock').exists()
raw=(F/'state.json').read_bytes();state=json.loads(raw)
families=json.loads((F/'support-constraints.json').read_bytes())['families']
def members(mask):
    while mask:
        bit=mask&-mask;yield bit.bit_length()-1;mask^=bit
records=[]
for region in state['frontier']:
    domains=region['domains']
    for parity,f in enumerate(families):
        for side in ['clique','outside']:
            ids=f[side];edges=[domains[x] for x in ids];owner={};failed=None
            def augment(row,seen_columns,seen_rows):
                seen_rows.add(row)
                for w in members(edges[row]):
                    if w in seen_columns:continue
                    seen_columns.add(w)
                    if w not in owner or augment(owner[w],seen_columns,seen_rows):
                        owner[w]=row;return True
                return False
            for row in range(len(ids)):
                cols=set();rows=set()
                if not augment(row,cols,rows):
                    union=0
                    for j in rows:union|=edges[j]
                    assert union.bit_count()<len(rows)
                    failed={'variables':[ids[j] for j in sorted(rows)],'union':union,'words':union.bit_count()}
                    break
            removals={};certificates=[]
            if failed is None:
                for start in range(len(ids)):
                    rows={start};pending=[start];union=0;free=False
                    while pending:
                        j=pending.pop();union|=edges[j]
                        for w in members(edges[j]):
                            if w not in owner:free=True
                            elif owner[w] not in rows:rows.add(owner[w]);pending.append(owner[w])
                    if free:continue
                    assert union.bit_count()==len(rows)
                    affected={ids[j]:edges[j]&union for j in range(len(ids)) if j not in rows and edges[j]&union}
                    if affected:
                        certificates.append({'variables':[ids[j] for j in sorted(rows)],'union':union,'affected':affected})
                        for x,mask in affected.items():removals[x]=removals.get(x,0)|mask
            records.append({'region_id':region['id'],'parity':parity,'side':side,'deficient':failed,'distinct_candidate_removals':sum(m.bit_count() for m in removals.values()),'removal_masks':removals,'tight_certificates':certificates})
assert (F/'state.json').read_bytes()==raw
summary={'status':'COMPLETE','state_sha256':hashlib.sha256(raw).hexdigest(),'records':records,'deficient_regions':sorted({r['region_id'] for r in records if r['deficient'] is not None}),'regions_with_candidate_removals':sorted({r['region_id'] for r in records if r['distinct_candidate_removals']}),'distinct_candidates_across_regions':sum(r['distinct_candidate_removals'] for r in records),'scope':'Exact finite domain-union cardinalities for the saved snapshot; no state mutation, no propagation fixed point, no new search exclusion. Duplicates across certificates are removed within each region/family. These removals may also follow from existing binary propagation.'}
(H/'data/word-capacity-analysis.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k!='records'},indent=2))
