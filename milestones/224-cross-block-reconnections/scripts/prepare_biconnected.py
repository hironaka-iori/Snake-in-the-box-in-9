"""Reduce unresolved replacement regions to the blocks between their anchors."""
from pathlib import Path
import collections,hashlib,json,sys
H=Path(__file__).resolve().parents[1];R=H.parents[1]
helper=R/'milestones/194-targeted-extensions/scripts/block_bounds.py'
sys.path.insert(0,str(helper.parent));from block_bounds import terminal_blocks
raw=json.loads((H/'data/regions44.json').read_bytes());previous=json.loads((H/'data/pair44.json').read_bytes())
pending={r['id'] for r in previous['results'] if r['status'] in ['UNKNOWN','TIME_LIMIT']}
assert previous['status']=='COMPLETE_COVERAGE'
N=[sum(1<<(v^(1<<k)) for k in range(9)) for v in range(512)]
rows=[]
for row in raw['contexts']:
    if row['id'] not in pending:continue
    for part in row['parts']:
        mask=sum(1<<v for v in part['allowed']);u,v=part['anchors']
        blocks=terminal_blocks(mask,u,v,N);part['block_reduction']=blocks
        reduced=blocks['mask']
        for block in blocks['blocks']:
            if block['adjacent']:
                for w in block['vertices']:
                    if w not in [block['entry'],block['exit']]:reduced &= ~(1<<w)
        part['previous_allowed']=part['allowed']
        part['allowed']=[w for w in range(512) if reduced>>w&1]
        part['rejections']=[]
        if blocks['upper_edges']<44:part['rejections'].append('ANCHOR_BLOCK_BOUND')
        if len(part['allowed'])<45:part['rejections'].append('SIZE_AFTER_BLOCK_REDUCTION')
        even=sum(w.bit_count()%2==0 for w in part['allowed'])
        if even<part['required_even'] or len(part['allowed'])-even<45-part['required_even']:part['rejections'].append('COLOUR_AFTER_BLOCK_REDUCTION')
    row['status']='STATIC_EXCLUDED' if any(p['rejections'] for p in row['parts']) else 'PENDING';rows.append(row)
assert len(rows)==len(pending)
raw['contexts']=rows
raw['refinement_pins']={str(p.relative_to(R)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [helper,H/'data/regions44.json',H/'data/pair44.json',H/'data/pair44-execution.json']}
raw['scope']='Refinement of exactly the92 unresolved44-edge pairs. Keep only vertices in the anchor-to-anchor block chain; adjacent block entry/exit force the direct edge. Block parity bounds and reduced-domain counts are necessary for each replacement. No contact or short-closure premise.'
dest=H/'data/regions44-refined.json';assert not dest.exists();dest.write_text(json.dumps(raw,indent=2)+'\n',encoding='utf-8')
s=(H/'scripts/joint_regions44.py').read_text(encoding='utf-8').replace("H/'data/regions44.json'","H/'data/regions44-refined.json'")
s=s.replace('All maximal contexts covering blockers7/143.','Only unresolved contexts, reduced using the anchor block chain.')
(H/'scripts/joint_regions44_refined.py').write_text(s,encoding='utf-8')
s=(H/'scripts/run_regions44.py').read_text(encoding='utf-8').replace('scripts/joint_regions44.py','scripts/joint_regions44_refined.py').replace("H/'data/regions44.json'","H/'data/regions44-refined.json'")
(H/'scripts/run_regions44_refined.py').write_text(s,encoding='utf-8')
print(json.dumps(dict(contexts=len(rows),statuses=dict(collections.Counter(r['status'] for r in rows)),removed_domain_vertices=sum(len(p['previous_allowed'])-len(p['allowed']) for r in rows for p in r['parts']))),flush=True)
