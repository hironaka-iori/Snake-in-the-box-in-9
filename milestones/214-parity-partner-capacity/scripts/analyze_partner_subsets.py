"""Evaluate necessary partner-capacity inequalities on a frozen search frontier."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1]
folder=H/'data/case-22'
assert not (H/'data/history-search.lock').exists()
raw=(folder/'state.json').read_bytes();state=json.loads(raw)
families=json.loads((folder/'support-constraints.json').read_bytes())['families']
records=[]
for region in state['frontier']:
    domains=region['domains']
    for parity,f in enumerate(families):
        outside=f['outside'];clique=f['clique'];position={y:k for k,y in enumerate(clique)}
        neighbours=[sum(1<<position[y] for y in f['partners'][str(x)] if domains[x]&domains[y]) for x in outside]
        unions=[0]*(1<<len(outside));largest_deficiency=0;witness=0
        for mask in range(1,len(unions)):
            bit=mask&-mask;unions[mask]=unions[mask^bit]|neighbours[bit.bit_length()-1]
            deficiency=mask.bit_count()-unions[mask].bit_count()
            if deficiency>largest_deficiency:largest_deficiency=deficiency;witness=mask
        spare=32-len(clique)
        records.append({'region_id':region['id'],'parity':parity,'outside_count':len(outside),'spare':spare,'zero_support_variables':sum(n==0 for n in neighbours),'largest_partner_deficiency':largest_deficiency,'witness_outside':[x for k,x in enumerate(outside) if witness>>k&1],'violates_necessary_inequality':largest_deficiency>spare,'subsets_enumerated':len(unions)-1})
assert (folder/'state.json').read_bytes()==raw
result={'status':'COMPLETE','state_sha256':hashlib.sha256(raw).hexdigest(),'records':records,'violating_regions':sorted({r['region_id'] for r in records if r['violates_necessary_inequality']}),'scope':'Exhaustive subsets of the current outside families. A necessary consequence of injective sharing into candidate partners and spare-word capacity. This analysis does not modify or exclude saved search regions and does not claim a complete native certificate.'}
(H/'data/partner-subset-analysis.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'regions':len(state['frontier']),'violating_regions':result['violating_regions'],'largest_deficiencies':{str(p):max((r['largest_partner_deficiency'] for r in records if r['parity']==p),default=0) for p in [0,1]}},indent=2))
