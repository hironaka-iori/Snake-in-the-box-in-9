"""Reuse native task exclusions under path reversal, exchange and containment."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];P=H.parents[1]/'milestones/229-two-layer-construction'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_bytes())
current=H/'data/lower-pairs.json';prior=P/'data/boundary-lower-pairs.json';cp=P/'data/coverage46.json'
j=read(current);old=read(prior);cover=read(cp)
assert cover['status']=='COMPLETE_NATIVE_EXCLUSION' and cover['width']==46
assert all(sha(p)==h for p,h in cover['pins'].items())
assert all(sha(p)==h for p,h in j['pins'].items())
def parts(c):
    return [(tuple(sorted(c['first_anchors'])),c['first_edges'],set(c['first_domain'])),(tuple(sorted(c['lower_anchors'])),c['lower_edges'],set(c['lower_domain']))]
prior_rows=[(i,parts(old['configurations'][i])) for i in old['representatives']]
assert {str(i) for i,_ in prior_rows}==set(cover['representative_results'])
transfers={};pending=[]
for i in j['representatives']:
    c=parts(j['configurations'][i]);hit=None
    for k,d in prior_rows:
        for swap in [False,True]:
            target=list(reversed(d)) if swap else d
            if all(x[:2]==y[:2] and x[2]<=y[2] for x,y in zip(c,target)):
                hit=dict(prior_representative=k,exchange_paths=swap,current_sorted_endpoints=[list(x[0]) for x in c],prior_sorted_endpoints=[list(x[0]) for x in target]);break
        if hit is not None:break
    if hit is None:pending.append(i)
    else:transfers[str(i)]=hit
out=dict(status='COMPLETE_TASK_TRANSFER_SCAN',pins={str(p):sha(p) for p in [current,prior,cp,Path(__file__)]},transfers=transfers,pending=pending,scope='Each inherited exclusion preserves both path lengths and unordered endpoint pairs, possibly exchanging paths, with current domains contained in the corresponding previously excluded domains. Path reversal and exchange preserve existence of two separated undirected induced paths. No interval-width exclusion transfers upward. Native data comparisons and prior solver scope remain explicit.')
(H/'data/task-transfer.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print('TRANSFERRED',len(transfers),'PENDING',len(pending))
