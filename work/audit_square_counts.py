import json
from pathlib import Path
from itertools import combinations
from collections import Counter

pairs=list(combinations(range(9),2))
def singletons(vertices):
    selected=set(vertices)
    return {v:[(a,b) for a,b in pairs if all(w not in selected for w in
         [v^(1<<a),v^(1<<b),v^(1<<a)^(1<<b)])] for v in vertices}

def audit(vertices):
    counts=Counter()
    selected=set(vertices)
    for a,b in pairs:
        mask=(1<<a)|(1<<b)
        for v in range(512):
            if not v&mask:
                counts[sum(w in selected for w in [v,v^(1<<a),v^(1<<b),v^mask])]+=1
    local=singletons(vertices)
    assert counts[4]==0 and counts[3]==len(vertices)-2
    assert sum(counts.values())==4608
    assert sum(len(a) for a in local.values())==counts[1]
    assert 2*counts[0]+counts[1]+35*len(vertices)+2==9216
    return {'vertices':len(vertices),'square_counts':dict(sorted(counts.items())),
            'local_alpha_histogram':dict(sorted(Counter(map(len,local.values())).items())),
            'minimum_alpha':min(map(len,local.values())),
            'minimum_vertices':[v for v,a in local.items() if len(a)==min(map(len,local.values()))]}

if __name__=='__main__':
    bank=json.loads(Path('work/bank9.json').read_text())
    report=[]
    for i,row in enumerate(bank):
        r=audit(row['vertex_sequence']);r['seed_index']=i;report.append(r)
    Path('outputs/square_bank_audit.json').write_text(json.dumps(report,indent=2))
    print(json.dumps({'bank_minima':dict(Counter(r['minimum_alpha'] for r in report)),
        'first_minimum_seed':min(report,key=lambda r:r['minimum_alpha'])}),flush=True)
    for name in ['square_local_n9_a1_path.json','square_local_n9_a1_path_d2.json']:
        r=json.loads(Path('outputs',name).read_text());print(name,json.dumps(audit(r['path'])),flush=True)
