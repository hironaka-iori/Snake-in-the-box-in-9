"""Extract the longest one-crossing subpath from the supplied bank, then normalize it."""
import json
from pathlib import Path
from check_snake import verify


def extract():
    bank=json.loads(Path('work/bank9.json').read_text())
    best=None
    for seed,row in enumerate(bank):
        p=row['vertex_sequence']
        for bit in range(9):
            cuts=[i for i,(u,v) in enumerate(zip(p,p[1:])) if u^v==1<<bit]
            for t,i in enumerate(cuts):
                start=cuts[t-1]+1 if t else 0
                end=cuts[t+1] if t+1<len(cuts) else len(p)-1
                if i==start or i+1==end: continue
                if best is None or end-start>best['joined_edges']:
                    project=lambda v: (v&((1<<bit)-1))|((v>>(bit+1))<<bit)
                    a=[project(v)^project(p[i]) for v in reversed(p[start:i+1])]
                    b=[project(v)^project(p[i+1]) for v in p[i+1:end+1]]
                    ca,cb=a[1].bit_length()-1,b[1].bit_length()-1
                    assert ca!=cb
                    axes=[ca,cb]+[k for k in range(8) if k not in [ca,cb]]
                    permute=lambda v: sum(((v>>old)&1)<<new for new,old in enumerate(axes))
                    a,b=list(map(permute,a)),list(map(permute,b))
                    assert set(a)&set(b)=={0} and a[1]==1 and b[1]==2
                    joined=list(reversed(a))+[v+256 for v in b]
                    witness=verify([(u^v).bit_length()-1 for u,v in zip(joined,joined[1:])])
                    best={'bank_seed_index':seed,'deleted_coordinate':bit,'start_index':start,
                          'bridge_index':i,'end_index':end,'left_edges':len(a)-1,'right_edges':len(b)-1,
                          'left_path':a,'right_path':b,'joined_edges':end-start,'joined_witness':witness}
    return best

if __name__=='__main__':
    result=extract()
    Path('outputs/joint_layer_seed.json').write_text(json.dumps(result,indent=2),encoding='utf-8')
    print({k:v for k,v in result.items() if k not in ['left_path','right_path','joined_witness']})
