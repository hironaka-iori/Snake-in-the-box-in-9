"""Check unrestricted extensions of all oriented contiguous 95-edge starts of one Q8 snake."""
import json,sys
from pathlib import Path
from q9_long_q8_starts import roots,code
from verify_q8_free_layer_dual import verify

def main():
    ref=json.loads(Path(sys.argv[1]).read_text())['vertex_sequence']
    assert len(ref)==len(set(ref))==99 and all(0<=v<256 for v in ref)
    assert all(((v^ref[j]).bit_count()==1)==(j==i+1) for i,v in enumerate(ref) for j in range(i+1,len(ref)))
    bounds={}
    for arm in roots(ref,95):
        holes={v for v in range(256) if v not in arm and all((v^x).bit_count()!=1 for x in arm)}
        degree=max((sum((v^(1<<d)) in holes for d in range(8)) for v in holes),default=0)
        assert degree<=1
        # A returning bottom segment cannot leave again: one site would repeat a top
        # vertex, two neighboring sites put a chord between their top counterparts.
        bounds[code(arm)]={'first_edges':len(arm)-1,'crossing':arm[0],'bottom_terminal_limit':1+degree if holes else 0,'upper':None}
    for f in ['q8_free_layer_duals.jsonl','q8_free_layer_93_95_duals.jsonl','q9_long_q8_starts_duals.jsonl','q9_95_extra_dual.jsonl']:
        for r in map(json.loads,open(f)):
            key=code(r['certificate']['arm'])
            if key not in bounds:continue
            verify(r)
            b=bounds[key];parity=(1+r['certificate']['end_parity'])%2
            maximum=r['vertices_upper']-((r['vertices_upper']-parity)%2)
            upper=b['first_edges']+maximum+1+b['bottom_terminal_limit']
            if b['upper'] is None or upper<b['upper']:
                b['upper']=upper;b['certificate']=[f,r['index']]
    assert all(v['upper'] is not None for v in bounds.values())
    report={}
    for i in range(len(ref)-95):
        a=ref[i:i+96]
        for p in (a,a[::-1]):
            todo=[p];family=[]
            while todo:
                s=todo.pop();family.append(bounds[code(s[::-1])])
                for v in (s[-1]^(1<<j) for j in range(8)):
                    if v not in s and all((v^u).bit_count()!=1 for u in s[:-1]):
                        todo.append(s+[v])
            report[f'{p[0]}->{p[-1]}']={'upper':max(b['upper'] for b in family),'first_crossing_cases':family}
    print(json.dumps(report,indent=2))
if __name__=='__main__':main()
