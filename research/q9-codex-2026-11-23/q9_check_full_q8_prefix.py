"""Bound arbitrary extensions of this full Q8 witness inside Q9."""
import argparse, io, json, subprocess
from contextlib import redirect_stdout
from pathlib import Path
from export_q8_search_factors import emit
from verify_q8_free_layer_dual import verify

def validate(p):
    assert len(set(p))==len(p) and all(0<=v<512 for v in p)
    assert all(((x^p[j]).bit_count()==1)==(j==i+1) for i,x in enumerate(p) for j in range(i+1,len(p)))

if __name__=="__main__":
    ap=argparse.ArgumentParser()
    ap.add_argument("reference",type=Path)
    ap.add_argument("solver")
    ap.add_argument("--nodes",type=int,default=120000)
    args=ap.parse_args()
    reference=json.loads(args.reference.read_text())["vertex_sequence"]
    validate(reference)
    assert len(reference)==99
    for r in map(json.loads,open("q8_free_layer_full98_duals.jsonl")):
        verify(r)
        arm=r["certificate"]["arm"];first=arm[::-1];tip=first[-1]
        assert arm in (reference,reference[::-1])
        holes={v for v in range(256) if v not in first and all((v^x).bit_count()!=1 for x in first)}
        assert all((x^y).bit_count()>1 for x in holes for y in holes if x!=y)
        assert not any(v not in first and all((v^x).bit_count()!=1 for x in first[:-1]) for v in (tip^(1<<d) for d in range(8)))
        assert r["certificate"]["end_parity"]==1
        buf=io.StringIO()
        with redirect_stdout(buf):emit(r)
        header,body=buf.getvalue().split('\n',1)
        even=(r["vertices_upper"]//2)*2
        upper=98+(even+1)+1
        tests=[];witness=None
        for n in range(even,even-9,-2):
            head=header.split();head[1]=str(n)
            data=' '.join(head)+'\n'+body
            result=subprocess.run([args.solver,str(args.nodes),"walk"],input=data,text=True,capture_output=True,check=True)
            idx,st,nodes,*path=result.stdout.split()
            tests.append([n,st,int(nodes)])
            if st=="EXHAUSTED":upper=min(upper,98+(n-1)+1)
            if st=="FOUND":
                witness=list(map(int,path));validate(witness)
                assert witness[:99]==first and len(witness)-1==98+n
                break
            if st=="UNKNOWN":break
        print(json.dumps(dict(start=first[0],crossing=tip,holes=sorted(holes),dual_even_upper=even,tests=tests,upper_edges=upper,witness=witness)),flush=True)
