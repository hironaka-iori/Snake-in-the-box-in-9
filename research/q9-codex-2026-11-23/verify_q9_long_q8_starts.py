"""Verify a Q9 start bound with any number of crossings, from a 96-edge witness subpath."""
import argparse, json, io, subprocess
from pathlib import Path
from contextlib import redirect_stdout
from q9_long_q8_starts import roots,code
from verify_q8_free_layer_dual import verify
from export_q8_search_factors import emit

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('reference',type=Path)
    ap.add_argument('solver')
    args=ap.parse_args()
    ref=json.loads(args.reference.read_text())['vertex_sequence']
    assert len(set(ref))==len(ref)==99 and all(0<=v<256 for v in ref)
    assert all(((x^ref[j]).bit_count()==1)==(j==i+1) for i,x in enumerate(ref) for j in range(i+1,len(ref)))
    expected={code(a) for a in roots(ref)}
    rows=list(map(json.loads,open('q9_long_q8_starts_duals.jsonl')))
    assert len(rows)==len(expected) and {code(r['certificate']['arm']) for r in rows}==expected
    previous={}
    for old in map(json.loads,open('q8_free_layer_duals.jsonl')):
        k=code(old['certificate']['arm'])
        if k in expected:
            verify(old)
            upper=old['vertices_upper']
            upper-= (upper-old['target_vertices'])%2
            previous[k]=old['lower_edges']+upper+2
    out=[]
    for r in rows:
        verify(r)
        c=r['certificate'];arm=c['arm'];n=len(arm)-1
        h={v for v in range(256) if v not in arm and all((v^u).bit_count()!=1 for u in arm)}
        assert all((v^u).bit_count()!=1 for v in h for u in h if u!=v)
        minimum=191-n
        assert r['target_vertices']==minimum
        # A path with at least 192 edges has at least this many second-layer
        # vertices. Returning to the original layer contributes at most one last vertex.
        direct=r['vertices_upper']
        if direct<minimum:
            status='DUAL'
        else:
            buf=io.StringIO()
            with redirect_stdout(buf):emit(r)
            text=subprocess.check_output([args.solver,'1200000','walk'],input=buf.getvalue(),text=True)
            _,status,*_=text.split()
        valid_upper=n+direct-((direct-minimum)%2)+2
        if status=='EXHAUSTED':valid_upper=min(valid_upper,191)
        valid_upper=min(valid_upper,previous.get(code(arm),valid_upper))
        out.append({'unrestricted_extension_upper_edges':valid_upper,'index':r['index'],'first_edges':n,'min_vertices':minimum,
                    'parity_upper':direct,'isolated_holes':len(h),'status':status})
    print(json.dumps(out,indent=2))
if __name__=='__main__':main()
