"""Replay the two single-crossing exclusions using Python and a C++17 compiler.

Run python3 verify_q8_single_crossing_results.py in the experiment directory.
Optionally supply the repository's outputs/snake8_witness.json path.
"""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
from export_q8_search_factors import emit
from verify_q8_free_layer_dual import verify
from contextlib import redirect_stdout

ROOT=Path(__file__).resolve().parent
def records(name):
    with (ROOT/name).open() as stream:
        return [json.loads(line) for line in stream]
def signature(steps):
    labels={}
    return tuple(labels.setdefault(d,len(labels)) for d in steps)
def code(p):
    return signature(a^b for a,b in zip(p,p[1:]))
def checked(p):
    assert len(set(p))==len(p) and min(p)>=0 and max(p)<512
    assert all(((a^b).bit_count()==1)==(i+1==j) for i,a in enumerate(p) for j,b in enumerate(p) if j>i)
def run():
    cases=records("q8_free_layer_duals.jsonl")+records("q8_free_layer_93_95_duals.jsonl")
    ref=next(r['certificate']['arm'] for r in cases if r['lower_edges']==98)
    if len(sys.argv)>1:
        original=json.loads(Path(sys.argv[1]).read_text())['vertex_sequence']
        assert code(original) in (code(ref),code(ref[::-1]))
    expected={code(q) for n in range(93,99) for i in range(len(ref)-n)
              for part in [ref[i:i+n+1]] for q in (part,part[::-1])}
    assert len(expected)==42 and expected=={code(r['certificate']['arm']) for r in cases}
    for r in cases:
        verify(r)
        assert r['target_vertices']==192-r['lower_edges']
        assert r['certificate']['end_parity']==(r['target_vertices']-1)%2
        assert r['vertices_upper']<r['target_vertices']
    print("Verified integer exclusions for all 42 oriented 93-98-edge subpaths.",flush=True)
    anchors=set()
    bank=records("q9_record_single_crossing_191.jsonl")
    for r in bank:
        a=list(map(int,r['steps']))
        p=[0]
        for d in a:p.append(p[-1]^(1<<d))
        checked(p);assert len(p)==192
        axes=[d for d in range(9) if a.count(d)==1]
        assert axes==r['crossing_axes'] and len(axes)==1
        cut=a.index(axes[0])
        anchors.update([signature(a[:cut][::-1]),signature(a[cut+1:])])
    tests=records("q8_record_arm_target192_duals.jsonl")
    assert len(bank)==25 and len(anchors)==10 and anchors=={code(r['certificate']['arm']) for r in tests}
    with tempfile.TemporaryDirectory() as td:
        exe=Path(td)/"solve"
        subprocess.run([os.environ.get("CXX","c++"),"-std=c++17","-O3",str(ROOT/"search_q8_conditioned_dual.cpp"),"-o",str(exe)],check=True)
        for rs,goal in [(records("q8_free_layer_191_controls.jsonl"),191),(tests,192)]:
            model=Path(td)/"models"
            with model.open("w") as stream, redirect_stdout(stream):
                for r in rs:
                    verify(r)
                    assert r['target_vertices']==goal-r['lower_edges']
                    assert r['certificate']['end_parity']==(r['target_vertices']-1)%2
                    emit(r)
            with model.open() as stream:
                out=subprocess.check_output([str(exe),"2000000","walk"],stdin=stream,text=True).splitlines()
            assert len(out)==len(rs)
            for line,r in zip(out,rs):
                i,st,n,*p=line.split()
                assert int(i)==r['index']
                if goal==191:
                    path=list(map(int,p));checked(path);assert st=='FOUND' and len(path)==192
                else:assert st=='EXHAUSTED' and not p
    print("Verified two constructive 191 controls and complete 192 exclusions for all ten rooted arms of the 25 records.")
if __name__=='__main__':run()
