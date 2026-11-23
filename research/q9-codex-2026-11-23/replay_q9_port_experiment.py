"""Replay saved integer upper bounds; optional DRAT replay for the SAT branches."""
import gzip,json,sys,tempfile,subprocess
from pathlib import Path
from q9_port_edge_degree import replay
from q9_port_fiveface import build5,check_q5
from q9_overlapping_port_bound import ROOT,controls,replay as replay_overlap, NEIGH
from bound_q9_positive_ports import sizes,tables
from verify_q9_222_disconnected import components

def read(name):
    return list(map(json.loads,gzip.open(ROOT/name,"rt")))

def catalogue_audit():
    masks=[]
    small_adj=[sum(1<<(v^(1<<d)) for d in range(4)) for v in range(16)]
    for s in range(1<<16):
        vs=[v for v in range(16) if s>>v&1]
        if any((small_adj[v]&s).bit_count()>2 for v in vs):continue
        # Repeatedly peel degree-zero and degree-one vertices; a cycle survives.
        rem=s
        while rem:
            tips=sum(1<<v for v in vs if rem>>v&1 and (small_adj[v]&rem).bit_count()<2)
            if not tips:break
            rem ^= tips
        if not rem:masks.append(s)
    masks.sort(key=lambda s:-s.bit_count())
    assert [s.bit_count() for s in masks]==sizes
    for v in range(16):
        for d in range(3):
            col=sum(1<<i for i,s in enumerate(masks) if s>>v&1 and (s&small_adj[v]).bit_count()>=d)
            assert col==tables[d][v]
    print("local Q4 catalogue",len(masks),"max",max(sizes),"Q5 longest normalized path count",check_q5(),flush=True)

def numeric():
    catalogue_audit()
    expected=list(controls())
    for filename,func in [
        ("q9_overlapping_ports_131.jsonl.gz",replay_overlap),
        ("q9_port_edge_degree_131.jsonl.gz",replay),
        ("q9_adversarial_port_forests.jsonl.gz",replay),
        ("q9_port_fiveface_trials.jsonl.gz",lambda e,w,d:replay(e,w,d,build5))]:
        rows=read(filename)
        if "_131" in filename:
            assert [r["row"] for r in rows]==list(range(131))
        for r in rows:
            if "row" in r:assert [tuple(e) for e in r["edges"]]==expected[r["row"]]
            if "weights" in r:
                assert func(r["edges"],r["weights"],r["den"])==r["upper"]
        print(filename,len(rows),"replayed",flush=True)

def drat(checker):
    from q9_port_adversarial_sat import formula
    for filename in ("q9_port_adversarial_drat.jsonl.gz","q9_port_cycle_orbit_drat.jsonl.gz"):
        for r in read(filename):
            if r["status"]!="DRAT_VERIFIED":continue
            cnf,required,free=formula(r["edges"])
            for c in r["cycles"]:
                T=set(c)
                assert len(c)==len(T) and T<=required|free and len(components(T))==1
                assert all(len(T.intersection(NEIGH[v]))==2 for v in T)
                cnf.append([-v-1 for v in c if v in free])
            with tempfile.TemporaryDirectory() as d:
                f=Path(d)/"cnf";p=Path(d)/"drat";cnf.to_file(str(f));p.write_text(r["proof"])
                proc=subprocess.run([checker,str(f),str(p)],capture_output=True)
                assert b"s VERIFIED" in proc.stdout
            print(filename,r["case"],"DRAT verified",flush=True)
if __name__=="__main__":
    if len(sys.argv)>1:drat(sys.argv[1])
    else:numeric()
