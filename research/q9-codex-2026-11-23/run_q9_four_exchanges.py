"""Run one local enumeration at a time. Resume only after checked, complete prior rows."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time
inputs=Path("q9_onechord_minority_sets.txt")
source=Path("search_q9_parity_combinations.cpp")
logfile=Path("q9_four_exchange_progress.jsonl")
binary=Path(sys.argv[1]).resolve()
rows=[list(map(int,l.split())) for l in inputs.read_text().splitlines()]
signature=hashlib.sha256(inputs.read_bytes()+source.read_bytes()+binary.read_bytes()).hexdigest()
def check_witness(p,original):
    assert len(p)==len(set(p))==193 and all(0<=v<512 for v in p)
    assert all(((x^p[j]).bit_count()==1)==(j==i+1) for i,x in enumerate(p) for j in range(i+1,len(p)))
    assert len(set(original)-set(p[1::2]))==4
def main():
    import fcntl,math
    with logfile.open("a+") as log:
        fcntl.flock(log,fcntl.LOCK_EX|fcntl.LOCK_NB)
        log.seek(0);done=set()
        for l in log:
            r=json.loads(l);assert r["signature"]==signature
            if r["status"]=="FOUND":check_witness(r["witness"],rows[r["id"]]);return
            assert r["id"] not in done and r["status"] in ("EXCLUDED","PARTIAL")
            done.add(r["id"])
        # Try neighborhoods which previously admitted the most full graph checks first.
        prior=Path("q9_onechord_parity_three.log").read_text().splitlines()
        rank={int(t[1]):int(t[-2]) for t in (l.split() for l in prior) if t[0]=="ROW"}
        order=sorted(range(len(rows)),key=lambda k:(-rank.get(k,0),k))
        for idx in order:
            if idx in done:continue
            since=time.monotonic()
            call=subprocess.run([str(binary),"192","4","0","1","sets"],input=" ".join(map(str,rows[idx]))+"\n",text=True,capture_output=True,check=True)
            t=call.stdout.split()
            if t[0]=="FOUND":
                p=list(map(int,t[1:]));check_witness(p,rows[idx]);record=dict(status="FOUND",witness=p)
            else:
                assert len(t)==7 and t[:3]==["ROW","0","0"] and int(t[3])==math.comb(96,4)
                record=dict(status="PARTIAL" if int(t[-1]) else "EXCLUDED",removed_sets=int(t[3]),search_nodes=int(t[4]),tested_graphs=int(t[5]),unknown=int(t[6]))
            record.update(id=idx,signature=signature,seconds=round(time.monotonic()-since,2))
            log.write(json.dumps(record)+"\n");log.flush()
            if record["status"]=="FOUND":break
if __name__=="__main__":main()
