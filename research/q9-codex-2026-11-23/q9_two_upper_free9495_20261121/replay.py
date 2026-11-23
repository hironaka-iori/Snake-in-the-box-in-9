import argparse,subprocess,gzip,tempfile,shutil,json
from pathlib import Path
from banks import D,path
import sys
sys.path.insert(0,str(D.parent))
from verify_q9_intact98_all_crossings import integer_bound
arg=argparse.ArgumentParser();arg.add_argument('--drat-trim');params=arg.parse_args()
W=(D/'donors.words').read_text().split();strong=[]
for cert in sorted(D.glob('strong_*.json')):
    obj=json.loads(cert.read_text());_,i,c=cert.stem.split('_');i=int(i);c=int(c);q=path(W[i]);ends=[2*int(c==v) for v in (0,1)];delta=sum((-1)**(v.bit_count()%2) for v in q)-(ends[0]-ends[1])//2
    assert obj['word']==W[i] and set(obj['ports'])=={q[0],q[-1]} and obj['upper_delta']==delta and obj['upper_endpoint_counts']==ends
    bound=integer_bound(obj['cert'],set(q),set(obj['ports']),ends,delta)+len(q)*obj['cert']['scale'];assert bound==obj['total_scaled'] and bound<193*obj['cert']['scale'];strong.append((i,c,bound))
proofs=sorted(D.rglob('*.drat.gz'));checked=0
if params.drat_trim:
    with tempfile.TemporaryDirectory() as tdir:
        fc=Path(tdir)/'a.cnf';fd=Path(tdir)/'b.drat'
        for wire in proofs:
            cnf=wire.parent/wire.name.replace('.drat.gz','.cnf.gz')
            for src,dst in ((wire,fd),(cnf,fc)):
                with gzip.open(src,'rb') as r,dst.open('wb') as w:shutil.copyfileobj(r,w)
            run=subprocess.run([params.drat_trim,str(fc),str(fd)],capture_output=True);assert b's VERIFIED' in run.stdout,wire;checked+=1
print(json.dumps(dict(integer_checks=strong,archived_drat=len(proofs),replayed_drat=checked)))
