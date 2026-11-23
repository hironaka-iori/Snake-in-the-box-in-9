"""Extract the archive and run python3 verify_bundle.py. Pass --native ./replay for a second backend."""
import argparse,gzip,hashlib,json,subprocess,tempfile
from pathlib import Path
from integer_checker import integer_bound
D=Path(__file__).resolve().parent
def checkwalk(p):
    assert len(set(p))==len(p)
    assert all(((v^u).bit_count()==1)==(j+1==i) for i,v in enumerate(p) for j,u in enumerate(p[:i]))
def main():
    cli=argparse.ArgumentParser();cli.add_argument('--native',type=Path);a=cli.parse_args()
    data=gzip.open(D/'catalogue.words.gz','rb').read()
    assert hashlib.sha256(data).hexdigest()==json.loads((D/'summary.json').read_text())['donor_bank_sha256']
    words=data.decode().split();ref=[];catalog=[]
    for i,w in enumerate(words):
        p=[0]
        for d in w:p.append(p[-1]^(1<<int(d)))
        checkwalk(p);catalog.append(p)
        shadow=set(p)|{v^(1<<d) for v in p for d in range(8)}
        ref.extend((i,v) for v in sorted(set(range(256))-shadow))
    rows=[json.loads(l) for l in (D/'manifest.jsonl').read_text().splitlines()]
    assert len(rows)==len(ref)==1496 and ref==[(r['i'],r['x']) for r in rows]
    with tempfile.TemporaryFile('w+') as inp,tempfile.NamedTemporaryFile('wb') as bank:
        seen={}
        for r in rows:
            i,x=r['i'],r['x'];p=catalog[i];low=set(p)|{x};ports={p[0],p[-1],x}
            c=json.load(gzip.open(D/r['cert'],'rt'));s=c['scale'];m=x.bit_count()%2
            bound=integer_bound(c,low,ports,[int(k!=m) for k in (0,1)],sum((-1)**v.bit_count() for v in low))+len(low)*s
            assert s==r['scale'] and bound==r['bound'] and bound<194*s
            if a.native:
                f=r['cert']
                if f not in seen:
                    j=len(seen);seen[f]=j;ax=[sum(1<<d for d in ds) for ds in c['axes']]
                    print('C',j,s,*c['end_weights'],c['balance_weight'],len(ax),len(c['weights']),*ax,file=inp)
                    for w in c['weights']:print(*w,file=inp)
                print('Q',seen[f],i,x,file=inp)
        if a.native:
            bank.write(data);bank.flush();inp.seek(0)
            out=subprocess.check_output([str(a.native.resolve()),bank.name],stdin=inp,text=True).splitlines()
            assert len(out)==1496
            assert all(list(map(int,l.split()))==[seen[r['cert']],r['i'],r['x'],r['bound']] for r,l in zip(rows,out))
    c=json.loads((D/'positive_verified.json').read_text());p=c['path'];checkwalk(p)
    i,x=c['case'];arm=catalog[i]
    assert len(p)==c['edges']+1 and {v for v in p if v<256}==set(arm)|{x}
    assert {(v%256) for v,w in zip(p,p[1:]) if v^w==256}=={arm[0],arm[-1],x}
    assert (p[0]^p[-1]).bit_count()%2==1
    print('Verified 1496 odd-endpoint upper bounds and the',c['edges'],'edge positive control.')
if __name__=='__main__':main()
