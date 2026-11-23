import json,gzip,itertools,hashlib,subprocess,tempfile
from pathlib import Path
from integer_checker import integer_bound
D=Path(__file__).resolve().parent
archive=gzip.open(D/'catalogue.words.gz','rb').read();words=archive.decode().split()
assert hashlib.sha256(archive).hexdigest()==json.loads((D/'summary.json').read_text())['bank_sha256']
manifest=[json.loads(l) for l in (D/'manifest.jsonl').read_text().splitlines()]
trees={z['rank']:z for l in (D/'tree_manifest.jsonl').read_text().splitlines() if(z:=json.loads(l))}
catalog=[];jobs=[]
for i,word in enumerate(words):
    a=[0]
    for d in word:a.append(a[-1]^(1<<int(d)))
    assert len(set(a))==len(a) and all(((x^y).bit_count()==1)==(k==j+1)for k,x in enumerate(a)for j,y in enumerate(a[:k]))
    shadow=set(a)|{x^(1<<d) for x in a for d in range(8)}
    jobs.extend((i,x) for x in sorted(set(range(256))-shadow));catalog.append(a)
assert len(manifest)==len(jobs)==1496 and jobs==[(r['i'],r['x']) for r in manifest]
with tempfile.TemporaryDirectory() as t:
    t=Path(t);(t/'words').write_bytes(archive)
    for source,out in [('emit_tables.cpp','tables'),('tree_replay.cpp','replay')]:
        subprocess.run(['c++','-std=c++20','-O3',str(D/source),'-o',str(t/out)],check=True)
    nproof=0
    for rank,r in enumerate(manifest):
        i,x=jobs[rank];p=catalog[i];m=x.bit_count()%2;L=set(p)|{x};P={p[0],p[-1],x}
        c=json.load(gzip.open(D/r['cert'],'rt'));delta=sum((-1)**v.bit_count() for v in L)-(-1)**m
        n=integer_bound(c,L,P,[int(j==m) for j in (0,1)],delta)+len(L)*c['scale']
        assert n==r['bound'] and c['scale']==r['scale']
        if n<193*c['scale']:assert rank not in trees;continue
        z=trees[rank];assert (z['i'],z['x'])==(i,x);nproof+=1
        with (t/'input').open('w') as f:
            print('C',0,c['scale'],*c['end_weights'],c['balance_weight'],len(c['axes']),len(c['weights']),*(sum(1<<j for j in a) for a in c['axes']),file=f)
            for w in c['weights']:print(*w,file=f)
        with (t/'input').open() as f,(t/'data').open('w') as o:subprocess.run([str(t/'tables'),str(t/'words'),str(i),str(x)],stdin=f,stdout=o,check=True)
        (t/'branch').write_bytes(gzip.open(D/z['tree'],'rb').read())
        out=subprocess.check_output([str(t/'replay'),str(t/'data'),str(t/'branch'),'193'],text=True).strip()
        assert out==z['replay'] and ' open 0 witnesses 0 ' in out and ' invalid_full 0 ' in out
assert nproof==len(trees)==55
print('Verified all 1496 same-colour cases including 55 complete integer splitting trees.')
