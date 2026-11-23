import gzip,json,subprocess,sys,tempfile
from pathlib import Path
from collections import Counter
from itertools import combinations
import random
D=Path(__file__).resolve().parent;R=D.parent;old=R/'q9_lower_island_edge_20261121'
def go():
    nk,sweeps,part,mod,tag,seed=map(str,sys.argv[1:7]);nk,sweeps,part,mod,seed=map(int,(nk,sweeps,part,mod,seed))
    cases=list(map(json.loads,(old/'cases.jsonl').read_text().splitlines()))
    finished=set()
    for f in sorted(D.glob('pass*.jsonl')):
        for l in f.read_text().splitlines():
            if not l.endswith('}'):continue
            r=json.loads(l)
            if 'file' in r:finished.add((r['i'],r['c']))
    lengths=Counter()
    for f in old.glob('*.paths'):
        for l in f.read_text().splitlines():
            i,n,*_=map(int,l.split());lengths[i]=max(lengths[i],n)
    ids=sorted([i for i,c in enumerate(cases) if len(c['w'])==93 and i not in {1249,1250,1251,1252}],key=lambda i:(-lengths[i],i))
    assert len(ids)==1510
    cells=[(i,c) for rank,i in enumerate(ids) if rank%mod==part for c in range(4) if (i,c) not in finished]
    ax=list(combinations(range(8),3));random.Random(seed).shuffle(ax);masks=[sum(1<<d for d in a) for a in ax[:nk]]
    folder=D/tag;folder.mkdir(exist_ok=True);out=D/(tag+f'_{part}.jsonl');assert not out.exists()
    with tempfile.TemporaryFile('w+') as f,out.open('w') as log:
        for i,c in cells:print(i,c,file=f)
        f.seek(0);p=subprocess.Popen([D/('diffuse20' if nk>12 else 'diffuse'),old/'cases.dat',str(sweeps),'193',','.join(map(str,masks))],stdin=f,stdout=subprocess.PIPE)
        buf=p.stdout
        for i,c in cells:
            head=buf.readline();parts=head.split();assert parts[0]==b'R' and list(map(int,parts[1:3]))==[i,c]
            v=int(parts[3]);rec=dict(i=i,c=c,score=v,sweeps=int(parts[-1]),best_previous=lengths[i])
            records=bytearray()
            for line in buf:
                if line==b'E\n':break
                if v<1930000:records.extend(line)
            if v<1930000:
                name=f'{i}_{c}.gz';rec['file']=tag+'/'+name
                (folder/name).write_bytes(gzip.compress((' '.join(map(str,masks))+'\n').encode()+head+records,compresslevel=2,mtime=0))
            print(json.dumps(rec,separators=(',',':')),file=log,flush=True)
        assert not buf.read() and p.wait()==0
if __name__=='__main__':go()
