from geom import *
import hashlib,itertools,sys,subprocess,tempfile
from collections import Counter
def verify(path_filter=''):
    selected,rows=regs()
    if path_filter:selected={k:v for k,v in selected.items() if v['file'].startswith(path_filter)}
    targets={i for i,s in enumerate(cases) if len(s['w'])==93}-{1249,1250,1251,1252}
    assert len(targets)==1510 and all(i in targets and 0<=c<4 for i,c in selected)
    source_keys=set()
    for i in targets:
        z=cases[i];q=[0]
        for step in z['w']:
            assert '0'<=step<='7';q.append(q[-1]^(1<<int(step)))
        assert q==z['lo'] and len(set(q))==len(q)==94
        ix={v:j for j,v in enumerate(q)}
        assert all({ix[x^1<<d] for d in range(8) if x^1<<d in ix}=={j for j in (k-1,k+1) if 0<=j<len(q)} for k,x in enumerate(q))
        a,b=z['edge'];assert 0<=a<b<256 and (a^b).bit_count()==1 and min((u^v).bit_count() for u in (a,b) for v in q)>=2
        assert len({tuple(sorted(geometry(i,k)[1])) for k in range(4)})==4
        source_keys.add((z['w'],a,b))
    assert len(source_keys)==1510
    positive=defaultdict(int);checked=0
    for f in [*old.glob('*.paths'), *(D/name for name in ('mixed.paths','deep.paths','regrow.paths') if (D/name).exists())]:
        for s in f.read_text().splitlines():
            i,n,*p=map(int,s.split())
            if i not in targets or n%2:continue
            out={min(x,y) for x,y in zip(p,p[1:]) if x^y==256};c=cases[i]
            code=2*(c['edge'][1] in out)+(len(out)-2)
            L,P,m,eps,delta=geometry(i,code);assert out==P and L==set(x for x in p if x<256)
            assert p[0].bit_count()%2==p[-1].bit_count()%2==m and len(p)==len(set(p))==n+1
            pos={v:j for j,v in enumerate(p)};assert all({pos[q] for q in [x^1<<d for d in range(9)] if q in pos}=={j for j in (t-1,t+1) if 0<=j<len(p)} for t,x in enumerate(p))
            positive[i,code]=max(positive[i,code],len(p));checked+=1
    asserts=0;ranked=[]
    with tempfile.TemporaryFile('w+b') as encoded:
        for k,r in sorted(selected.items()):
            i,c=k;L,P,m,eps,delta=geometry(i,c)
            stream=gzip.decompress((D/r['file']).read_bytes()).split(b'\n',2);maskline,header,weights=stream
            h=header.split();ri,rc,v,scale,bal,e,o,sw=map(int,h[1:]);assert h[0]==b'R' and (ri,rc)==k and v==r['score'] and v<193*scale and scale==10000
            if k in positive:assert v>=positive[k]*scale;asserts+=1
            header=[i,c,len(L),len(P),sum(eps),m,delta,scale,bal,e,o,len(maskline.split()),weights.count(b'\n'),v]
            encoded.write((' '.join(map(str,header+sorted(L)+sorted(P)))+' ').encode()+maskline+b'\n'+weights)
            ranked.append((i,c,v))
        encoded.seek(0)
        res=subprocess.run([D/'fast_check'],stdin=encoded,stdout=subprocess.PIPE,check=True)
        assert [tuple(map(int,s.split())) for s in res.stdout.splitlines()]==ranked
    covered=Counter(i for i,c in selected);closed={i for i,z in covered.items() if z==4}
    owners=Counter(r['file'].split('/')[0] for r in selected.values())
    summary=dict(source_sha256=hashlib.sha256((old/'cases.jsonl').read_bytes()).hexdigest(),cases=1510,total_cells=6040,closed_cells=len(selected),closed_cases=len(closed),open_cases=sorted(targets-closed),open_cells_by_geometry=Counter(4-covered[i] for i in targets),positive_even_paths=checked,distinct_positive_layouts=len(positive),covered_positive_layouts=asserts,files_by_pass=owners,largest_closed_numerator=max(r['score'] for r in selected.values()),hot189={i:[c for c in range(4) if (i,c) in selected] for i in (962,1215)})
    dest=D/('audit'+('_'+path_filter if path_filter else '')+'.json')
    dest.write_text(json.dumps(summary,indent=2)+'\n')
    (D/('chosen'+('_'+path_filter if path_filter else '')+'.jsonl')).write_text(''.join(json.dumps(r,separators=(',',':'))+'\n' for _,r in sorted(selected.items())))
    print({k:v for k,v in summary.items() if k!='open_cases'},flush=True)
if __name__=='__main__':verify(*sys.argv[1:])
