from prepare import *
from repair import model
import collections,hashlib
def key(p):
    w=''.join(str((a^b).bit_length()-1) for a,b in zip(p,p[1:]))
    def f(s):
        d={};return ''.join(str(d.setdefault(v,len(d))) for v in s)
    return min(f(w),f(w[::-1]))
rs={r['rank']:r for r in json.loads((B/'branches.json').read_text())}
catalogue={key(path(w)) for w in bank}; ps=collections.defaultdict(list)
for line in (B/'placements.txt').read_text().splitlines():
    i,t,sc,src,j,d,*p=map(int,line.split());r=rs[i];geometry(p)
    assert len(p)==192 and key(p)==key(path(bank[src])) and p[j]==r['ep'] and p[j+d]==r['new_vertex']
    assert bool(t)==(j+d in (0,191)) and not(set(r['forbidden'])&set(p)) and sc==len(set(p)&set(r['oldfixed']))
    ps[i].append(p)
out={'placements':sum(map(len,ps.values()))}
geometry_classes=set()
for name,end in [('crossover_final','DONE'),('interior','SEARCH')]:
    highest=0;tested=0;finish=0;n=0;keys=set(); outsideparents=0
    for l in (B/(name+'.log')).read_text().splitlines():
        z=l.split()
        if z[0]==end:tested+=int(z[2]);finish+=int(z[4]);continue
        i,length,sa,sb,oa,ob,la,lb,mid,*p=map(int,z[1:]);geometry(p);n+=1
        r=rs[i];a=ps[i][sa];b=ps[i][sb];hard=(set(r['oldfixed'])&set(a)&set(b))|{r['ep'],r['new_vertex']}
        assert len(p)==length+1 and hard<=set(p) and not set(p)&set(r['forbidden'])
        if name=='crossover_final':
            aa=(a[::-1] if oa else a)[:la];bb=(b[::-1] if ob else b)[:lb][::-1]
            u=p.index(aa[0]);assert p[u:u+la]==aa and p[u+la+mid:u+la+mid+lb]==bb
        if length==191:
            keys.add(key(p));outsideparents=max(outsideparents,min(len(set(p)-set(a)),len(set(p)-set(b))))
        highest=max(highest,length)
    geometry_classes|=keys
    out[name]=dict(tested=tested,completed_or_unique=finish,records=n,maximum=highest,classes191=len(keys),new191=len(keys-catalogue),max_outside_each_parent=outsideparents)
out['pooled_191_classes']=len(geometry_classes);out['pooled_new_191']=len(geometry_classes-catalogue)
for name in ['near','target','planted','unions','challenge']:
    obj=[json.loads(l) for l in (B/(name+'.jsonl')).read_text().splitlines()];states=collections.Counter()
    for o in obj:
        r=rs[o['rank']];old=set(r['oldfixed']);freed=set(o['freed'])
        assert freed<=old and r['ep'] not in freed
        states[o['result']]+=1
        if o['result']=='FOUND':
            p=o['path'];geometry(p);assert (old-freed)|{r['new_vertex']}<=set(p) and not set(p)&set(r['forbidden']) and len(p)==192
    out[name]=dict(states=states,release_range=[min(len(o['freed']) for o in obj),max(len(o['freed']) for o in obj)])
certs=list(map(json.loads,(B/'certified.jsonl').read_text().splitlines()));grow={r['rank']:r for r in map(json.loads,(B/'grown.jsonl').read_text().splitlines())}
for c in certs:
    i=c['rank'];r=rs[i];g=grow[i];m=set(g['mandatory']);old=set(r['oldfixed'])
    assert set(g['freed'])==old-m and m<=old and r['ep'] in m
    F,_,__,___=model(r,m,193,r['majority'])
    assert hashlib.sha256((F.to_dimacs()+'\n').encode()).hexdigest()==c['cnf_sha256']
    assert hashlib.sha256((B/f'core{i}.drat').read_bytes()).hexdigest()==c['drat_sha256']
out['certified']=[(c['rank'],c['remaining'],c['removed']) for c in certs]
print(json.dumps(out,indent=2))
