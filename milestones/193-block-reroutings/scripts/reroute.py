from pathlib import Path
import collections,functools,hashlib,json,time
R=Path('E:/Snake-in-a-box');H=R/'milestones/193-block-reroutings';P=R/'milestones/192-moving-ports';start=time.monotonic()
assert not H.exists()
for name in ['data','scripts','lean','build','logs']:(H/name).mkdir(parents=True,exist_ok=True)
(H/'.gitattributes').write_text('* -text\n')
for name in ['check_core.py','native_resources.py','publication.py']:(H/'scripts'/name).write_bytes((P/'scripts'/name).read_bytes())
bank=json.loads((R/'work/bank9.json').read_text());NB=[{v^(1<<k) for k in range(9)} for v in range(512)];NBM=[sum(1<<v for v in q) for q in NB]
def canonical(p):
    t=[(a^b).bit_length()-1 for a,b in zip(p,p[1:])]
    def relabel(xs):
        d={};out=[]
        for x in xs:
            if x not in d:d[x]=len(d)
            out.append(d[x])
        return tuple(out)
    return min(relabel(t),relabel(t[::-1]))
known={canonical(row['vertex_sequence']):i for i,row in enumerate(bank)};new={};witnesses=[];extensions=[];rows=[];complete=True
@functools.lru_cache(None)
def routes(length,target):
    p=[0];out=[]
    def dfs(left):
        u=p[-1];dist=(u^target).bit_count()
        if dist>left or (left-dist)%2:return
        if left==0:
            if u==target:out.append(tuple(p))
            return
        for v in sorted(NB[u]):
            if v in p or any(v in NB[w] for w in p[:-1]):continue
            p.append(v);dfs(left-1);p.pop()
    dfs(length);return out
for length in [3,4,5]:
    for index,row in enumerate(bank):
        p=row['vertex_sequence'];assert len(p)==192 and len(set(p))==192
        examined=0;valid=0;newcount=0;portmoves=0;bydist=collections.Counter()
        for i in range(len(p)-length):
            j=i+length;outside=p[:i+1]+p[j:];outside_set=set(outside);forbidden=sum(1<<v for v in outside)
            for v in outside_set-{p[i],p[j]}:forbidden|=NBM[v]
            possibilities=routes(length,p[i]^p[j]);bydist[(p[i]^p[j]).bit_count()]+=1
            for route in possibilities:
                inner=[v^p[i] for v in route[1:-1]]
                if inner==p[i+1:j]:continue
                examined+=1
                if any((1<<v)&forbidden for v in inner):continue
                q=p[:i+1]+inner+p[j:];valid+=1
                assert len(set(q))==192 and all(((q[a]^q[b]).bit_count()==1)==(b==a+1) for a in range(192) for b in range(a+1,192))
                code=canonical(q);changed=[]
                for k in range(9):
                    oldcuts=[a for a in range(191) if p[a]^p[a+1]==1<<k]
                    if len(oldcuts)!=2:continue
                    newcuts=[a for a in range(191) if q[a]^q[a+1]==1<<k]
                    if oldcuts!=newcuts:changed.append({'coordinate':k,'old_cuts':oldcuts,'new_cuts':newcuts})
                portmoves+=bool(changed)
                record={'seed_index':index,'length':length,'start':i,'end':j,'old_internal':p[i+1:j],'new_internal':inner,'known_class':known.get(code),'changed_rare_crossings':changed,'path':q}
                witnesses.append(record)
                if code not in known and code not in new:new[code]=record;newcount+=1
                chosen=set(q)
                for reverse in [False,True]:
                    orient=q[::-1] if reverse else q
                    for w in NB[orient[-1]]:
                        if w not in chosen and all(w not in NB[v] for v in orient[:-1]):extensions.append({'source':{k:v for k,v in record.items() if k!='path'},'path':orient+[w]})
            if extensions:break
        rows.append({'length':length,'seed_index':index,'alternative_routes_examined':examined,'valid_moves':valid,'new_classes_first_seen':newcount,'moves_altering_rare_crossings':portmoves,'blocks_by_endpoint_distance':dict(bydist)})
        if extensions or time.monotonic()-start>180:complete=False;break
    print(json.dumps({'length':length,'elapsed':time.monotonic()-start,'valid':sum(r['valid_moves'] for r in rows if r['length']==length),'new_classes_total':len(new),'extensions':len(extensions)}),flush=True)
    if not complete:break
out={'status':'LONGER_WITNESS_FOUND' if extensions else 'COMPLETE' if complete else 'INCOMPLETE','seconds':time.monotonic()-start,'rows':rows,'summary':{str(k):{'seeds':sum(r['length']==k for r in rows),'alternatives':sum(r['alternative_routes_examined'] for r in rows if r['length']==k),'valid_moves':sum(r['valid_moves'] for r in rows if r['length']==k),'rare_crossing_moves':sum(r['moves_altering_rare_crossings'] for r in rows if r['length']==k)} for k in [3,4,5]},'new_classes':len(new),'extensions':extensions,'cache':str(routes.cache_info()),'bank_sha256':hashlib.sha256((R/'work/bank9.json').read_bytes()).hexdigest(),'scope':'All induced routes of the same3,4,5edge length between each block endpoint pair; outside path unchanged. Includes new coordinate excursions when the endpoint distance is smaller than block length. Every accepted whole path and endpoint extension is checked; no completeness claim for larger or noncontiguous replacements.'}
(H/'data/reroutings.json').write_text(json.dumps(out,indent=2)+'\n');(H/'data/rerouting-witnesses.json').write_text(json.dumps({'moves':witnesses,'new_classes':list(new.values()),'extensions':extensions},indent=2)+'\n');(H/'scripts/reroute.py').write_bytes(Path(__file__).read_bytes())
(H/'data/start.json').write_text(json.dumps({'round':193,'previous_turn':'PROGRESS: round192 published endpoint corrections and concrete Lean square-substitution exclusion.','parent_commit':'4c476081883fd0497efc25d4128674eb74c81e45','start_utc':'2026-11-11 05:22:14 UTC','goal_status':'active','contributor_head':'b2f85574241bd8d9aca499440b9bc0f3b4c0def0'},indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k not in ['rows','extensions']},indent=2),flush=True)
