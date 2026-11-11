from pathlib import Path
import re,json,collections,hashlib
R=Path('E:/Snake-in-a-box');H=R/'milestones/188-dimensional-constructions'
html=(H/'sources/minortriad-index.html').read_text(encoding='utf-8')
def check(v,n):
    assert len(v)==len(set(v)) and all(0<=x<1<<n for x in v)
    for i,x in enumerate(v):
        for j in range(i+1,len(v)):
            assert ((x^v[j]).bit_count()==1)==(j==i+1),(n,i,j)
def project(v,k):return (v&((1<<k)-1))|((v>>(k+1))<<k)
def profile(v,n):
    check(v,n);out=[]
    for k in range(n):
        cuts=[i for i in range(len(v)-1) if v[i]^v[i+1]==1<<k]
        parts=[];start=0
        for stop in cuts+[len(v)-1]:
            path=[project(x,k) for x in v[start:stop+1]];check(path,n-1)
            parts.append({'start':start,'stop':stop,'side':(v[start]>>k)&1,'edges':stop-start,'path':path});start=stop+1
        faces=[{project(x,k) for x in v if (x>>k)&1==b} for b in [0,1]]
        overlap=sorted(faces[0]&faces[1]);assert len(overlap)==len(cuts)
        assert sum(p['edges'] for p in parts)+len(cuts)==len(v)-1
        out.append({'coordinate':k,'crossings':len(cuts),'cut_indices':cuts,'component_edges':[p['edges'] for p in parts],
                    'face_vertices':[len(x) for x in faces],'face_components':[sum(p['side']==b for p in parts) for b in [0,1]],'overlap':overlap,'parts':parts})
    return sorted(out,key=lambda x:(x['crossings'],-max(x['component_edges']),x['coordinate']))
seeds={}
for n in [5,6,7,8]:
    match=re.search(r'\{ id:"sn'+str(n)+r'", ref:"([^"]+)"\s*, ts:\s*"([^"]+)"',html,re.S)
    assert match,n
    seq=[int(x,16) for x in re.sub(r'[\s\\]','',match[2])]
    v=[0]
    for d in seq:v.append(v[-1]^(1<<d))
    result={'dimension':n,'edges':len(seq),'source':'https://minortriad.com/snake/','reference':match[1],'transitions':seq,'vertices':v,'profiles':profile(v,n)}
    seeds[str(n)]=result
    print(n,len(seq),'counts',dict(sorted(collections.Counter(seq).items())),'least',[(x['coordinate'],x['crossings'],x['component_edges']) for x in result['profiles'][:3]])
bank=json.loads((R/'work/bank9.json').read_text())
bankstats=[]
for i,row in enumerate(bank):
    p=profile(row['vertex_sequence'],9)
    bankstats.append({'index':i,'minimum_crossings':p[0]['crossings'],'best_profiles':[{k:x[k] for k in ['coordinate','crossings','component_edges','face_vertices','face_components']} for x in p if x['crossings']==p[0]['crossings']]})
(H/'data/lower-dimensional-seeds.json').write_text(json.dumps(seeds,indent=2)+'\n')
(H/'data/bank9-face-profiles.json').write_text(json.dumps({'source_sha256':hashlib.sha256((R/'work/bank9.json').read_bytes()).hexdigest(),'paths':bankstats},indent=2)+'\n')
(H/'scripts/profiles.py').write_bytes(Path(__file__).read_bytes())
print('Bank minimum crossing distribution',dict(collections.Counter(x['minimum_crossings'] for x in bankstats)))
print('Bank face pairs',dict(collections.Counter(tuple(x['best_profiles'][0]['component_edges']) for x in bankstats)))
