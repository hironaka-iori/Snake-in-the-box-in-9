from pathlib import Path
import collections,hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
source=H/'data/shorten2-blocks4-24.json'
data=json.loads(source.read_text());assert data['status']=='COMPLETE'
bank=json.loads((R/'work/bank9.json').read_text())
N=[{v^(1<<k) for k in range(9)} for v in range(512)]
def canonical(p):
    t=[(u^v).bit_length()-1 for u,v in zip(p,p[1:])]
    def relabel(t):
        d={};r=[]
        for x in t:
            if x not in d:d[x]=len(d)
            r.append(d[x])
        return tuple(r)
    return min(relabel(t),relabel(t[::-1]))
def valid(p):
    return len(set(p))==len(p) and all((((u^p[j]).bit_count()==1)==(j==i+1)) for i,u in enumerate(p) for j in range(i+1,len(p)))
known={canonical(r['vertex_sequence']):i for i,r in enumerate(bank)}
rows=[];all_returned=set();new_returned={};longer=[];maxima=collections.Counter()
for index,row in enumerate(data['new_classes']):
    levels=[{canonical(row['path']):row['path']}]
    for depth in range(3):
        level={}
        for q in levels[-1].values():
            for rev in [False,True]:
                p=q[::-1] if rev else q
                for w in N[p[-1]]:
                    if w not in p and all(w not in N[z] for z in p[:-1]):
                        t=p+[w];assert valid(t)
                        level[canonical(t)]=t
        levels.append(level)
    returned=sorted({known[c] for c in levels[2] if c in known})
    for c,p in levels[2].items():
        if c not in known:new_returned[c]=p
    longer.extend(levels[3].values());all_returned.update(returned)
    maximum=max(k for k,level in enumerate(levels) if level);maxima[maximum]+=1
    rows.append(dict(shortened_class=index,source_seed=row['seed'],source_block=[row['start'],row['end']],
        class_counts_by_added_edges=[len(level) for level in levels],maximum_added_edges=maximum,returned_bank_classes=returned))
out=dict(status='COMPLETE',shortened_classes=len(rows),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
    maxima=dict(maxima),returned_bank_classes=sorted(all_returned),new_191_classes=list(new_returned.values()),
    longer=longer,rows=rows,scope='All endpoint additions through depth three from every symmetry class of 189-edge outcomes. Each step may use either endpoint; equivalence reduction preserves all future endpoint possibilities.')
target=H/'data/regrowth.json';assert not target.exists();target.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='rows'},indent=2))
