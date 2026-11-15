"""Prepare wider simultaneous replacements without transferring smaller exclusions."""
from pathlib import Path
import argparse,collections,hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
ap=argparse.ArgumentParser();ap.add_argument('--width',type=int,required=True);a=ap.parse_args();w=a.width
assert 45<=w<=50
source=R/'milestones/223-coupled-four-crossings/data/joint-d4.json';p=json.loads(source.read_bytes())['seed']
N=[{v^(1<<k) for k in range(9)} for v in range(512)]
def sha(q):return hashlib.sha256(Path(q).read_bytes()).hexdigest()
def peel(values,u,v):
    values=set(values);removed=[];queue=collections.deque(z for z in values if z not in [u,v] and len(N[z]&values)<2)
    while queue:
        z=queue.popleft()
        if z not in values or len(N[z]&values)>=2:continue
        neighbours=N[z]&values;values.remove(z);removed.append(z)
        queue.extend(t for t in neighbours if t not in [u,v] and len(N[t]&values)<2)
    seen={u};todo=[u]
    while todo:
        z=todo.pop()
        for t in (N[z]&values)-seen:seen.add(t);todo.append(t)
    return values&seen,removed
rows=[]
for start in range(7):
    end=start+w
    for other in range(144-w,143):
        finish=other+w;intervals=[[start,end],[other,finish]]
        retained={v for i,v in enumerate(p) if not(start<i<end or other<i<finish)}
        assert all(v not in N[24] and v!=24 for v in retained if v!=88)
        parts=[]
        for i,j in intervals:
            u,v=p[i],p[j];forbidden=set(retained)|N[24]|{24}
            for z in retained-{u,v}:forbidden|=N[z]
            values=(set(range(512))-forbidden)|{u,v};initial=sorted(values)
            values,removed=peel(values,u,v);reasons=[]
            if v not in values:reasons.append('DISCONNECTED')
            if len(values)<w+1:reasons.append('SIZE')
            even=(w+2)//2 if u.bit_count()%2==0 else (w+1)//2
            if sum(z.bit_count()%2==0 for z in values)<even or sum(z.bit_count()%2==1 for z in values)<w+1-even:reasons.append('COLOUR')
            parts.append(dict(interval=[i,j],anchors=[u,v],initial_allowed=initial,allowed=sorted(values),peeling_order=removed,required_even=even,target_vertices=w+1,rejections=reasons))
        fixed=sum(u^v==256 for i,(u,v) in enumerate(zip(p,p[1:])) if not(start<=i<end or other<=i<finish))
        rows.append(dict(id=len(rows),intervals=intervals,retained=sorted(retained),parts=parts,replacement_crossings=4-fixed,status='STATIC_EXCLUDED' if any(x['rejections'] for x in parts) else 'PENDING'))
out=dict(width=w,seed=p,endpoint=24,contexts=rows,pins={str(q):sha(q) for q in [source,Path(__file__)]},scope='All maximal equal-width two-block replacements containing blockers7and143 of fixedseed, endpoint24 appended, exactlyfour bit8crossings. Anchors/outside indices retained. No inherited smaller-width exclusion and no short-move closure premise.')
dest=H/'data'/f'regions{w}.json';assert not dest.exists();dest.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(width=w,contexts=len(rows),statuses=dict(collections.Counter(r['status'] for r in rows)))),flush=True)
