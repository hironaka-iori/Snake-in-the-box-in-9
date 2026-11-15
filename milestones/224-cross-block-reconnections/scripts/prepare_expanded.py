"""Prepare 44-edge simultaneous replacements without short-closure pruning."""
from pathlib import Path
import collections,hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
source=R/'milestones/223-coupled-four-crossings/data/joint-d4.json'
p=json.loads(source.read_bytes())['seed'];N=[{v^(1<<k) for k in range(9)} for v in range(512)]
width=44;endpoint=24
def peel(values,u,v):
    values=set(values);removed=[];queue=collections.deque(z for z in values if z not in [u,v] and len(N[z]&values)<2)
    while queue:
        z=queue.popleft()
        if z not in values or len(N[z]&values)>=2:continue
        neighbours=N[z]&values;values.remove(z);removed.append(z)
        queue.extend(w for w in neighbours if w not in [u,v] and len(N[w]&values)<2)
    seen={u};todo=[u]
    while todo:
        z=todo.pop()
        for w in N[z]&values-seen:seen.add(w);todo.append(w)
    return values&seen,removed
rows=[]
for a in range(7):
    b=a+width
    for c in range(143-width+1,143):
        d=c+width;intervals=[(a,b),(c,d)]
        retained={v for i,v in enumerate(p) if not(a<i<b or c<i<d)}
        assert all(v not in N[endpoint] and v!=endpoint for v in retained if v!=88)
        parts=[]
        for i,j in intervals:
            u,v=p[i],p[j];forbidden=set(retained)|N[endpoint]|{endpoint}
            for z in retained-{u,v}:forbidden |=N[z]
            values=(set(range(512))-forbidden)|{u,v}
            initial=sorted(values);values,removed=peel(values,u,v)
            reasons=[]
            if v not in values:reasons.append('DISCONNECTED')
            if len(values)<width+1:reasons.append('SIZE')
            required_even=23 if u.bit_count()%2==0 else 22
            if sum(z.bit_count()%2==0 for z in values)<required_even or sum(z.bit_count()%2==1 for z in values)<45-required_even:reasons.append('COLOUR')
            parts.append(dict(interval=[i,j],anchors=[u,v],initial_allowed=initial,allowed=sorted(values),peeling_order=removed,required_even=required_even,target_vertices=width+1,rejections=reasons))
        fixed_crossings=sum(u^v==256 for index,(u,v) in enumerate(zip(p,p[1:])) if not(a<=index<b or c<=index<d))
        rows.append(dict(id=len(rows),intervals=intervals,retained=sorted(retained),parts=parts,replacement_crossings=4-fixed_crossings,status='STATIC_EXCLUDED' if any(q['rejections'] for q in parts) else 'PENDING'))
out=dict(seed=p,endpoint=endpoint,width=width,source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),contexts=rows,scope='All301 pairs of44-edge windows containing blocker indices7/143. Equal-length replacements and endpoint24 extension, exactlyfour total bit8crossings. No mutualcontact restriction and no short-move closure premise.')
dest=H/'data/regions44.json';assert not dest.exists();dest.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(contexts=len(rows),statuses=dict(collections.Counter(r['status'] for r in rows)),largest_domains=[max(len(r['parts'][k]['allowed']) for r in rows) for k in [0,1]])),flush=True)
