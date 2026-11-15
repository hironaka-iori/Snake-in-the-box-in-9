"""Prepare every maximal short two-block context for endpoint24."""
from pathlib import Path
import collections,hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
source=R/'milestones/223-coupled-four-crossings/data/joint-d4.json'
p=json.loads(source.read_bytes())['seed'];N=[{v^(1<<k) for k in range(9)} for v in range(512)]
endpoint=24
assert p[7]==28 and p[143]==56 and p[-1]==88
assert [i for i,v in enumerate(p[:-1]) if v==endpoint or v in N[endpoint]]==[7,143]
def peel(values,u,v):
    values=set(values);removed=[]
    queue=collections.deque(z for z in values if z not in [u,v] and len(N[z]&values)<2)
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
    b=a+33
    for c in range(111,143):
        d=c+33;intervals=[(a,b),(c,d)]
        retained={v for i,v in enumerate(p) if not(a<i<b or c<i<d)}
        assert all(v not in N[endpoint] and v!=endpoint for v in retained if v!=88)
        parts=[]
        for index,(i,j) in enumerate(intervals):
            u,v=p[i],p[j];forbidden=set(retained)|N[endpoint]|{endpoint}
            for z in retained-{u,v}:forbidden |=N[z]
            values=(set(range(512))-forbidden)|{u,v}
            if index==0:values={z for z in values if z<256}
            initial=sorted(values);values,removed=peel(values,u,v)
            other=intervals[1-index];old_other=p[other[0]+1:other[1]]
            contact=sorted(z for z in values-{u,v} if any(z==w or w in N[z] for w in old_other))
            reasons=[]
            if v not in values:reasons.append('DISCONNECTED')
            if len(values)<34:reasons.append('SIZE')
            if any(sum(z.bit_count()%2==colour for z in values)<17 for colour in [0,1]):reasons.append('COLOUR')
            if not contact:reasons.append('NO_CROSS_CONTACT')
            parts.append(dict(interval=[i,j],anchors=[u,v],crossings=index,initial_allowed=initial,allowed=sorted(values),peeling_order=removed,contact_candidates=contact,rejections=reasons))
        rows.append(dict(id=len(rows),intervals=intervals,retained=sorted(retained),parts=parts,status='STATIC_EXCLUDED' if any(q['rejections'] for q in parts) else 'PENDING'))
out=dict(seed=p,endpoint=endpoint,source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),contexts=rows,scope='All224 pairs of33-edge windows containing old blocker indices7 and143 in their open interiors. Both replacement lengths remain33; anchors and outside positions stay fixed; endpoint24 is appended. The first replacement stays in the lower face and the second crosses bit8 once, as required by exactlyfour total crossings. NO_CROSS_CONTACT uses the short-move closure argument conditional on the native round193 census.')
dest=H/'data/regions.json';assert not dest.exists();dest.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(contexts=len(rows),statuses=dict(collections.Counter(r['status'] for r in rows)),pending=[r['id'] for r in rows if r['status']=='PENDING'],reasons=dict(collections.Counter(reason for r in rows for part in r['parts'] for reason in part['rejections'])))),flush=True)
