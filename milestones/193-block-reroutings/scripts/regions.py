"""Enumerate induced replacements inside regions freed by a contiguous deletion."""
from pathlib import Path
import argparse, collections, hashlib, json, time
from native_resources import snapshot

H = Path(__file__).resolve().parents[1]
R = H.parents[1]
ap = argparse.ArgumentParser()
ap.add_argument('--first', type=int, default=6)
ap.add_argument('--last', type=int, default=24)
ap.add_argument('--seconds', type=float, default=180)
ap.add_argument('--loss', type=int, default=0)
ap.add_argument('--tag', default='regions6-24')
a = ap.parse_args()
assert a.loss >= 0 and a.loss % 2 == 0
dest = H/'data'/(a.tag+'.json')
assert not dest.exists()
gate = snapshot()
assert not gate['errors'] and not gate['processes'] and gate['free_bytes'] >= 1024**3, gate
raw = (R/'work/bank9.json').read_bytes()
bank = json.loads(raw)
N = [[v^(1<<k) for k in range(9)] for v in range(512)]
NM = [sum(1<<w for w in ns) for ns in N]

def canonical(p):
    t = [(u^v).bit_length()-1 for u,v in zip(p,p[1:])]
    def renumber(xs):
        d = {}; out = []
        for x in xs:
            if x not in d: d[x] = len(d)
            out.append(d[x])
        return tuple(out)
    return min(renumber(t),renumber(t[::-1]))

def valid(p):
    return len(set(p)) == len(p) and all(
        (((u^p[j]).bit_count()==1) == (j==i+1))
        for i,u in enumerate(p) for j in range(i+1,len(p)))

known = {canonical(row['vertex_sequence']): i for i,row in enumerate(bank)}
new = {}; examples = []; growth = []; rows = []; nodes = 0
started = time.monotonic(); current = None

class EndSearch(Exception): pass

def grow(q, remaining):
    if remaining == 0: return q
    occupied = set(q)
    for reverse in [False,True]:
        p = q[::-1] if reverse else q
        for w in N[p[-1]]:
            if w not in occupied and all(w not in N[v] for v in p[:-1]):
                ans = grow(p+[w],remaining-1)
                if ans is not None: return ans
    return None

def save(status):
    out = dict(status=status, seconds=time.monotonic()-started, arguments=vars(a),
        bank_sha256=hashlib.sha256(raw).hexdigest(), resource_gate=gate, nodes=nodes,
        completed_rows=rows, current_incomplete=current if status!='COMPLETE' else None,
        new_classes=list(new.values()), examples=examples, growth=growth,
        scope='Fixed endpoints and outside order; enumerate all induced replacement routes of block length minus loss. Each accepted whole path independently checked. Endpoint growth can alternate ends. Only completed rows are exhaustive.')
    dest.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')

try:
    for length in range(a.first,a.last+1):
        for index,entry in enumerate(bank):
            p = entry['vertex_sequence']; assert valid(p)
            oldcuts = {k: [z for z in range(191) if p[z]^p[z+1]==1<<k] for k in range(9)}
            current = dict(length=length, seed=index, blocks_complete=0,
                routes=0, valid_moves=0, rare_crossing_moves=0, new_classes=0)
            for i in range(len(p)-length):
                j=i+length; u=p[i]; v=p[j]
                retained=p[:i+1]+p[j:]
                forbidden=sum(1<<z for z in retained)
                for z in retained:
                    if z!=u and z!=v: forbidden |= NM[z]
                route=[u]
                def dfs(left, blocked):
                    global nodes
                    nodes+=1
                    if nodes % 1024 == 0:
                        if time.monotonic()-started>a.seconds: raise EndSearch()
                    last=route[-1]; distance=(last^v).bit_count()
                    if distance>left or (left-distance)%2: return
                    if left==1:
                        if v not in N[last] or ((1<<v)&blocked): return
                        current['routes']+=1
                        inner=route[1:]
                        if inner==p[i+1:j]: return
                        q=p[:i+1]+inner+p[j:]
                        assert len(q)==192-a.loss and valid(q)
                        current['valid_moves']+=1
                        changed=[k for k,cuts in oldcuts.items() if len(cuts)==2 and
                            cuts!=[z for z in range(len(q)-1) if q[z]^q[z+1]==1<<k]]
                        current['rare_crossing_moves']+=bool(changed)
                        code=canonical(q)
                        record=dict(seed=index,start=i,end=j,block_length=length,
                            new_internal=inner[:],path=q,known_class=known.get(code),changed_rare_coordinates=changed)
                        if code not in known and code not in new:
                            new[code]=record; current['new_classes']+=1
                        if changed and len(examples)<20: examples.append(record)
                        ext=grow(q,a.loss+1)
                        if ext is not None:
                            assert len(ext)==193 and valid(ext)
                            growth.append(dict(source=record,path=ext)); raise EndSearch()
                        return
                    excluded=blocked|forbidden|(1<<v)
                    for w in N[last]:
                        if (1<<w)&excluded: continue
                        route.append(w)
                        dfs(left-1,blocked|NM[last]|(1<<last))
                        route.pop()
                dfs(length-a.loss,0)
                current['blocks_complete']+=1
            rows.append(current); current=None
        print(json.dumps(dict(length=length,seconds=time.monotonic()-started,
            moves=sum(r['valid_moves'] for r in rows if r['length']==length),
            new_classes=len(new),nodes=nodes)),flush=True)
        save('CHECKPOINT')
    save('COMPLETE')
except EndSearch:
    save('LONGER_WITNESS_FOUND' if growth else 'TIME_LIMIT')
print(json.dumps(dict(file=str(dest),rows=len(rows),new_classes=len(new),growth=len(growth),nodes=nodes,seconds=time.monotonic()-started)),flush=True)
