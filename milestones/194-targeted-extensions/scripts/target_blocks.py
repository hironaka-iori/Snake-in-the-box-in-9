"""Target one new endpoint while replacing a contiguous block at unchanged length."""
from pathlib import Path
import argparse,collections,hashlib,json,time
from native_resources import snapshot
from block_bounds import terminal_blocks
H=Path(__file__).resolve().parents[1]
ap=argparse.ArgumentParser();ap.add_argument('--first',type=int,default=34);ap.add_argument('--last',type=int,default=64)
ap.add_argument('--seconds',type=float,default=180);ap.add_argument('--nodes-per-query',type=int,default=100000)
ap.add_argument('--tag',default='target34-64');a=ap.parse_args()
dest=H/'data'/(a.tag+'.json');assert not dest.exists()
gate=snapshot();assert not gate['errors'] and not gate['processes'] and gate['free_bytes']>=1024**3,gate
raw=(H/'data/bank9-input.json').read_bytes();bank=json.loads(raw)
N=[[v^(1<<k) for k in range(9)] for v in range(512)];NM=[sum(1<<v for v in ns) for ns in N]
ALL=(1<<512)-1;EVEN=sum(1<<v for v in range(512) if v.bit_count()%2==0)
started=time.monotonic();nodes=0;rows=[];unknown=[];current=None;witness=None;static_examples={}

def bits(mask):
    while mask:
        b=mask&-mask;mask^=b;yield b.bit_length()-1

def valid(p):
    return len(set(p))==len(p) and all((((u^p[j]).bit_count()==1)==(j==i+1)) for i,u in enumerate(p) for j in range(i+1,len(p)))

def peel(mask,u,v):
    queue=collections.deque(z for z in bits(mask) if z!=u and z!=v and (NM[z]&mask).bit_count()<2)
    removed=[]
    while queue:
        z=queue.popleft();b=1<<z
        if not mask&b:continue
        neighbours=NM[z]&mask
        if neighbours.bit_count()>=2:continue
        mask^=b;removed.append(z)
        for w in bits(neighbours):
            if w!=u and w!=v and (NM[w]&mask).bit_count()<2:queue.append(w)
    return mask,removed

def component(mask,u):
    seen=1<<u;front=seen;distance=0;dist={u:0}
    while front:
        neighbours=0
        for z in bits(front):neighbours|=NM[z]
        front=neighbours&mask&~seen;seen|=front;distance+=1
        for z in bits(front):dist[z]=distance
    return seen,dist

class Stop(Exception):pass
class QueryLimit(Exception):pass

def save(status):
    out=dict(status=status,arguments=vars(a),seconds=time.monotonic()-started,nodes=nodes,resource_gate=gate,
        block_bounds_sha256=hashlib.sha256((H/'scripts/block_bounds.py').read_bytes()).hexdigest(),bank_sha256=hashlib.sha256(raw).hexdigest(),script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        completed_rows=rows,current_incomplete=current,unknown=unknown,witness=witness,static_examples=static_examples,
        scope='Specified global endpoint addition after one same-length contiguous replacement. All old blockers must be removed. Nonanchor degree peeling, component/distance and colour counts are necessary pruning. Terminal block restriction and sum of block colour bounds, including the adjacent-anchor bound1, are also necessary. Per-query node limits give UNKNOWN, never exclusions.')
    dest.write_text(json.dumps(out,indent=2)+'\n')

candidates=[]
for index,entry in enumerate(bank):
    p=entry['vertex_sequence'];assert valid(p)
    for end in [0,191]:
        for k in range(9):
            w=p[end]^(1<<k)
            blocked=[i for i,z in enumerate(p) if i!=end and (z==w or z in N[w])]
            assert blocked
            if 0 not in blocked and 191 not in blocked:
                candidates.append((index,end,k,w,min(blocked),max(blocked)))
try:
    for length in range(a.first,a.last+1):
        current=dict(length=length,candidates_complete=0,queries=0,rejections=collections.Counter(),unknown=0,search_nodes=0)
        for ci,(index,end,k,w,lo,hi) in enumerate(candidates):
            p=bank[index]['vertex_sequence']
            for i in range(max(0,hi-length+1),min(lo-1,191-length)+1):
                if time.monotonic()-started>a.seconds:raise Stop()
                j=i+length;u=p[i];v=p[j]
                info=dict(length=length,seed=index,endpoint=end,direction=k,start=i,end=j)
                current['active_query']=info
                current['queries']+=1
                retained=p[:i+1]+p[j:]
                forbidden=(1<<w)|NM[w]
                for z in retained:
                    forbidden|=1<<z
                    if z!=u and z!=v:forbidden|=NM[z]
                free=(ALL&~forbidden)|(1<<u)|(1<<v)
                free,removed=peel(free,u,v)
                comp,dist=component(free,u)
                reason=None
                if not comp&(1<<v):reason='DISCONNECTED'
                elif dist[v]>length:reason='DISTANCE'
                elif comp.bit_count()<length+1:reason='SIZE'
                else:
                    startcolour=comp& (EVEN if u.bit_count()%2==0 else ALL^EVEN)
                    if startcolour.bit_count()<(length+2)//2 or (comp^startcolour).bit_count()<(length+1)//2:reason='COLOUR'
                if reason:
                    current['rejections'][reason]+=1
                    if reason not in static_examples:static_examples[reason]=dict(query=info,free_vertices=list(bits(free)),peeling_order=removed,component=list(bits(comp)))
                    continue
                blocks=terminal_blocks(comp,u,v,NM)
                if blocks['upper_edges']<length:
                    current['rejections']['BLOCK_BOUND']+=1
                    if 'BLOCK_BOUND' not in static_examples:static_examples['BLOCK_BOUND']=dict(query=info,block_bound=blocks['upper_edges'],blocks=blocks['blocks'])
                    continue
                comp=blocks['mask']
                route=[u];local_nodes=0
                def dfs(left,blockedmask):
                    global nodes,local_nodes,witness
                    nodes+=1;local_nodes+=1
                    if local_nodes>a.nodes_per_query:raise QueryLimit()
                    if nodes%4096==0:
                        if time.monotonic()-started>a.seconds:raise Stop()
                    last=route[-1];d=(last^v).bit_count()
                    if d>left or (left-d)%2:return False
                    if left==1:
                        if v not in N[last] or blockedmask&(1<<v):return False
                        q=p[:i+1]+route[1:]+p[j:]
                        full=([w]+q) if end==0 else (q+[w])
                        assert len(full)==193 and valid(full)
                        witness=dict(query=info,path=full,old_path=p,replacement=route+[v])
                        return True
                    available=NM[last]&comp&~blockedmask&~(1<<v)
                    for z in bits(available):
                        route.append(z)
                        if dfs(left-1,blockedmask|NM[last]|(1<<last)):return True
                        route.pop()
                    return False
                try:
                    if dfs(length,0):raise Stop()
                    current['rejections']['EXHAUSTIVE_DFS']+=1
                except QueryLimit:
                    current['unknown']+=1;unknown.append(dict(query=info,nodes=local_nodes))
                current['search_nodes']+=local_nodes
            current['candidates_complete']=ci+1
        current.pop('active_query',None);rows.append(current);current=None
        print(json.dumps(rows[-1]),flush=True);save('CHECKPOINT')
    save('COMPLETE')
except Stop:
    save('LONGER_WITNESS_FOUND' if witness else 'TIME_LIMIT')
print(json.dumps(dict(file=str(dest),seconds=time.monotonic()-started,completed_lengths=[r['length'] for r in rows],unknown=len(unknown),witness=bool(witness),nodes=nodes)),flush=True)
