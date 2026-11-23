from itertools import combinations,product
import json,sys,collections
from pysat.solvers import Minicard
def sw(x,t):
    for j in range(0,2*t,2):
        if ((x>>j)^(x>>(j+1)))&1:x^=3<<j
    return x
def ok(p):return len(p)==len(set(p)) and all(((x^y).bit_count()==1)==(j==i+1) for i,x in enumerate(p) for j,y in enumerate(p[i+1:],i+1))
def solve(wing1,wing2,mid,t,wanted,budget):
    mirrors=lambda x:sw(x,t-1)
    orbit=lambda x:min(x,mirrors(x))
    sets=[{orbit(v>>2) for v in z} for z in (wing1,wing2)]
    ports=[orbit(wing1[-1]>>2),orbit(wing2[0]>>2)]
    if ports[0] in sets[1] or ports[1] in sets[0]:return 'UNSAT',None
    candidates={x for x in range(1,128) if orbit(x) not in sets[0]|sets[1]}
    goal=wanted-len(wing1)-len(wing2)
    pending=False
    for a,b in product((ports[0],mirrors(ports[0])),(ports[1],mirrors(ports[1]))):
        free=candidates|{a,b}
        if 0 in free or a==b:continue
        adj={x:{x^1<<j for j in range(7)}&free for x in free}
        # Delete disconnected vertices and forget isolated endpoints.
        comp={a};q=[a]
        for v in q:
            for y in adj[v]-comp:comp.add(y);q.append(y)
        if b not in comp or len(comp)<goal:continue
        free=comp
        with Minicard() as s:
            s.add_clause([a+1]);s.add_clause([b+1]);s.add_atmost([-(x+1) for x in free],len(free)-goal)
            for x in free:
                nn=[j+1 for j in adj[x]]
                k=1 if x in (a,b) else 2
                if len(nn)<k:s.add_clause([-x-1]);continue
                for vec in combinations(nn,k+1):s.add_clause([-x-1,*[-y for y in vec]])
                for vec in combinations(nn,len(nn)-k+1):s.add_clause([-x-1,*vec])
            s.set_phases([x+1 if x in mid else -x-1 for x in free])
            while True:
                remain=budget-s.accum_stats()['conflicts']
                if remain<=0:pending=True;break
                s.conf_budget(remain);sat=s.solve_limited()
                if sat is not True:pending|=sat is None;break
                model=set(s.get_model());used={v for v in free if v+1 in model}
                path=[a];seen={a}
                while path[-1]!=b:
                    nxt,=adj[path[-1]]&(used-seen);seen.add(nxt);path.append(nxt)
                if len(path)>=goal:
                    arm=[0]
                    for u in [*wing1,*[1+(x<<2) for x in path],*wing2]:
                        if (arm[-1]^u).bit_count()!=1:u=sw(u,t)
                        arm.append(u)
                    full=[sw(x,t) for x in arm[:0:-1]]+arm
                    assert ok(full)
                    return 'FOUND',full
                unused=used-seen
                while unused:
                    start=next(iter(unused));cycle=[start];unused.remove(start)
                    for x in cycle:
                        fresh=adj[x]&unused;unused-=fresh;cycle.extend(fresh)
                    vset=set(cycle);border=set().union(*(adj[x] for x in cycle))-vset
                    s.add_clause([-start-1,*[x+1 for x in border]])
    return ('UNKNOWN' if pending else 'UNSAT'),None
def main():
    t=int(sys.argv[1]);sources=sys.argv[2:];cache=set();stats=collections.Counter()
    for fn in sources:
        for row in open(fn):
            ws=row.split();length=int(ws[1]);i,m,o=map(int,ws[5:8])
            if length<164:continue
            full=list(map(int,ws[9:]));assert ok(full);half=full[len(full)//2+1:];assert len(half)==i+m+o
            for d,e in product(range(5),repeat=2):
                left=half[:i-d];right=half[i+m+e:]
                if not left or not right:continue
                mid=half[i:i+m];mid=[(x if x%4==1 else sw(x,t))>>2 for x in mid]
                for goal in ([96,length//2] if d==e==0 else [96]):
                    key=(tuple(left),tuple(right),goal)
                    if key in cache:continue
                    cache.add(key)
                    status,witness=solve(left,right,mid,t,goal,3000)
                    stats[goal==96,status]+=1
                    if witness:print(json.dumps(dict(t=t,base=length,want=2*goal,len=len(witness)-1,trim=[d,e],path=witness)),flush=True)
    print(stats,file=sys.stderr)
if __name__=='__main__':main()
