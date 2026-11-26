"""Enumerate every extension at the two free Q9 endpoints of the longest starting constructions."""
from collections import Counter
from search_partners import HERE,R271,cases,hunt,read,write
from exchange import input_paths

def main():
    roots=cases();extra=read(HERE/"additional-witnesses.json")
    best=read(HERE/"summary.json")["maximum_constructed"]
    seeds={}
    for k,r in roots.items():
        for q in [r["best"]["joined"],*extra.get(k,{}).values()]:
            if len(q)-1>=max(180,best-3):
                seeds.setdefault(tuple(q),k)
    out={}
    for seed,k in seeds.items():
        occupied=set(seed);paths=Counter();max_path=list(seed);attains=0
        def extend(q,at_left):
            nonlocal max_path,attains
            if len(q)>=193:
                write(HERE/"candidate-192.json",dict(root=k,ordered=q,starting_path=seed))
                assert hunt.original_audit.path_edges(q,9)==len(q)-1
                if len(q)>len(max_path):max_path=q;attains=1
                elif len(q)==len(max_path):attains+=1
                paths[len(q)-1]+=1
                return
            if at_left:extend(q,False)
            else:
                paths[len(q)-1]+=1
                if len(q)>len(max_path):max_path=q;attains=1
                elif len(q)==len(max_path):attains+=1
            tip=q[0] if at_left else q[-1]
            for axis in range(9):
                u=tip^(1<<axis)
                if u in occupied or any((u^(1<<i)) in occupied and (u^(1<<i))!=tip for i in range(9)):continue
                occupied.add(u)
                extend([u]+q if at_left else q+[u],at_left)
                occupied.remove(u)
        extend(list(seed),True)
        assert hunt.original_audit.path_edges(max_path,9)==len(max_path)-1
        loc=next(j for j in range(len(max_path)-len(seed)+1) if max_path[j:j+len(seed)]==list(seed))
        sig=hunt.original_audit.shape(seed).hex()
        out.setdefault(sig,[]).append(dict(root=k,starting_edges=len(seed)-1,growth=paths,max_edges=len(max_path)-1,
                                       longest_examples=attains,left_added=loc,joined=max_path))
    joined=[q for rows in out.values() for q in rows]
    top=max((r["max_edges"] for r in joined),default=0)
    candidates={hunt.original_audit.shape(r["joined"]).hex():[] for r in joined if r["max_edges"]==top}
    records=[(f"271/{k}/{t}",p) for k,rows in read(R271/"additional-witnesses.json").items() for t,p in rows.items()]
    for label,p in list(input_paths())+records:
        for offset in range(len(p)-top):
            sig=hunt.original_audit.shape(p[offset:offset+top+1]).hex()
            if sig in candidates:candidates[sig].append([label,offset])
    write(HERE/"endpoint-growth.json",dict(archive_matches=candidates,seeds=len(seeds),minimum_seed_edges=max(180,best-3),by_shape=out,
          longest=max((r["max_edges"] for rows in out.values() for r in rows),default=0)))
    print("Seed constructions",len(seeds),"longest",max((r["max_edges"] for rows in out.values() for r in rows),default=0),flush=True)

if __name__=="__main__":main()
