from certify import *
ranks=list(map(int,sys.argv[1:]))
rows={r['rank']:r for r in map(json.loads,(B/'pilot.jsonl').read_text().splitlines())}
for rank in ranks:
    r=rows[rank];F,x,ends=cnf(r,with_vars=True);tag='rank'+str(rank);cycles=[]
    budget=int(os.getenv('Q9_BUDGET','1200000'));total=0
    while True:
        with Solver(name='cadical195',bootstrap_with=F,with_proof=True) as s:
            s.conf_budget(max(1,budget-total));ans=s.solve_limited();total+=s.accum_stats()['conflicts']
            if ans is False:
                F.to_file(str(B/(tag+'.cnf')))
                (B/(tag+'.drat')).write_text('\n'.join(s.get_proof())+'\n')
                if cycles:(B/(tag+'.cycles')).write_text(json.dumps(cycles))
                r.update(result='CNF_UNSAT',conflicts=total,cuts=len(cycles));break
            if ans is None:
                r.update(result='UNKNOWN',conflicts=total,cuts=len(cycles));break
            model=set(s.get_model());chosen={v for v,a in x.items() if a in model};remain=set(chosen);parts=[]
            while remain:
                q=[remain.pop()]
                for v in q:
                    n={v^1<<i for i in range(9)}&remain;q.extend(n);remain-=n
                parts.append(q)
            if len(parts)==1:
                adj={v:{v^1<<i for i in range(9)}&chosen for v in chosen}
                p=[next(v for v in chosen if len(adj[v])==1)];rest=chosen-set(p)
                while rest:
                    v,=adj[p[-1]]&rest;p.append(v);rest.remove(v)
                assert len(chosen)==193 and all(((a^b).bit_count()==1)==(j-i==1) for i,a in enumerate(p) for j,b in enumerate(p) if i<j)
                r.update(result='FOUND',path=p,conflicts=total,cuts=len(cycles));break
            for part in parts:
                if all(len({v^1<<i for i in range(9)}&chosen)==2 for v in part):
                    F.append([-x[v] for v in part]);cycles.append(part)
    print(json.dumps(r),flush=True)
