import json
from verify import D,permitted,hamilton
from core_moves import possible
def read(n):return list(map(json.loads,(D/n).read_text().splitlines()))
def main():
    sources=[set(map(int,l.split()[1:])) for l in (D/'resolved.sets').read_text().splitlines()]
    jobs=read('core_jobs.jsonl');concrete=read('core_concrete.jsonl');seen=set();original_seen={tuple(sorted(A)) for A in sources}
    for job in jobs:
        A=sources[job['index']];G=permitted(A);core=job['core']
        assert not possible(G,core) and possible(G,core,job['edges'])
    for idx,vec in concrete:
        r=jobs[idx];c=r['c'];A=sources[r['index']];B=set(vec);assert len(B)==97 and len(A-B)==c['k']
        G=permitted(B);assert possible(G,r['core']) and all(y in G[x] for x,y in r['edges'])
        key=tuple(sorted(B))
        if key not in seen:
            sat,cut=hamilton(G)
            if sat:raise RuntimeError(('POTENTIAL_192',key))
            seen.add(key)
    (D/'core_repaired.sets').write_text(''.join('97 '+' '.join(map(str,key))+'\n' for key in sorted(seen)))
    print(json.dumps(dict(families=len(jobs),constructed=len(concrete),distinct=len(seen),hamilton_unsat=len(seen),different_from_source_roots=len(seen-original_seen))))
if __name__=='__main__':main()
