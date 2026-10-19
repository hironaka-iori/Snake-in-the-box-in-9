"""Record the available endpoint extensions with the path and five cycles retained."""
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
HERE=Path(__file__).resolve().parents[1]


def main():
    run=json.loads((HERE/'data/one.json').read_text())
    seed=json.loads((ROOT/run['source']).read_text())
    path=seed['path_vertices'];ps=set(path);frozen=set(run['frozen_vertices'])
    ends=[path[0],path[-1]];internal=ps-set(ends)
    blocked=frozen|{v^(1<<k)for v in frozen|internal for k in range(9)}
    available=set(range(512))-blocked-ps
    starts={u:sorted(v for v in available if (u^v).bit_count()==1 and
                    sum((v^w).bit_count()==1 for w in path)==1)for u in ends}
    reachable=set();todo=[v for values in starts.values()for v in values]
    while todo:
        v=todo.pop()
        if v in reachable:continue
        reachable.add(v);todo.extend(v^(1<<k)for k in range(9)if v^(1<<k)in available)
    assert starts=={0:[2],120:[]} and reachable=={2}
    excluded=frozen|{v^(1<<k)for v in frozen for k in range(9)}
    blockers=[]
    for u in ends:
        for k in range(9):
            v=u^(1<<k)
            if v in excluded or v in ps:continue
            blockers.append({'endpoint':u,'candidate':v,'other_path_neighbors':[w for w in path if w!=u and(v^w).bit_count()==1]})
    out={'status':'CHECKED','path_edges':40,'frozen_vertices':sorted(frozen),
        'endpoints':ends,'available_vertices':sorted(available),'first_extensions':starts,
        'relaxed_reachable_additions':sorted(reachable),'additional_vertices_needed':26,
        'blockers':blockers,'scope':'Finite diagnostic with this path and these five cycles retained; not a global bound or Lean certificate.'}
    (HERE/'data/endpoint-diagnostic.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({'first_extensions':starts,'reachable_additions':sorted(reachable)}))


if __name__=='__main__':main()
