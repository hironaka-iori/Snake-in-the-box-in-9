"""Find disjoint 26-vertex degree-two sets in Q6, then lift and trim to 197 vertices."""
import itertools
import json
from pathlib import Path
import sys
ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT/'work'))
from exact_search import cp_model
from component_search import components


def run():
    m = cp_model.CpModel()
    xs = [[m.new_bool_var(f'x{b}_{v}') for v in range(64)] for b in range(2)]
    for row in xs:
        m.add(sum(row)==26)
        for v in range(64):
            m.add(sum(row[v^(1<<k)] for k in range(6))==2).only_enforce_if(row[v])
        for a,b in itertools.combinations(range(6),2):
            for v in range(64):
                if v & ((1<<a)|(1<<b)) == 0:
                    m.add(sum(row[w] for w in (v,v^(1<<a),v^(1<<b),v^(1<<a)^(1<<b)))<=3)
    for v in range(64):
        m.add(xs[0][v]+xs[1][v]<=1)
    m.add(xs[0][0]==1)
    m.add(xs[0][1]==1)
    m.add(xs[0][2]==1)
    s=cp_model.CpSolver()
    s.parameters.max_time_in_seconds=60
    s.parameters.num_search_workers=2
    s.parameters.random_seed=196
    status=s.solve(m)
    result={'base_dimension':6,'vertices_per_base':26,'status':s.status_name(status),
            'seconds':s.wall_time,'branches':s.num_branches,'conflicts':s.num_conflicts}
    if status in (cp_model.OPTIMAL,cp_model.FEASIBLE):
        bases=[[v for v in range(64) if s.value(row[v])] for row in xs]
        assert not set(bases[0]) & set(bases[1])
        for base in bases:
            parts,adj=components(base,6)
            assert len(base)==26 and all(len(adj[v])==2 for v in base)
        product=[(layer<<6)|v for layer in range(8) for v in bases[layer.bit_count()%2]]
        parts,adj=components(product,9)
        assert len(product)==208 and all(len(adj[v])==2 for v in product)
        result.update(base_sets=bases,product_vertices=sorted(product),product_components=parts)
        # Drop complete cycles and one proper consecutive segment, totaling eleven vertices.
        for k,c in enumerate(parts):
            order=[c[0],adj[c[0]][0]]
            while len(order)<len(c):
                order.append(next(v for v in adj[order[-1]] if v!=order[-2]))
            assert len(set(order))==len(c) and order[0] in adj[order[-1]]
            others=[d for j,d in enumerate(parts) if j!=k]
            choices={0:[]}
            for d in others:
                for count,whole in list(choices.items()):
                    if count+len(d)<=10:choices.setdefault(count+len(d),whole+[d])
            for count,whole in sorted(choices.items()):
                remove=11-count
                if 1<=remove<=len(c)-2:
                    deleted=set(order[:remove]) | {v for d in whole for v in d}
                    kept=set(product)-deleted
                    pieces,g=components(kept,9)
                    ends=[v for v in kept if len(g[v])==1]
                    assert len(kept)==197 and len(ends)==2 and all(len(g[v]) in (1,2) for v in kept)
                    # Normalize a path endpoint to zero and its neighbor to one.
                    origin=min(ends); direction=(origin^g[origin][0]).bit_length()-1
                    def normalize(v):
                        v^=origin
                        if ((v>>direction)^v)&1:
                            v^=(1<<direction)|1
                        return v
                    normalized=sorted(normalize(v) for v in kept)
                    result.update(seed_vertices=normalized,deleted_vertices=sorted(deleted),
                        seed_components=components(normalized,9)[0])
                    break
            if 'seed_vertices' in result:break
        if 'seed_vertices' not in result:result['trim_status']='NO_ELEVEN_VERTEX_TRIM_FOUND'
    out=ROOT/'milestones/14-component-construction/data/product-seed.json'
    out.parent.mkdir(parents=True,exist_ok=True)
    out.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({k:v for k,v in result.items() if k in ('status','seconds','trim_status')}),flush=True)


if __name__=='__main__':run()
