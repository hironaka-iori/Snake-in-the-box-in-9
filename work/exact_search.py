"""Exact induced-path feasibility model. UNKNOWN never means infeasible."""
import sys, json, time, argparse
from pathlib import Path
sys.path.insert(0, str(Path('work/solver_packages').resolve()))
from ortools.sat.python import cp_model

def model(n, edges, fixed_vertices=None, hint=None, symmetry=True):
    size = 1 << n
    m = cp_model.CpModel()
    x = [m.new_bool_var(f'x{v}') for v in range(size)]
    arcs = [(v, v, x[v].Not()) for v in range(size)]
    edge_arcs = {}
    crossings = [[] for _ in range(n)]
    for u in range(size):
        for k in range(n):
            v = u ^ (1 << k)
            if u < v:
                uv, vu = m.new_bool_var(f'a{u}_{v}'), m.new_bool_var(f'a{v}_{u}')
                arcs.extend([(u,v,uv),(v,u,vu)])
                edge_arcs[u,v] = uv
                edge_arcs[v,u] = vu
                m.add(uv + vu >= x[u] + x[v] - 1)
                crossings[k].extend([uv, vu])
    # Dummy vertex turns the desired path into one circuit. Self-loops exclude vertices.
    start = m.new_bool_var('start')
    m.add(start == 1)
    arcs.append((size, 0, start))
    ends = []
    for v in range(1, size):
        end = m.new_bool_var(f'end{v}')
        arcs.append((v,size,end))
        ends.append(end)
        m.add(sum(x[v ^ (1 << k)] for k in range(n)) == 2 - end).only_enforce_if(x[v])
    m.add(sum(x[1 << k] for k in range(n)) == 1)
    m.add_circuit(arcs)
    m.add(sum(x) == edges + 1)
    m.add(sum(x[v] for v in range(size) if v.bit_count()%2 == 0) == edges//2 + 1)
    m.add(sum(x[v] for v in range(size) if v.bit_count()%2 == 1) == (edges+1)//2)
    if symmetry and edges >= 2:
        m.add(edge_arcs[0,1] == 1)
        m.add(edge_arcs[1,3] == 1)
        for k in range(2,n-1):
            m.add(sum(crossings[k]) >= sum(crossings[k+1]))
    if fixed_vertices is not None:
        for v in fixed_vertices:
            m.add(x[v] == 1)
    if hint is not None:
        occupied = set(hint)
        for v in range(size):
            m.add_hint(x[v], int(v in occupied))
    return m,x,edge_arcs

def solve(n, edges, seconds, fixed_vertices=None, hint=None, symmetry=True):
    m,x,arcs = model(n,edges,fixed_vertices,hint,symmetry)
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = seconds
    solver.parameters.num_search_workers = 4
    solver.parameters.random_seed = 13
    started = time.monotonic()
    status = solver.solve(m)
    report = {'dimension':n, 'target_edges':edges, 'status':solver.status_name(status),
              'elapsed_seconds':time.monotonic()-started,
              'branches':solver.num_branches,'conflicts':solver.num_conflicts,
              'fixed_vertices':len(fixed_vertices) if fixed_vertices is not None else 0}
    if status in (cp_model.OPTIMAL,cp_model.FEASIBLE):
        vertices = [0]
        while True:
            nxt = [v for (u,v),a in arcs.items() if u == vertices[-1] and solver.value(a)]
            if not nxt:
                break
            vertices.append(nxt[0])
        from check_snake import verify
        actions = [(u^v).bit_length()-1 for u,v in zip(vertices,vertices[1:])]
        validation = verify(actions,n)
        assert validation['edges'] == edges
        assert vertices == validation['vertex_sequence']
        report['vertices'] = vertices
    return report

if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--seconds', type=float, default=120)
    p.add_argument('--n',type=int,default=9)
    p.add_argument('--edges',type=int,default=192)
    p.add_argument('--output',default='outputs/exact_search.json')
    args = p.parse_args()
    result = solve(args.n,args.edges,args.seconds)
    Path(args.output).write_text(json.dumps(result,indent=2),encoding='utf-8')
    print(json.dumps(result,indent=2),flush=True)
