"""Test a fixed published 98-edge Q8 snake as one layer of a Q9 lift."""
import json, re, time, argparse
from pathlib import Path
from itertools import permutations
from check_snake import verify

def seed():
    if Path('work/minortriad.html').exists():
        html = Path('work/minortriad.html').read_text(encoding='utf-8')
        text = re.search(r'id:"sn8".*?ts:\s*"([\s\S]*?)"', html).group(1)
        actions = [int(c) for c in text if c.isdigit()]
    else:
        actions = json.loads(Path('outputs/snake8_witness.json').read_text())['transition_sequence']
    result = verify(actions, 8)
    assert result['edges'] == 98
    result['source'] = 'https://www.minortriad.com/snake/'
    result['attribution'] = 'Carlson and Hougen (2010), as listed by source'
    Path('outputs/snake8_witness.json').write_text(json.dumps(result, indent=2))
    return result['vertex_sequence']

def orbit_test(vertices):
    started = time.monotonic()
    lefts = [[v ^ root for v in vertices] for root in [vertices[0], vertices[-1]]]
    rights = []
    for p in [vertices[1:],vertices[:-1]]:
        for root in [p[0],p[-1]]:
            rights.append([v ^ root for v in p])
    leftsets = [set(p) for p in lefts]
    best = 257
    tested = 0
    for perm in permutations(range(8)):
        mapping = [0]*256
        for v in range(1,256):
            bit = v & -v
            mapping[v] = mapping[v^bit] | (1 << perm[bit.bit_length()-1])
        for p in rights:
            image = set(mapping[v] for v in p)
            for a in leftsets:
                overlap = len(a & image)
                best = min(best,overlap)
                tested += 1
    return {'candidate_placements':tested,'minimum_shared_vertices':best,
            'required_shared_vertices':1,'elapsed_seconds':time.monotonic()-started,
            'scope':'One fixed 98-edge snake and a 97-edge endpoint truncation of an isometric copy of the same snake; all endpoint joins and coordinate permutations.'}

def solve_complement(vertices,seconds,target=97):
    from exact_search import model,cp_model
    reports = []
    for root in [vertices[0],vertices[-1]]:
        forbidden = {v ^ root for v in vertices} - {0}
        m,x,arcs = model(8,target,symmetry=False)
        for v in forbidden:
            m.add(x[v] == 0)
        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = seconds
        solver.parameters.num_search_workers = 4
        solver.parameters.random_seed = 13
        start = time.monotonic()
        status = solver.solve(m)
        report = {'root':root,'target_partner_edges':target,'status':solver.status_name(status),
                  'elapsed_seconds':time.monotonic()-start,
                  'branches':solver.num_branches,'conflicts':solver.num_conflicts}
        if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            path = [0]
            while True:
                nxt = [v for (u,v),a in arcs.items() if u==path[-1] and solver.value(a)]
                if not nxt: break
                path.append(nxt[0])
            a = [v ^ root for v in vertices]
            if a[-1] != 0: a.reverse()
            joined = a + [v+256 for v in path]
            transitions = [(u^v).bit_length()-1 for u,v in zip(joined,joined[1:])]
            report['witness'] = verify(transitions,9)
            assert report['witness']['edges'] == 99+target
        reports.append(report)
        print(json.dumps(report),flush=True)
    return reports

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--seconds',type=float,default=60)
    args=parser.parse_args()
    vertices=seed()
    report={'orbit':orbit_test(vertices)}
    print(json.dumps(report),flush=True)
    report['complement_search']=solve_complement(vertices,args.seconds)
    report['limitation']='Restricted to the published Q8 seed. Computations are not Lean certificates.'
    Path('outputs/layer_search.json').write_text(json.dumps(report,indent=2))
