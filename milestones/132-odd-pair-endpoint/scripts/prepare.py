"""Prepare a necessary full-cube counterexample input; never run a solver."""
from pathlib import Path
from itertools import combinations
import ast, hashlib, importlib.util, json, sys

H = Path(__file__).resolve().parents[1]
R = H.parents[1]
sys.dont_write_bytecode = True
sys.path[:0] = [str(R/'milestones/10-window-aggregate/scripts'),str(R/'work/share_packages'),str(R/'work/solver_packages')]
from gen_lean_sat import TaggedEncoding
from wincert import Encoding

sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
def write_json(p,obj):
    with p.open('x',encoding='utf-8') as f:
        json.dump(obj,f,indent=2)
        f.write('\n')

def main():
    for name in ['data','work']:
        (H/name).mkdir(parents=True,exist_ok=True)
    targets = [H/'work/base.cnf',H/'data/encoding.json',H/'data/preparation.json']
    assert not any(p.exists() for p in targets), 'Preserve existing prepared input'
    window = [0,1,3,7,6,14,10]
    bounds = [[0,21] for _ in range(5)]
    enc = TaggedEncoding(window,bounds,radius=9)
    reference = Encoding(window,[tuple(b) for b in bounds],radius=9)
    assert enc.clauses == reference.clauses and enc.nv == reference.nv
    assert enc.ball == list(range(512)) and enc.ends == 2
    assert all(enc.var[v] == v+1 and enc.meaning[513+v] == ('e',v) for v in range(512))
    base_variables, base_clauses = enc.nv, len(enc.clauses)
    centres = [window[2],window[4]]
    corner_lists = []
    for k in [2,4]:
        used = {(window[k]^window[k-1]).bit_length()-1,(window[k]^window[k+1]).bit_length()-1}
        corners = [window[k]^(1<<a)^(1<<b) for a,b in combinations(range(9),2) if a not in used and b not in used]
        assert len(corners) == len(set(corners)) == 21
        corner_lists.append(corners)
    # Concatenate occurrences. Shared corners deliberately remain repeated.
    literals = [-enc.var[v] for corners in corner_lists for v in corners]
    assert len(literals) == 42
    pair_start = len(enc.clauses)
    enc.atmost(literals,9,('pair_counterexample_cap',))
    pair_end = len(enc.clauses)
    even = [513+v for v in range(512) if v.bit_count()%2 == 0]
    odd = [513+v for v in range(512) if v.bit_count()%2 == 1]
    assert len(even) == len(odd) == 256 and set(even).isdisjoint(odd)
    enc.add(even,('one_even_endpoint',))
    enc.add(odd,('one_odd_endpoint',))
    common = [v for v in range(512) if all((v^c).bit_count() == 2 for c in centres)]
    assert centres == [3,6] and len(common) == 14
    for v in common:
        enc.add([-(513+v)],('endpoint_not_common_two',v))
    assert len(enc.clauses) == pair_end+16
    assert len(enc.ctrs) == 2, 'Only the base endpoint counter and pair-cap counter are allowed'
    assert enc.ctrs[1][0] == literals and enc.ctrs[1][1] == 9
    raw = (f'p cnf {enc.nv} {len(enc.clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in enc.clauses)).encode('ascii')
    with targets[0].open('xb') as f:
        f.write(raw)
    sources = [Path(__file__),H/'scripts/probe.py',R/'milestones/10-window-aggregate/scripts/gen_lean_sat.py',
               R/'milestones/10-window-aggregate/scripts/wincert.py']
    for name in ['pysat.solvers','pysolvers']:
        spec = importlib.util.find_spec(name)
        assert spec is not None and spec.origin
        sources.append(Path(spec.origin))
    pins = {p.relative_to(R).as_posix():sha(p) for p in sources}
    metadata = dict(window=window,directions=[0,1,2,0,3,2],bounds=bounds,radius=9,
        centres=centres,corner_lists=corner_lists,pair_literals=literals,pair_cap=9,
        occurrence_count=len(literals),unique_literal_count=len(set(literals)),
        pair_counter_index=1,pair_clause_interval_zero_based=[pair_start,pair_end],
        base_variables=base_variables,base_clauses=base_clauses,variables=enc.nv,clauses=len(enc.clauses),
        even_endpoint_clause=even,odd_endpoint_clause=odd,forbidden_common_sphere=common,
        variable_meaning=enc.meaning,counters=enc.ctrs,cnf_sha256=hashlib.sha256(raw).hexdigest(),
        source_files_sha256=pins,additional_cycle_cuts=[],
        clause_scope='Unmodified full-cube TaggedEncoding with five[0,21] bounds, plus pair cap, two parity clauses and14 endpoint units. Standard base4/6-cycle clauses are inherited from TaggedEncoding; no prior experimental cuts or other candidate bounds are added.')
    write_json(targets[1],metadata)
    for p in [Path(__file__),H/'scripts/probe.py']:
        ast.parse(p.read_text(encoding='utf-8'))
    preparation = dict(status='PREPARED_SEARCH_NOT_RUN',cnf=targets[0].relative_to(R).as_posix(),
        cnf_sha256=sha(targets[0]),encoding_sha256=sha(targets[1]),source_files_sha256=pins,
        variables=enc.nv,clauses=len(enc.clauses),pair_occurrences=42,pair_unique_literals=len(set(literals)),
        common_sphere=common,full_cube=True,plain_and_tagged_base_equal=True,syntax_checked=True,
        solver_started=False,lean_started=False,nominal_solver_seconds=45,hard_parent_timeout_seconds=90,
        conflicts_per_call=1000,minimum_free_bytes=1610612736,
        hypothesis='For odd edge length, a fitting012032 window with pair count9 has some one endpoint at distance2 from both centres.',
        necessity='An actual odd-length counterexample selects its path and actual endpoints. Its endpoints have opposite parity, so the two positive endpoint clauses hold. The14 forbidden flags express failure of the same-endpoint conclusion. The pair cap includes equality9 and weaker smaller values. Multiplicity counts the two centres separately.',
        limitations='Input necessity is explained and mechanically inspected, not Lean checked here. SAT requires independent path validation; native UNSAT is uncertified; timeout or UNKNOWN gives no exclusion.')
    write_json(targets[2],preparation)
    print(json.dumps({k:v for k,v in preparation.items() if k!='source_files_sha256'},indent=2))

if __name__ == '__main__':
    main()
