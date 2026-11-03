"""Bounded saved-cycle audit; no solver, compiler, or full-edge inequality scan.

Adapted from115 independent_cycles.py, with independent full-key diagram and
endpoint/weight reconstruction from the pinned original models. Output is
printed by default; --output creates a new file and never overwrites evidence.
"""
from pathlib import Path
from fractions import Fraction
import argparse, ast, gzip, hashlib, json, re, subprocess, sys

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT/'work/solver_packages'))
import numpy as np

old_script = ROOT/'milestones/115-total-count-certificate/scripts/independent_cycles.py'
pins = {}
def pin(path):
    path = Path(path)
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    key = path.relative_to(ROOT).as_posix()
    assert key not in pins or pins[key] == digest
    pins[key] = digest
    return digest

def read(path):
    pin(path)
    return json.loads(Path(path).read_text(encoding='utf-8-sig'))

def literal(path, name):
    pin(path)
    text = path.read_text(encoding='utf-8-sig')
    match = re.search(r'\bdef '+re.escape(name)+r'\b[^=]*:=\s*', text)
    assert match
    start = match.end()
    start += text[start] == '#'
    assert text[start] == '['
    depth = 0
    for end in range(start, len(text)):
        depth += (text[end] == '[') - (text[end] == ']')
        if depth == 0:
            return ast.literal_eval(text[start:end+1].replace('#[','['))
    raise AssertionError(name)

def canon(word):
    names = {}
    return tuple(names.setdefault(int(x), len(names)) for x in word)

def shape(word):
    return min(canon(word), canon(word[::-1]))

def symbols(code):
    assert 0 <= code < 46656
    return [code//6**j % 6 + 1 for j in range(5,-1,-1)]

dsmodel = read(ROOT/'milestones/59-extended-share-window/extended/data/model.json')
ds = dsmodel['extensions']
assert ds == literal(ROOT/'milestones/77-direction-state-coverage/lean/DirectionTables.lean','extensions')
shape_index = {tuple(w): i for i,w in enumerate(dsmodel['direction_shapes'])}
geometry = read(ROOT/'milestones/59-extended-share-window/data/geometry.json')['patterns']
history = read(ROOT/'milestones/67-critical-family-charge/data/full-model.json')
prefixes = history['prefixes']
dagpath = ROOT/'milestones/87-retained-array-membership/data/coverage-membership-dag.json.gz'
pin(dagpath)
dag = json.loads(gzip.decompress(dagpath.read_bytes()))
assert dag['nodes'] == literal(ROOT/'milestones/88-retention-diagram-certificate/lean/GraphData.lean','retainedDiagram')
assert dag['roots'] == literal(ROOT/'milestones/92-full-witness-batch/lean/BatchContextData.lean','recordedClassRoots')
assert list(map(tuple,dag['blocks'])) == literal(ROOT/'milestones/92-full-witness-batch/lean/ContextAssignmentData.lean','savedBlockClasses')
blocks = dict(dag['blocks'])

def accepted(di, q, digits):
    assert 0 <= di < 505 and 0 <= q < 75
    cls = blocks[75*di+q]
    node = dag['roots'][cls]
    route = [node]
    for remaining,symbol in zip(range(6,0,-1),digits):
        if node not in (0,1):
            row = dag['nodes'][node-2]
            assert len(row) == 7 and row[0] == remaining
            node = row[symbol]
        route.append(node)
    assert node == 1
    return dict(cls=cls,route=route)

forward = [([0,1,2,3,1,4],[3,3,3,6,5],48),
           ([0,1,2,3,4,5],[3,6,2,3,6],96),
           ([0,1,2,0,3,4],[6,3,6,3,3],96),
           ([0,1,2,3,4,5],[4,6,2,3,6],96)]
conditioned = forward + [(list(canon(w[::-1])),c[::-1],v) for w,c,v in forward]

def original_semantics(di,q,code):
    word,counts = ds[di],symbols(code)
    assert geometry[di]['directions'] == word
    credits = [geometry[di]['share_lower']]
    for w,c,v in conditioned:
        if canon(word[-6:]) == tuple(w) and counts[1:] == c:
            credits.append(v)
    emitted = prefixes[q]+[di]
    for rule in history['patterns']:
        if len(emitted) >= 3 and emitted[-3:] == rule['signature']:
            hit = all(counts[int(j)] <= cap for j,cap in rule['caps'].items())
            if rule['mode'] == 'exclusion':
                assert not hit
            else:
                credits.append(rule['geometric_lower'])
                if hit:
                    credits.append(rule['lower'])
    if len(set(word[-6:])) == 6 and counts[1:] in ([4,5,4,2,6],[6,2,4,5,4]):
        credits.append(120)
    options = [j for j,pref in enumerate(prefixes) if pref and len(pref)<=len(emitted) and emitted[-len(pref):]==pref]
    target_q = max(options,key=lambda j:len(prefixes[j])) if options else 0
    source_shape,target_shape = shape_index[canon(word[:8])],shape_index[canon(word[1:])]
    assert q == 0 or history['compatible_shapes'][q] == source_shape
    assert target_q == 0 or history['compatible_shapes'][target_q] == target_shape
    def state(sh,h,c):
        return sh*7776+c if h == 0 else 1026432+(h-1)*7776+c
    return 120*counts[-1]+max(credits),state(source_shape,q,code//6),state(target_shape,target_q,code%7776)

graphbase = ROOT/'milestones/72-four-count-proof-closure/critical-current'
meta = read(graphbase/'data/source-proved-model.json')
pin(graphbase/'build/source-graph.npz')
with np.load(graphbase/'build/source-graph.npz') as archive:
    graph = {k:archive[k] for k in archive.files}
assert {k:hashlib.sha256(v.tobytes()).hexdigest() for k,v in graph.items()} == meta['arrays_sha256']
completed = read(ROOT/'milestones/73-countfree-share-catalogue/data/proved-model.json')
cf = {tuple(x['shape']):x['share'] for x in completed['countfree_floors']}
ff = cf | {(0,1,2,0,3,2):16,(0,1,2,0,3,4):18,(0,1,2,3,0,1):16,(0,1,2,3,4,0):16,(0,1,2,3,4,5):16}
prior = set(read(ROOT/'milestones/111-critical-count-intervals/data/middle325-profiles/removed-indices.json'))
previous = set(read(ROOT/'milestones/113-all-four-sum-pressure/data/pair24/removed-indices.json'))
algorithm = subprocess.check_output(['git','show','41797e3863e17be730f06e3a9c5df09bbc0d404d:milestones/10-window-aggregate/scripts/refine.py'],cwd=ROOT).decode().replace('\r\n','\n')
algorithm_sha = hashlib.sha256(algorithm.encode()).hexdigest()
experiments = []
removed_sets = {}
for label,script in [('universal345-total21','evaluate_total.py'),('universal345-total22','evaluate_total.py')]:
    folder = HERE/'data'/label
    data = read(folder/'results.json')
    assert data['script_sha256'] == pin(HERE/'scripts'/script)
    assert data['algorithm_sha256'] == algorithm_sha
    for path,digest in data['source_files_sha256'].items():
        assert pin(ROOT/path) == digest
    rules = data['rules']
    assert len(rules) == (11 if label == 'universal345-total21' else 10) and data['coefficients'] == [24]*5
    probes = []
    for rule in rules:
        probe = read(ROOT/rule['probe'])
        expected = 'UNSAT_UNCERTIFIED'
        assert probe['status'] == expected
        assert shape(probe['directions']) == shape(rule['directions'])
        assert probe['bounds'] == rule['bounds'] == rule['bounds'][::-1]
        assert rule['positions'] == sorted(4-j for j in rule['positions'])
        assert len(set(rule['positions'])) == len(rule['positions'])
        assert probe.get('cap',probe.get('outer_sum_cap')) == rule['lower']-1
        assert probe.get('positions',[0,1,3,4]) == rule['positions']
        probes.append(dict(name=rule['name'],status=expected,cycle_cuts=len(probe['cycle_cuts']),solver_seconds=probe.get('solver_seconds')))
    raw_removed = read(folder/'removed-indices.json')
    removed = set(raw_removed)
    removed_sets[label] = removed
    assert len(removed) == len(raw_removed) and all(0 <= k < len(graph['U']) for k in removed)
    assert prior <= removed and previous <= removed
    assert len(graph['U'])-len(removed) == data['edges']
    assert len(removed)-len(prior) == data['additional_removed']
    assert len(removed)-len(previous) == data['additional_to_previous_family']
    assert sum(e['marginal_removed'] for e in data['effects']) == data['additional_removed']
    profiles = []
    for profile in data['profiles']:
        potential_path = folder/profile['potential_file']
        pin(potential_path)
        raw = gzip.decompress(potential_path.read_bytes())
        assert hashlib.sha256(raw).hexdigest() == profile['potential_sha256']
        pi = np.frombuffer(raw,dtype='<i8')
        assert len(pi) == data['states'] == meta['states']
        assert int(pi.min()) == 0 and int(pi.max()) == profile['range_scaled']
        assert Fraction(profile['range']) == Fraction(profile['range_scaled'],profile['d'])
        cycle = profile['cycle']
        floors = cf if profile['profile'] == 'completed' else ff
        decoded = []
        for i,e in enumerate(cycle):
            k = e['edge']
            assert k not in removed and e['v'] == cycle[(i+1)%len(cycle)]['u']
            for key,array in [('u','U'),('v','V'),('direction','direction'),('history','history'),('count_code','count_code')]:
                assert e[key] == int(graph[array][k])
            vals = symbols(e['count_code'])
            membership = accepted(e['direction'],e['history'],vals)
            original,u,v = original_semantics(e['direction'],e['history'],e['count_code'])
            assert original == int(graph['weight'][k]) and u == e['u'] and v == e['v']
            placements = []
            for s in [0,1]:
                word = ds[e['direction']][s+2:s+8]
                counts = vals[s:s+5]
                reverse = canon(word[::-1]) < canon(word)
                evaluated = []
                for rule in rules:
                    applicable = shape(word) == shape(rule['directions']) and all(lo<=x and (21 if x==6 else x)<=hi for x,(lo,hi) in zip(counts,rule['bounds']))
                    deficit = max(0,rule['lower']-sum(counts[j] for j in rule['positions'])) if applicable else 0
                    assert deficit == 0
                    evaluated.append(dict(name=rule['name'],applicable=applicable,deficit=deficit,selected_clipped_sum=sum(counts[j] for j in rule['positions']),required_lower=rule['lower'],deletion=False if not applicable else deficit>0 and all(counts[j]<6 for j in rule['positions'])))
                normalized = counts[::-1] if reverse else counts
                placements.append(dict(offset=s,raw_directions=word,canonical_shape=list(shape(word)),reverse=reverse,counts=normalized,
                    count_intervals=[[x,21 if x==6 else x] for x in normalized],total_clipped=sum(counts),rules=evaluated))
            base = max(original,120*vals[-1]+floors.get(shape(ds[e['direction']][-6:]),0))
            assert e['bonus'] == 0 and e['weight'] == base
            slack = profile['d']*base+int(pi[u])-profile['p']-int(pi[v])
            assert slack == 0
            decoded.append(dict(edge=k,di=e['direction'],q=e['history'],code=e['count_code'],u=u,v=v,counts6=vals,weight=base,potential_slack=slack,membership=membership,placements=placements))
        mean = Fraction(sum(e['weight'] for e in cycle),len(cycle))
        comparison = Fraction(1098960*profile['d']+8*profile['p']+profile['range_scaled'],4200*profile['d']+profile['p'])
        assert mean == Fraction(profile['mean']) == Fraction(profile['p'],profile['d'])
        assert comparison == Fraction(profile['comparison_bound'])
        assert comparison.numerator//comparison.denominator == profile['comparison_integer_bound']
        profiles.append(dict(profile=profile['profile'],mean=str(mean),range=profile['range'],range_scaled=profile['range_scaled'],
            comparison=str(comparison),integer_comparison=profile['comparison_integer_bound'],all_saved_cycle_rule_deficits_zero=True,
            coefficient_independent_cycle_ceiling=str(mean),cycle=decoded))
    experiments.append(dict(label=label,status=data['status'],edges=data['edges'],removed=len(removed),additional_to_prior=data['additional_removed'],
        additional_to_previous_family=data['additional_to_previous_family'],probe_statuses=probes,profiles=profiles))
prior_total = set(read(ROOT/'milestones/114-total-count-pressure/data/total19/removed-indices.json'))
middle_removed=set(read(HERE/'data/middle345-total22/removed-indices.json'))
assert prior_total <= middle_removed <= removed_sets['universal345-total21'] <= removed_sets['universal345-total22']
extra_removed = {label:len(values-middle_removed) for label,values in removed_sets.items()}
common_shapes = set.intersection(*(set(tuple(e['placements'][1]['canonical_shape']) for e in p['cycle']) for x in experiments for p in x['profiles']))
common_windows = [dict(experiment=x['label'],profile=p['profile'],edge=e['edge'],shape=e['placements'][1]['canonical_shape'],counts=e['placements'][1]['counts'])
    for x in experiments for p in x['profiles'] for e in p['cycle'] if tuple(e['placements'][1]['canonical_shape']) in common_shapes]
probe_details=[]
for name in ['012345-total20','012345-total21','012345-total22','012345-total22-long','012345-total23','012345-ends3-middle4-total20']:
    probe_path=HERE/'data/probes'/(name+'.json')
    probe=read(probe_path)
    assert probe['status'] in ['UNSAT_UNCERTIFIED','UNKNOWN','SAT_LOCAL_WITNESS']
    assert probe['directions']==list(range(6)) and probe['positions']==list(range(5))
    for path,digest in probe['source_files_sha256'].items():assert pin(ROOT/path)==digest
    assert pin(HERE/'scripts/probe_sum.py')==probe['script_sha256']
    probe_details.append(dict(name=probe['name'],bounds=probe['bounds'],cap=probe['cap'],status=probe['status'],cycle_cuts=len(probe['cycle_cuts']),solver_seconds=probe['solver_seconds']))
stronger=[]
for exp in experiments:
    if exp['label']!='universal345-total22':continue
    for prof in exp['profiles']:
        matches=[dict(edge=e['edge'],offset=p['offset'],counts=p['counts'],clipped_sum=sum(p['counts']),demand23=max(0,23-sum(p['counts']))) for e in prof['cycle'] for p in e['placements'] if p['canonical_shape']==list(range(6))]
        assert matches==[]
        stronger.append(dict(profile=prof['profile'],cycle_edges=len(prof['cycle']),placements_checked=2*len(prof['cycle']),matching_windows=matches,minimum_012345_clipped_sum=None,all_candidate23_demands_zero=True,unchanged_cycle_mean=prof['mean'],old_potential_range=prof['range']))
out = dict(probe_details=probe_details,candidate23_cycle_test=stronger,monotonicity_scope='If only the universal012345 lower bound increases22to23, deletions increase and surviving-edge weights do not decrease. The old all-edge certificate therefore remains valid. No saved attaining cycle contains this shape at either placement, so its weights and membership remain unchanged. This is an arithmetic transfer conditional on the producer all-edge certificate, not a new graph23 scan or Lean proof.',status='PASS_BOUNDED_SAVED_CYCLE_REVIEW',experiments=experiments,
    extra_removed_beyond_middle345_family=extra_removed,
    common_suffix_shapes=[list(s) for s in sorted(common_shapes)],common_suffix_windows=common_windows,
    source_pins=pins,algorithm_source_sha256=algorithm_sha,script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    adapted_from=dict(path=old_script.relative_to(ROOT).as_posix(),sha256=pin(old_script)),
    scope='Independent saved-cycle membership, original-key endpoints/weights, all eleven or ten rule deficits on both placements, potential bytes/ranges and exact comparison arithmetic. Removal sets/counts checked, but rule predicates and potential inequalities not rerun over all edges. The universal total-count rules have native UNSAT evidence only; unproved family hypotheses remain explicit. No solver or Lean compilation; no new actual-snake bound.')
parser = argparse.ArgumentParser()
parser.add_argument('--output',type=Path)
args = parser.parse_args()
text = json.dumps(out,indent=2)+'\n'
if args.output:
    with args.output.open('x',encoding='utf-8') as stream:
        stream.write(text)
    print(json.dumps(dict(status=out['status'],experiments=len(experiments),output=str(args.output),sha256=hashlib.sha256(args.output.read_bytes()).hexdigest(),common_suffix_shapes=out['common_suffix_shapes']),indent=2))
else:
    print(text,end='')
