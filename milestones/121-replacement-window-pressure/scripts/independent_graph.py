"""Bounded saved-cycle audit; no solver, compiler, or full-edge inequality scan.

Adapted from119 independent_graph.py, with independent full-key diagram and
endpoint/weight reconstruction from the pinned original models. Output is
printed by default; --output creates a new file and never overwrites evidence.
"""
from pathlib import Path
from fractions import Fraction
import argparse, ast, gzip, hashlib, json, re, sys

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT/'work/solver_packages'))
import numpy as np

old_script = ROOT/'milestones/120-nine-transition-window/scripts/independent_graph.py'
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
prior_audit = read(ROOT/'milestones/117-cycle-sum-refinement/data/graph-audit.json')
algorithm_sha = prior_audit['algorithm_source_sha256']

label = 'pair-graph'
folder = HERE/'data'/label
data = read(folder/'results.json')
producer = HERE/'scripts/evaluate_pair.py'
assert data['script_sha256'] == pin(producer)
assert data['algorithm_sha256'] == algorithm_sha
for path,digest in data['source_files_sha256'].items():
    assert pin(ROOT/path) == digest
assert data['status'] == 'EXACT_FINITE_PROFILES_WITH_UNPROVED_SUM_RULES'
rules = data['rules']
assert len(rules) == 13 and data['coefficients'] == [24]*5
assert rules[-2]['name'] == '012304-completed-b-total23'
assert rules[-1]['name'] == '012304-conditional-a-total23'
assert data['prior117_full_weights_and_removals_reproduced'] is True
assert data['prior119_full_weights_and_removals_reproduced'] is True
assert rules[:11] == read(ROOT/'milestones/117-cycle-sum-refinement/data/middle5-rules.json')
probes = []
for rule in rules:
    probe = read(ROOT/rule['probe'])
    assert probe['status'] == 'UNSAT_UNCERTIFIED'
    assert shape(probe['directions']) == shape(rule['directions'])
    assert probe['bounds'] == rule['bounds']
    assert canon(probe['directions']) == shape(probe['directions'])
    assert canon(rule['directions']) == shape(rule['directions'])
    assert rule['positions'] == sorted(4-j for j in rule['positions'])
    assert len(set(rule['positions'])) == len(rule['positions'])
    assert probe.get('cap',probe.get('outer_sum_cap')) == rule['lower']-1
    assert probe.get('positions',[0,1,3,4]) == rule['positions']
    probes.append(dict(name=rule['name'],status=probe['status'],cycle_cuts=len(probe['cycle_cuts']),solver_seconds=probe.get('solver_seconds')))
orientation_checks = 0
for rule in rules[11:]:
    target = shape(rule['directions'])
    assert canon(rule['directions']) != canon(rule['directions'][::-1])
    for direction in ds:
        for offset in [0,1]:
            word = direction[offset+2:offset+8]
            if shape(word) != target:
                continue
            for trial in [[2,6,2,3,6],[2,6,4,2,6],[6,3,2,6,2],[6,2,4,6,2],[1,2,3,4,5]]:
                left = trial[::-1] if canon(word[::-1]) < canon(word) else trial
                rw,rc = word[::-1],trial[::-1]
                right = rc[::-1] if canon(rw[::-1]) < canon(rw) else rc
                assert left == right
                orientation_checks += 1
raw_removed = read(folder/'removed-indices.json')
removed = set(raw_removed)
assert len(removed) == len(raw_removed) and all(0 <= k < len(graph['U']) for k in removed)
assert prior <= removed and previous <= removed
assert len(graph['U'])-len(removed) == data['edges']
assert len(removed)-len(prior) == data['additional_removed']
assert len(removed)-len(previous) == data['additional_to_previous_family']
assert sum(e['marginal_removed'] for e in data['effects']) + data['guard_effect']['newly_removed'] + sum(e['marginal_removed'] for e in data['pair_effects']) == data['additional_removed']
old_folder=ROOT/'milestones/120-nine-transition-window/data/outer3'
old_results=read(old_folder/'results.json')
old_removed=set(read(old_folder/'removed-indices.json'))
assert old_removed <= removed and len(graph['U'])-len(old_removed)==old_results['edges']
extra_removed=len(removed-old_removed)
assert extra_removed==data['additional_to120']==sum(e['marginal_removed'] for e in data['pair_effects'])
assert data['prior120_full_weights_and_removals_reproduced'] is True
assert rules==old_results['rules']
guard_probe = read(ROOT/'milestones/120-nine-transition-window/data/probes/012031-outer3-radius3.json')
assert guard_probe['directions'] == [0,1,2,0,3,1]
assert guard_probe['bounds'] == [[0,3],[0,3],[0,21],[0,3],[0,3]]
assert guard_probe['status'] == 'UNSAT_UNCERTIFIED' and guard_probe['sum_cap'] is None

def pair_hits(di,code):
    counts=symbols(code)
    return [s for s in [0,1] if shape(ds[di][s+2:s+8])==(0,1,2,0,3,2)
            and (min(counts[s+1],counts[s+3])<2 or counts[s+1]+counts[s+3]<8)]

def guard_hits(di,code):
    counts=symbols(code)
    outer=[s for s in [0,1] if shape(ds[di][s+2:s+8])==(0,1,2,0,3,1)
           and all(counts[s+j]<=3 for j in [0,1,3,4])]
    return sorted(set(outer+pair_hits(di,code)))

new_removed=sorted(removed-old_removed)
new_guard_contexts=set()
for edge in new_removed:
    di,code=int(graph['direction'][edge]),int(graph['count_code'][edge])
    assert pair_hits(di,code), edge
    new_guard_contexts.add((di,int(graph['history'][edge])))
guard_orientation_checks=0
for word in ds:
    for offset in [0,1]:
        part=word[offset+2:offset+8]
        if shape(part)!=(0,1,2,0,3,1): continue
        for counts in [[3,3,6,3,3],[1,3,1,2,3],[4,3,6,3,3],[3,3,6,3,4]]:
            hit=all(counts[j]<=3 for j in [0,1,3,4])
            assert hit==all(counts[::-1][j]<=3 for j in [0,1,3,4])
            guard_orientation_checks+=1
pair_orientation_checks=0
for a in range(1,7):
    for b in range(1,7):
        hi=lambda x:21 if x==6 else x
        explicit=(hi(a)<=1 or hi(b)<=1 or (hi(a)<=2 and hi(b)<=5) or
                  (hi(b)<=2 and hi(a)<=5) or (hi(a)<=3 and hi(b)<=4) or
                  (hi(b)<=3 and hi(a)<=4))
        assert explicit==(min(a,b)<2 or a+b<8)
        pair_orientation_checks+=1
profiles=[]
for profile in data['profiles']:
    assert profile['all_edge_inequalities_checked'] is True
    potential_path=folder/profile['potential_file']
    pin(potential_path)
    raw=gzip.decompress(potential_path.read_bytes())
    assert hashlib.sha256(raw).hexdigest()==profile['potential_sha256']
    pi=np.frombuffer(raw,dtype='<i8')
    assert len(pi)==data['states']==meta['states']
    assert int(pi.min())==0 and int(pi.max())==profile['range_scaled']
    assert Fraction(profile['range'])==Fraction(profile['range_scaled'],profile['d'])
    cycle=profile['cycle']
    assert cycle
    floors=cf if profile['profile']=='completed' else ff
    decoded=[]
    for i,e in enumerate(cycle):
        k=e['edge']
        assert k not in removed and e['v']==cycle[(i+1)%len(cycle)]['u']
        assert not guard_hits(e['direction'],e['count_code'])
        for key,array in [('u','U'),('v','V'),('direction','direction'),('history','history'),('count_code','count_code')]:
            assert e[key]==int(graph[array][k])
        vals=symbols(e['count_code'])
        membership=accepted(e['direction'],e['history'],vals)
        original,u,v=original_semantics(e['direction'],e['history'],e['count_code'])
        assert original==int(graph['weight'][k]) and u==e['u'] and v==e['v']
        placements=[]
        reconstructed_bonus=0
        for s in [0,1]:
            word=ds[e['direction']][s+2:s+8]
            counts=vals[s:s+5]
            reverse=canon(word[::-1])<canon(word)
            # Canonicalize count order before applying asymmetric bounds.
            counts=counts[::-1] if reverse else counts
            evaluated=[]
            for rule in rules:
                applicable=shape(word)==shape(rule['directions']) and all(lo<=x and (21 if x==6 else x)<=hi for x,(lo,hi) in zip(counts,rule['bounds']))
                selected_sum=sum(counts[j] for j in rule['positions'])
                deficit=max(0,rule['lower']-selected_sum) if applicable else 0
                deletion=applicable and deficit>0 and all(counts[j]<6 for j in rule['positions'])
                assert not deletion
                coefficient=min(data['coefficients'][j] for j in rule['positions'])
                credit=coefficient*deficit if s==1 else 0
                reconstructed_bonus=max(reconstructed_bonus,credit)
                evaluated.append(dict(name=rule['name'],applicable=applicable,deficit=deficit,selected_clipped_sum=selected_sum,required_lower=rule['lower'],coefficient=coefficient,credit=credit,deletion=deletion))
            normalized=counts
            placements.append(dict(offset=s,raw_directions=word,canonical_shape=list(shape(word)),reverse=reverse,counts=normalized,
                count_intervals=[[x,21 if x==6 else x] for x in normalized],total_clipped=sum(counts),outer3_guard_hit=(s in guard_hits(e['direction'],e['count_code'])),rules=evaluated))
        floor=floors.get(shape(ds[e['direction']][-6:]),0)
        base=max(original,120*vals[-1]+floor)
        weight=base+reconstructed_bonus
        assert e['bonus']==reconstructed_bonus and e['weight']==weight
        slack=profile['d']*weight+int(pi[u])-profile['p']-int(pi[v])
        assert slack==0
        decoded.append(dict(edge=k,di=e['direction'],q=e['history'],code=e['count_code'],u=u,v=v,counts6=vals,original_weight=original,countfree_floor=floor,base_weight=base,bonus=reconstructed_bonus,weight=weight,potential_slack=slack,membership=membership,placements=placements))
    mean=Fraction(sum(e['weight'] for e in cycle),len(cycle))
    comparison=Fraction(1098960*profile['d']+8*profile['p']+profile['range_scaled'],4200*profile['d']+profile['p'])
    assert mean==Fraction(profile['mean'])==Fraction(profile['p'],profile['d'])
    assert comparison==Fraction(profile['comparison_bound'])
    assert comparison.numerator//comparison.denominator==profile['comparison_integer_bound']
    all_zero=all(r['deficit']==0 for e in decoded for p in e['placements'] for r in p['rules'])
    suffix_zero=all(r['deficit']==0 for e in decoded for r in e['placements'][1]['rules'])
    profiles.append(dict(profile=profile['profile'],mean=str(mean),cycle_length=len(cycle),weight_sum=sum(e['weight'] for e in cycle),range=profile['range'],range_scaled=profile['range_scaled'],potential_entries=len(pi),potential_min=int(pi.min()),potential_max=int(pi.max()),potential_raw_sha256=profile['potential_sha256'],producer_weight_sha256_not_recomputed=profile['weight_sha256'],comparison=str(comparison),integer_comparison=profile['comparison_integer_bound'],all_saved_cycle_rule_deficits_zero=all_zero,suffix_deficits_zero=suffix_zero,coefficient_independent_cycle_ceiling=str(mean) if suffix_zero else None,cycle=decoded))
shape_sets=[set(tuple(w['canonical_shape']) for e in p['cycle'] for w in e['placements']) for p in profiles]
common_shapes=set.intersection(*shape_sets)
common_windows=[]
for p in profiles:
    unique={}
    for e in p['cycle']:
        for w in e['placements']:
            if tuple(w['canonical_shape']) in common_shapes:
                key=(tuple(w['canonical_shape']),tuple(w['counts']))
                item=unique.setdefault(key,dict(shape=w['canonical_shape'],counts=w['counts'],total_clipped=sum(w['counts']),outer_clipped=sum(w['counts'])-w['counts'][2],occurrences=[]))
                item['occurrences'].append(dict(edge=e['edge'],offset=w['offset'],reverse=w['reverse']))
    common_windows.append(dict(profile=p['profile'],windows=list(unique.values())))
old_cycle_survival=[]
for p in old_results['profiles']:
    old_cycle_survival.append(dict(profile=p['profile'],cycle_length=len(p['cycle']),newly_removed_cycle_edges=[e['edge'] for e in p['cycle'] if e['edge'] in removed-old_removed],guard_hits=[dict(edge=e['edge'],placements=guard_hits(e['direction'],e['count_code'])) for e in p['cycle'] if guard_hits(e['direction'],e['count_code'])]))
out=dict(status='PASS_BOUNDED_SAVED_CYCLE_REVIEW',experiment=label,states=data['states'],edges=data['edges'],removed=len(removed),additional_to_prior=data['additional_removed'],additional_to_pair_family=data['additional_to_previous_family'],additional_to120=extra_removed,rule_count=len(rules),orientation_checks=orientation_checks,guard_orientation_checks=guard_orientation_checks,pair_orientation_checks=pair_orientation_checks,new_guard_removed_keys_checked=len(new_removed),new_guard_removed_contexts=len(new_guard_contexts),guard_effect=data['guard_effect'],coefficients=data['coefficients'],probe_statuses=probes,profiles=profiles,old_cycle_survival=old_cycle_survival,common_shapes=[list(s) for s in sorted(common_shapes)],common_windows=common_windows,source_pins=pins,algorithm_source_sha256_from_pinned117_audit=algorithm_sha,script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),adapted_from=dict(path=old_script.relative_to(ROOT).as_posix(),sha256=pin(old_script)),scope='Independent saved full-key diagram membership, original endpoint and weight reconstruction, all13rule tests with oriented asymmetric bounds plus the old outer3 and new pair guards at both placements, removal-set membership/counts and the guard hit of every newly removed key, potential bytes/ranges and cycle tightness, exact mean/comparison arithmetic. No full-edge rule or potential rescan; whole-graph lower certificates rely on pinned producer checks. Any coefficient ceiling is for this fixed thirteen-rule family only. Prior117/119/120 full-vector reproduction is producer-reported and source-reviewed, not rerun here. The guard theorem receipt is reviewed separately; inherited negative sum rules retain native evidence and remaining hypotheses and no new actual-snake bound are explicit.')
parser=argparse.ArgumentParser()
parser.add_argument('--output',type=Path)
args=parser.parse_args()
text=json.dumps(out,indent=2)+'\n'
if args.output:
    with args.output.open('x',encoding='utf-8') as stream:stream.write(text)
    print(json.dumps(dict(status=out['status'],output=str(args.output),sha256=hashlib.sha256(args.output.read_bytes()).hexdigest(),profiles=[{k:p[k] for k in ['profile','mean','cycle_length','range','comparison','all_saved_cycle_rule_deficits_zero']} for p in profiles],additional_to120=extra_removed,common_shapes=out['common_shapes']),indent=2))
else:print(text,end='')
