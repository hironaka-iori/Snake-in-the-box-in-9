"""Check whether current sharp cycles and floor obstructions survive the new rule."""
from pathlib import Path
import hashlib,json,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/109-relaxed-graph-test/scripts'));import check_graph as base
np=base.np;sha=lambda b:hashlib.sha256(b).hexdigest();pins={}
def read(rel):
    p=ROOT/rel;raw=p.read_bytes();pins[rel]=sha(raw);return json.loads(raw)
removed=set(read('milestones/109-relaxed-graph-test/data/removed-edge-indices.json'))
restriction=read('milestones/109-relaxed-graph-test/data/restricted-profiles.json')
screen=read('milestones/110-critical-cycle-core-screen/data/all-core-screen.json')
graph='milestones/72-four-count-proof-closure/critical-current/'
meta=read(graph+'data/source-proved-model.json');gp=ROOT/(graph+'build/source-graph.npz');pins[gp.relative_to(ROOT).as_posix()]=sha(gp.read_bytes())
with np.load(gp) as z:a={k:z[k] for k in z.files}
assert {k:sha(v.tobytes()) for k,v in a.items()}==meta['arrays_sha256']
ds=read('milestones/59-extended-share-window/extended/data/model.json')['extensions']
floors={(0,1,2,0,3,1):16,(0,1,2,0,3,2):16,(0,1,2,0,3,4):18,(0,1,2,3,0,1):16,
        (0,1,2,3,0,4):16,(0,1,2,3,1,0):12,(0,1,2,3,1,4):16,(0,1,2,3,4,0):16,(0,1,2,3,4,5):16}
tests=[(7301,'012032',15,'case7301.json'),(7302,'012034',17,'012034-minimum/floor17.json'),
       (7303,'012301',15,'case7303.json'),(7307,'012340',15,'case7307.json'),(7308,'012345',15,'case7308.json')]
walks=[];survival=[]
for case,shape,floor,path in tests:
    d=read('milestones/97-geometric-credit-integration/floor-sensitivity/'+path)
    es=[r['edge'] for r in d['walk']];assert es and all(a['V'][x]==a['U'][y] for x,y in zip(es,es[1:]))
    assert not (set(es)&removed)
    local=floors|{tuple(map(int,shape)):floor};total=0
    for e in es:
        word=ds[int(a['direction'][e])];key=min(base.canon(word[-6:]),base.canon(word[-6:][::-1]))
        total+=max(int(a['weight'][e]),120*(int(a['count_code'][e])%6+1)+local[key])
    cycle=[r['edge'] for r in d['cycle']];assert not(set(cycle)&removed)
    assert all(a['V'][x]==a['U'][y] for x,y in zip(cycle,cycle[1:]+cycle[:1]))
    cw=[]
    for e in cycle:
        word=ds[int(a['direction'][e])];key=min(base.canon(word[-6:]),base.canon(word[-6:][::-1]))
        cw.append(max(int(a['weight'][e]),120*(int(a['count_code'][e])%6+1)+local[key]))
    assert sum(cw)==496*len(cycle)
    ceiling=(227-len(es))*496+total;assert len(es)<=227 and ceiling<=111960
    survival.append(dict(case=case,tested_floor=floor,path_length=len(es),path_total=total,
        criterion_ceiling=ceiling,threshold=111960,cycle_mean=496,path_survives=True,cycle_survives=True))
    walks.append((str(case),es))
for row in restriction['profiles']:walks.append((row['profile']+'-sharp-cycle',row['sharp_cycle_original_indices']))
def hit(e,candidate):
    word=ds[int(a['direction'][e])];code=int(a['count_code'][e]);digits=[code//6**j%6+1 for j in range(5,-1,-1)]
    bounds=candidate['proposed_bounds'];width=len(bounds)
    for s in range(7-width):
        part=word[s+2:s+width+3]
        for rev in [False,True]:
            if base.canon(part[::-1] if rev else part)!=tuple(candidate['directions']):continue
            if all(lo<=digits[s+(width-1-i if rev else i)]<=hi for i,(lo,hi) in enumerate(bounds)):return True
    return False
candidate_hits=[]
for candidate in screen['candidates']:
    candidate_hits.append(dict(root=candidate['root'],hits={name:[e for e in es if hit(e,candidate)] for name,es in walks}))
out=dict(status='BROAD_CYCLE_AND_OBSTRUCTION_SCREEN',tests=survival,hypothetical_candidate_hits=candidate_hits,
    source_files_sha256=pins,script_sha256=sha(Path(__file__).read_bytes()),
    scope='Exact finite-graph checks. Existing paths still obstruct lowering each pending floor by one with the other current floors fixed. Candidate hit tests remain hypothetical except the proved D01234A1542 rule. No new global upper bound.')
(HERE/'data/cycle-screen.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print('Broad candidate sharp-cycle hits:',[(r['root'],{k:len(v) for k,v in r['hits'].items() if k.endswith('cycle') and v}) for r in candidate_hits if any(v for k,v in r['hits'].items() if k.endswith('cycle'))])
