from pathlib import Path
import hashlib,json
R=Path('E:/Snake-in-a-box');H=R/'milestones/192-moving-ports';D=Path(__file__).parent
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
seed=json.loads((H/'data/seed.json').read_text());p=seed['path'];cert=json.loads((H/'data/coordinated-certificates.json').read_text())[seed['bank_index']];assert cert['seed_index']==25
k=seed['original_cross_coordinate'];raw=json.loads((R/'work/bank9.json').read_text())[seed['bank_index']]['vertex_sequence']
def moved(v):return (v&((1<<k)-1))|((v>>(k+1))<<k)|(((v>>k)&1)<<8)
assert [moved(v) for v in raw]==p
def direction_map(d):return d if d<k else d-1 if d>k else 8
ordered=sorted(cert['endpoint_cases'],key=lambda r:(r['side']=='right',direction_map(r['direction'])))
files={'SquareChoice192':(D/'SquareChoice192.lean').read_text()}
files['SquareData192']='import SquareChoice192\nnamespace SquareChoice192\ndef values : Array Nat := #['+', '.join(map(str,p))+']\ndef original (i : Nat) : Nat := values[i]!\ndef alternate (i : Nat) : Nat := Nat.xor (Nat.xor (original (i-1)) (original i)) (original (i+1))\nend SquareChoice192\n'
receipts=[]
for case,record in enumerate(ordered):
    root=0 if record['side']=='left' else 191;direction=direction_map(record['direction']);w=p[root]^(1<<direction);bad=record['obstruction'];assert bad is not None and bad['kind']!='other_fixed_endpoint'
    required=set(record['required']);parents={r:None for r in required}
    for u,v in record['propagation']:
        assert u in parents and v not in parents;parents[v]=u
        assert v in cert['dependencies'][str(u)]
    targets=bad.get('indices',[bad.get('index')]);needed=set()
    for t in targets:
        while t is not None:needed.add(t);t=parents[t]
    roots=sorted(required&needed);steps=[(u,v) for u,v in record['propagation'] if v in needed]
    name=f'SquareCase192_{case:02d}'
    source=f'''import SquareData192
set_option maxRecDepth 100000
namespace SquareChoice192
theorem case{case:02d} (x : Nat → Bool) (h0 : x 0=false) (h191 : x 191=false)
    (hs : ∀ i j, i<192 → j<192 → (i+1<j ∨ j+1<i) →
      conflict (pick original alternate x i) (pick original alternate x j)=false)
    (he : ∀ i, i<192 → i≠{root} → conflict {w} (pick original alternate x i)=false) : False := by
'''
    for i in roots:
        assert i!=root and (p[i]==w or (p[i]^w).bit_count()==1)
        source+=f'  have z{i} : x {i}=true := forceOld original alternate x {w} {i} (he {i} (by decide) (by decide)) (by decide +kernel)\n'
    for i,j in steps:
        assert abs(i-j)>1
        source+=f'  have z{j} : x {j}=true := propagate original alternate x {i} {j} (hs {i} {j} (by decide) (by decide) (by decide)) (by decide +kernel) z{i}\n'
    if bad['kind']=='fixed_endpoint':
        i=bad['index'];assert i in [0,191];source+=f'  rw [z{i}] at h{i}\n  contradiction\n'
    elif bad['kind']=='forbidden_flip':
        i=bad['index'];assert i in record['forbidden'];source+=f'  have hn : x {i}=false := forbidNew original alternate x {w} {i} (he {i} (by decide) (by decide)) (by decide +kernel)\n  rw [z{i}] at hn\n  contradiction\n'
    else:
        i,j=bad['indices'];assert j in cert['conflicts'][str(i)] and abs(i-j)>1
        source+=f'  exact pairImpossible original alternate x {i} {j} (hs {i} {j} (by decide) (by decide) (by decide)) (by decide +kernel) z{i} z{j}\n'
    source+=f'#print axioms case{case:02d}\nend SquareChoice192\n';files[name]=source
    receipts.append({'case':case,'module':name,'side':record['side'],'endpoint_index':root,'direction':direction,'normalized_extension_vertex':w,'required_roots':roots,'used_implications':steps,'obstruction':bad})
for name,source in files.items():(H/'lean'/(name+'.lean')).write_text(source,encoding='utf-8',newline='\n')
base=json.loads((H/'data/MovingEndpoints192-execution.json').read_text());base.update(new_module_order=list(files),source_sha256={n:sha(H/'lean'/(n+'.lean')) for n in files},input_pins={str(q):sha(q) for q in [H/'data/seed.json',H/'data/coordinated-certificates.json',H/'scripts/native_resources.py']})
base['search_paths']=[str(H/'build')]
for name in files:(H/'data'/(name+'-execution.json')).write_text(json.dumps(base,indent=2)+'\n')
(H/'data/square-order.json').write_text(json.dumps(list(files),indent=2)+'\n');(H/'data/square-cases.json').write_text(json.dumps(receipts,indent=2)+'\n');(H/'scripts/square_lean.py').write_bytes(Path(__file__).read_bytes())
print('PREPARED',len(files),'modules',len(receipts),'endpoint candidates','maximum implications',max(len(r['used_implications']) for r in receipts))
