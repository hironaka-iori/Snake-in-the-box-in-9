from pathlib import Path
import hashlib,json
R=Path('E:/Snake-in-a-box');H=R/'milestones/192-moving-ports'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
order=json.loads((H/'data/square-order.json').read_text());pins={}
for n in order:
    q=H/'data'/(n+'-audit.json');r=json.loads(q.read_text());assert r['status']=='PASS'
    pins[str(q)]=sha(q)
    for field,hashfield in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:assert sha(r[field])==r[hashfield];pins[r[field]]=r[hashfield]
    for p,h in r['dependencies'].items():assert sha(p)==h;pins[p]=h
s=''.join('import '+n+'\n' for n in order if n.startswith('SquareCase'))
s+='''set_option maxRecDepth 100000
namespace SquareChoice192
def endpoint (right : Bool) : Nat := if right then 191 else 0

theorem noEndpointExtension (x : Nat → Bool) (right : Bool) (k : Fin 9)
    (h0 : x 0=false) (h191 : x 191=false)
    (hs : ∀ i j, i<192 → j<192 → (i+1<j ∨ j+1<i) →
      conflict (pick original alternate x i) (pick original alternate x j)=false)
    (he : ∀ i, i<192 → i≠endpoint right →
      conflict (Nat.xor (original (endpoint right)) (2^k.val))
        (pick original alternate x i)=false) : False := by
  cases right
'''
for side in range(2):
    s+='  · have hk : '+ ' ∨ '.join(f'k.val={i}' for i in range(9))+' := by omega\n'
    s+='    rcases hk with '+ '|'.join(f'hdir{i}' for i in range(9))+'\n'
    for i in range(9):s+=f'    · rw [hdir{i}] at he\n      exact case{side*9+i:02d} x h0 h191 hs he\n'
s+='#print axioms noEndpointExtension\nend SquareChoice192\n'
name='SquareExtension192';source=H/'lean'/(name+'.lean');source.write_text(s,encoding='utf-8',newline='\n')
base=json.loads((H/'data/SquareChoice192-execution.json').read_text());base.update(new_module_order=[name],source_sha256={name:sha(source)},input_pins=pins)
(H/'data'/(name+'-execution.json')).write_text(json.dumps(base,indent=2)+'\n');(H/'scripts/aggregate.py').write_bytes(Path(__file__).read_bytes())
