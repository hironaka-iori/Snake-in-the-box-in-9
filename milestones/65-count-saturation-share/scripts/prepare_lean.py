from pathlib import Path
import json,sys
HERE=Path(__file__).resolve().parents[1]
packets=json.loads((HERE/'data/compact-certificates.json').read_text())['rows']
exclusion='--exclusion' in sys.argv
packets=[r for r in packets if (r.get('mode','share')=='exclusion')==exclusion]
if '--pilot' in sys.argv:packets=packets[:1]
opt=lambda x:'none' if x is None else 'some '+str(x)
def conjunction(xs):return xs[0] if len(xs)==1 else '⟨'+xs[0]+', '+conjunction(xs[1:])+'⟩'
for record in packets:
    i=record['edge'];r=json.loads((HERE/f'data/cases/e{i:03d}.json').read_text());L=record['lower']
    used=set()
    for br in record['certificates']:
        if 'condition' in br['ending']:used.add(br['ending']['condition'])
        used.update(t['condition'] for t in br['steps'] if 'condition' in t)
    bounds=[(0,21)]*10
    for k in used:bounds[k+4]=(0,r['constraints'][k]['hi'])
    src=['import CountReject' if exclusion else 'import CountChoice',f'namespace Snake9.LocalWindow.CountPropagation65.E{i:03d}',
        'open ForcedShare58 ExtendedShare59 SplitShare62 NeighbourChoice64',
        'set_option maxHeartbeats 0','set_option maxRecDepth 100000',
        f"def W : List Nat := {r['vertices']}",f"def dirs : List Nat := {list(r['directions'])}",
        f"def A : List Nat := {r['A']}",f"def B : List Nat := {r['B']}",f"def C : List Nat := {r['centres']}",
        f'def bounds : List (Nat × Nat) := {bounds}']
    for k,c in enumerate(r['constraints']):
        j=c['position'];src.append(f"def c{k} : Centre := ⟨{r['vertices'][j]},{r['directions'][j-1]},{r['directions'][j]},0,{c['hi'] if k in used else 21}⟩")
        src.append(f'def cond{k} : Condition := ofCentre c{k}')
    src+=['def centres : List Centre := [c0,c1,c2,c3,c4,c5]','def conds : List Condition := centres.map ofCentre',
        'def cert : Option Nat → Option Nat → TraceCertificate']
    for br in record['certificates']:
        a,b=br['choices'];steps=[]
        for t in br['steps']:
            steps.append(f".degree {t['add']}" if t['kind']=='degree' else f".select cond{t['condition']} {t['add']}")
        end=br['ending'];ending='.degree' if end['kind']=='degree' else f".upper cond{end['condition']}" if end['kind']=='upper' else f".share {end['mask']}"
        src.append(f"  | {opt(a)}, {opt(b)} => ⟨{br['forced']}, [{', '.join(steps)}], {ending}⟩")
    src+=['  | _, _ => ⟨[],[],.share 0⟩',
        'theorem canonical : Canon W dirs := ⟨rfl,rfl,by decide +kernel⟩',
        'theorem supported : supportCheck W C=true := by decide +kernel',
        'theorem pairA : pairCheck W A=true := by decide +kernel',
        'theorem pairB : pairCheck W B=true := by decide +kernel',
        'theorem centres_checked : centres.all (fun c => (canonicalCentres W dirs bounds).contains c)=true := by decide +kernel']
    for j,br in enumerate(record['certificates']):
        a,b=br['choices'];src.append(f'theorem case{j:02d} : certCheck W A B C conds {L} ({opt(a)}) ({opt(b)}) (cert ({opt(a)}) ({opt(b)}))=true := by decide +kernel')
    width=len(r['B'])+1;proof=conjunction([conjunction([f'case{j:02d}' for j in range(k,k+width)]) for k in range(0,len(record['certificates']),width)])
    src.append(f'''theorem checked : (choices A).all (fun a => (choices B).all (fun b =>
    certCheck W A B C (centres.map ofCentre) {L} a b (cert a b)))=true := by
  simp only [choices,A,B,List.map_cons,List.map_nil,List.all_cons,List.all_nil,
    Bool.and_eq_true_iff,and_true]
  exact {proof}
theorem in_snake {{m : Nat}} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+dirs.length≤m) (hP : ∀ j, j<dirs.length → P.fwd (dir p (r+j))=dirs.getD j 0)
    (hb : ∀ i, i<bounds.length → (bounds.getD i (0,21)).1≤coreAlpha p (r+i+1) ∧
      coreAlpha p (r+i+1)≤(bounds.getD i (0,21)).2) :
    {L}≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := by
  apply count_choices_in_snake (W:=W) (dirs:=dirs) (A:=A) (B:=B) (C:=C)
    (bounds:=bounds) (centres:=centres) (L:={L}) (start:=6) cert canonical
    (by decide) (by decide) rfl ?_ supported pairA pairB checked p P r hr hP hb
  intro c hc
  rw [centresOf_canon canonical (by decide)]
  exact List.contains_iff.mp (List.all_eq_true.mp centres_checked c hc)
''')
    src += ['#print axioms '+n for n in ['canonical','supported','pairA','pairB','centres_checked','checked','in_snake']]
    src.append(f'end Snake9.LocalWindow.CountPropagation65.E{i:03d}')
    text='\n'.join(src)+'\n'
    if exclusion:
        text=text.replace('theorem in_snake', 'theorem all_reject : (choices A).all (fun a => (choices B).all (fun b => isRejection (cert a b).ending))=true := by decide +kernel\n\ntheorem impossible')
        text=text.replace(f'    {L}≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := by','    False := by')
        text=text.replace('apply count_choices_in_snake','apply count_choices_impossible').replace(f' (L:={L})','')
        text=text.replace('pairA pairB checked p P r','pairA pairB checked all_reject p P r')
        text=text.replace('#print axioms in_snake','#print axioms all_reject\n#print axioms impossible')
    (HERE/f'lean/Edge{i:03d}.lean').write_text(text,encoding='utf-8')
print('Generated',len(packets),'count-conditioned share instances')
