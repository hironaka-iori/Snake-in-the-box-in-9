from pathlib import Path
from fractions import Fraction
import json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text())
family=read(HERE/'data/family.json');geos={tuple(r['directions']):r for r in read(HERE/'data/geometry.json')}
selected=sorted({tuple(e['directions']) for e in family['edges'] if e['weight']>e['original_weight']})
old=read(ROOT/'milestones/61-critical-family-share/data/geometry.json')['patterns'];positive=[(i,r) for i,r in enumerate(old) if r['lower']>0]
reuse={tuple(r['directions']):(i,j//8,r) for j,(i,r) in enumerate(positive)}
records=[]
for begin in range(0,len(selected),5):
    group=selected[begin:begin+5];imports={'GenericWindow'}
    for ds in group:
        if ds in reuse and reuse[ds][2]['lower']>=geos[ds]['lower']:imports.add(f'GeometryBatch{reuse[ds][1]:02d}')
    lines=['import '+x for x in sorted(imports)]+['namespace Snake9.LocalWindow.FamilyCharge67',
        'open ForcedShare58 ExtendedShare59 CriticalExtension60','set_option maxHeartbeats 0','set_option maxRecDepth 100000']
    for i,ds in enumerate(group,begin):
        r=geos[ds];L=r['lower'];known=ds in reuse and reuse[ds][2]['lower']>=L
        lines += [f'namespace G{i:03d}',f"def W : List Nat := {r['vertices']}",f'def ds : List Nat := {list(ds)}']
        if known:
            oi,batch,pr=reuse[ds];theorem=f'Snake9.LocalWindow.FamilyShare61.G{oi:03d}.in_snake'
            proof=f'by\n  have h := {theorem} p P r hr hP\n  exact (by decide : {L}≤{pr["lower"]}).trans h'
        else:
            D=r['absent'];mask=sum(1<<v for v in D)
            lines += [f'def D : List Nat := {D}',f"def C : List Nat := {r['centres']}",f'def mask : Nat := {mask}',
                'theorem canonical : Canon W ds := ⟨rfl,rfl,by decide +kernel⟩',
                'theorem forced : forceCheck W D=true := by decide +kernel',
                'theorem supported : supportCheck W C=true := by decide +kernel',
                'theorem checked_mask : maskCheck mask D=true := by decide +kernel',
                f'theorem credit : {L}≤(C.map (shareLocal 12 (allowed mask))).sum := by decide +kernel']
            proof=f'''share_in_snake (W:=W) (cs:=ds) (D:=D) (C:=C) (L:={L}) (mask:=mask) (start:=6)
    canonical (by decide) (by decide) rfl forced supported checked_mask credit p P r hr hP'''
        lines += [f'''theorem in_snake {{m : Nat}} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r+ds.length≤m) (hP : ∀ j, j<ds.length → P.fwd (dir p (r+j))=ds.getD j 0) :
    {L}≤((List.range 5).map (fun i => coreShare 12 p (r+(i+6)))).sum := {proof}''']
        lines += ['#print axioms '+x for x in (['in_snake'] if known else ['canonical','forced','supported','checked_mask','credit','in_snake'])]
        lines.append(f'end G{i:03d}')
        records.append(dict(index=i,directions=ds,lower=L,reused=known,module=f'ChargeBatch{begin//5:02d}',
            prior_instance=f'G{reuse[ds][0]:03d}' if known else None))
    lines.append('end Snake9.LocalWindow.FamilyCharge67')
    (HERE/f'lean/ChargeBatch{begin//5:02d}.lean').write_text('\n'.join(lines)+'\n',encoding='utf-8')
for result in read(HERE/'data/analyses.json'):
    mode=result['mode'];name='OriginalPotential' if mode=='original_weight' else 'ChargePotential'
    es=[(e['u'],e['v'],e[mode]) for e in family['edges']];cy=[es[i] for i in result['cycle']]
    mu=Fraction(result['integer_mean']);p,d=mu.numerator,mu.denominator
    source=f'''import FinitePotential
namespace Snake9.CriticalFamily61.FamilyCharge67.{name}
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def edges : List (Nat × Nat × Nat) := {es}
def potential : List Nat := {result['potential']}
def cycle : List (Nat × Nat × Nat) := {cy}
theorem checked : checkEdges {p} {d} potential edges=true := by decide +kernel
theorem every_closed_walk (n : Nat) (f w : Nat → Nat)
    (h : ∀ i<n, (f i,f (i+1),w i)∈edges) (hc : f n=f 0) :
    n*{p}≤{d}*(∑ i∈Finset.range n,w i) := by
  apply closed_bound {p} {d} n (fun x => potential.getD x 0) f w ?_ hc
  intro i hi
  exact edge_of_check checked (h i hi)
theorem attaining_cycle : (List.range cycle.length).all (fun i =>
    edges.contains (cycle.getD i (0,0,0)) &&
    decide ((cycle.getD i (0,0,0)).2.1=(cycle.getD ((i+1)%cycle.length) (0,0,0)).1))=true := by decide +kernel
theorem attainment : {d}*(cycle.map (fun e => e.2.2)).sum={p}*cycle.length := by decide +kernel
#print axioms checked
#print axioms every_closed_walk
#print axioms attaining_cycle
#print axioms attainment
end Snake9.CriticalFamily61.FamilyCharge67.{name}
'''
    (HERE/f'lean/{name}.lean').write_text(source,encoding='utf-8')
replay=(ROOT/'milestones/66-full-model-and-revision/scripts/replay.py').read_text()
replay=replay.replace("[('65-count-saturation-share','latest')", "[('66-full-model-and-revision','latest'),('65-count-saturation-share','latest')")
(HERE/'scripts/replay.py').write_text(replay)
(HERE/'data/proof-plan.json').write_text(json.dumps(records,indent=2)+'\n')
print('Patterns',len(records),'reused',sum(r['reused'] for r in records),'new',sum(not r['reused'] for r in records))
