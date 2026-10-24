"""Add a checked endpoint-unit interpretation to the multi-centre counter proof."""
from pathlib import Path
import importlib.util,itertools,json,sys,types
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('joint_certificate',ROOT/'milestones/41-joint-intervening-sum/scripts/certify.py')
p=importlib.util.module_from_spec(spec);spec.loader.exec_module(p);p.HERE=HERE;p.old.HERE=HERE
p.DIRS=[0,1,2,3,4,0,3,1];p.BOUNDS=[(0,21)]*7
old=p.old;gen=p.gen;W=p.window(p.DIRS);e=p.TaggedEncoding(W,p.BOUNDS,radius=4)
e.atmost(p.joint_literals(e,W,[2,6]),7,('ends',))
description=json.loads((HERE/'data/core.json').read_text())
endvars={v:k for k,(kind,v,*_) in e.meaning.items() if kind=='e'}
for v in description['avoid_vertices']:e.add([-endvars[v]],('avoid',v))
name='endpoint451';mod='EndpointPair451';prefix=HERE/'certificates'/name
ids=[j-1 for j in description['ordinary_clause_ids']+description['endpoint_clause_ids']]
ordinary_n=len(description['ordinary_clause_ids']);clauses=[e.clauses[j] for j in ids]
used=sorted({abs(v) for c in clauses for v in c});ordering=used+sorted(e.meaning.keys()-set(used));rename={v:j+1 for j,v in enumerate(ordering)}
lit=lambda v:(1 if v>0 else -1)*rename[abs(v)]
compact=[[lit(v) for v in c] for c in clauses];old.writecnf(prefix.with_suffix('.cnf'),len(used),compact)
encoded=[[gen.code(v) for v in c] for c in compact]
ordinary=encoded[:ordinary_n];units=[c[0] for c in encoded[ordinary_n:]]
assert all(len(c)==1 for c in encoded[ordinary_n:])
for folder in ['LocalWindowCnf','LocalWindowSat']:(HERE/'lean'/folder).mkdir(exist_ok=True)
source=f'''import LocalWindowModel
set_option maxRecDepth 100000
namespace Snake9.LocalWindow.{mod}
def window : List Nat := {W}
def bounds : List (Nat × Nat) := [{','.join('(0,21)' for _ in range(7))}]
def ordinaryRaw : List (List Nat) := [
'''+',\n'.join('['+','.join(map(str,c))+']' for c in ordinary)+f'''
]
def endpointLits : List Nat := {units}
def endpointVertices : List Nat := {description['endpoint_demand']}
def endpointRaw : List (List Nat) := endpointLits.map (fun l => [l])
def raw := ordinaryRaw ++ endpointRaw
def cnf : List (List Int) := raw.map (·.map decodeLit)
end Snake9.LocalWindow.{mod}
'''
(HERE/f'lean/LocalWindowCnf/{mod}.lean').write_text(source,encoding='utf-8')
small=types.SimpleNamespace(nv=len(ordering),meaning={rename[k]:v for k,v in e.meaning.items()},ctrs=[([lit(x) for x in ls],k,kind) for ls,k,kind in e.ctrs])
p.sat_source(name,mod,small,[e.tags[j] for j in ids[:ordinary_n]],[2,6],7)
path=HERE/f'lean/LocalWindowSat/{mod}.lean';s=path.read_text(encoding='utf-8')
s=s.replace('import MultiCentreCount','import MultiCentreCount\nimport EndpointUnits')
s=s.replace('tags raw = true','tags ordinaryRaw = true')
s=s.replace('theorem sat (S E', '''theorem endpoint_negative : endpointLits.all (negE meaning) = true := by decide +kernel
theorem endpoint_meanings : endpointLits.map (vl meaning) = endpointVertices := by decide +kernel

theorem sat (S E''')
s=s.replace('(h : jointSum S ≤ 7) : ∃ τ, cnfTrue τ cnf = true := by','(h : jointSum S ≤ 7) (hnone : ∀ v ∈ endpointVertices, E v = false) : ∃ τ, cnfTrue τ cnf = true := by')
tail='''  exact ⟨tau S E meaning ctrs,
    JointTags.sound meaning ctrs window (centresK window bounds) tags raw clause_check S E hv axK⟩'''
assert tail in s
s=s.replace(tail,'''  have ho := JointTags.sound meaning ctrs window (centresK window bounds)
    tags ordinaryRaw clause_check S E hv axK
  have he := EndpointUnits.sound S E meaning ctrs endpointLits endpoint_negative (by
    intro l hl
    apply hnone
    rw [← endpoint_meanings]
    exact List.mem_map_of_mem hl)
  refine ⟨tau S E meaning ctrs, ?_⟩
  unfold cnf raw
  rw [List.map_append]
  unfold cnfTrue
  rw [List.all_append]
  rw [Bool.and_eq_true]
  exact ⟨ho,he⟩''')
path.write_text(s,encoding='utf-8')
meta=dict(module='LocalWindowCnf.'+mod,core_ids=list(range(1,len(compact)+1)),source_original_clause_ids=[j+1 for j in ids],active_variables=len(used),original_to_new=rename,dirs=p.DIRS,bounds=p.BOUNDS,positions=[2,6],joint_cap=7,ordinary_clauses=ordinary_n,endpoint_vertices=description['endpoint_demand'],cycle_cuts=[])
(HERE/f'data/{name}.json').write_text(json.dumps(meta,indent=2)+'\n')
old.run([old.LEANBIN/'cadical.exe','-q','--lrat','--no-binary',prefix.with_suffix('.cnf'),prefix.with_suffix('.lrat')],name+'-lrat-cadical.txt',20)
import gen_lean_lrat as lr
slots=lr.plan(meta['core_ids'],lr.read_lrat(str(prefix.with_suffix('.lrat'))))[3]
bits=next(b for b in range(13,20) if slots<1<<b)
report=old.run([sys.executable,'-X','utf8',ROOT/'milestones/10-window-aggregate/scripts/gen_lean_lrat.py','--work',HERE/'certificates','--data',HERE/'data','--out',HERE/'lean','--fast','--check','--noncomputable-data','--wbits',bits,'--off',2400,name],name+'-export.txt')
print('Exported',len(compact),'clauses;',len(used),'variables;',len(units),'endpoint units;',json.loads(report)['hints'],'hints',flush=True)
