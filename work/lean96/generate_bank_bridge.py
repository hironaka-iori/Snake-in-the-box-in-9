"""Emit proof obligations and concrete data; all claims are checked by Lean."""
import json,sys,re
from pathlib import Path
from collections import Counter
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'work'))
from build_regrowth_cnf import encode
ENTRY=int(sys.argv[1])
DEST=HERE/'bank'
DEST.mkdir(exist_ok=True)
PN=f'E96{ENTRY:03d}'
BN=f'B96E{ENTRY:03d}'
path=json.loads((ROOT/'work/bank9.json').read_text())[ENTRY//2]['vertex_sequence']
if ENTRY%2:path=path[::-1]
d=encode(path, keep=96, total_vertices=193)
survey=json.loads((ROOT/'outputs/lean96/survey.json').read_text())['entries']
CORE_ENTRY=survey[str(ENTRY)].get('reused_from',ENTRY)
core=({'clauses':[],'original_clause_indices':[]} if '--data-only' in sys.argv else
    json.loads((ROOT/f'outputs/lean96/cores/entry{CORE_ENTRY:03d}.json').read_text()))
assert [d['clauses'][i-1] for i in core['original_clause_indices']]==core['clauses']
BLOCKS=(len(core['clauses'])+31)//32
def lst(xs): return '['+', '.join(map(str,xs))+']'
def verts(xs): return '['+', '.join(f'({x} : Vertex)' for x in xs)+']'
def write(name,s):
    name=name.replace('First96',PN)
    s=re.sub(r'\bprefix\b','pre',s).replace('Dfs96FirstBoolean',BN).replace('First96',PN)
    dest=DEST/(name+'.lean')
    if not dest.exists() or dest.read_text(encoding='utf-8')!=s:dest.write_text(s,encoding='utf-8')
ban=sum(1<<v for v in d['banned']); R=sum(1<<v for v in d['vertices'] if v!=d['head'])
write('First96Data',f'''import Regrowth96ParityCounts
namespace Snake9.Regrowth96.First96
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def prefix : Array Nat := #{lst(d['prefix'])}
def region : List Vertex := {verts(d['vertices'])}
def oddSide : List Vertex := {verts([v for v in d['vertices'] if v.bit_count()%2])}
def evenSide : List Vertex := {verts([v for v in d['vertices'] if not v.bit_count()%2])}
def others : List Vertex := {verts([v for v in d['vertices'] if v!=d['head']])}
def head : Vertex := {d['head']}
def ban : Nat := {ban}
def reachable : Nat := {R}
theorem ban_eq : banFrom (fun i => prefix[i]!) 95 = ban := by decide
theorem head_eq : prefix[95]! = head.val := by decide
theorem region_closed : expand reachable &&& freeOf ban = reachable := by decide
theorem region_start : ∀ y : Fin 512,
    (expand (2^head.val) &&& freeOf ban).testBit y.val = true →
    reachable.testBit y.val = true := by decide
theorem region_mem : ∀ v : Vertex,
    v = head ∨ reachable.testBit v.val = true → v ∈ region := by decide
theorem odd_mem : ∀ v : Vertex, v ∈ region → bitParity v.val = true → v ∈ oddSide := by decide
theorem even_mem : ∀ v : Vertex, v ∈ region → bitParity v.val = false → v ∈ evenSide := by decide
theorem others_mem : ∀ v : Vertex, v ∈ region → v ≠ head → v ∈ others := by decide
theorem others_nodup : others.Nodup := by decide
theorem head_not_others : head ∉ others := by decide
theorem oddSide_length : oddSide.length = {sum(v.bit_count()%2 for v in d['vertices'])} := by decide
theorem evenSide_length : evenSide.length = {sum(not v.bit_count()%2 for v in d['vertices'])} := by decide

theorem suffix_head (p : Snake 192) (hp : StartsWith p prefix 96) :
    (suffix p).vertex 0 = head := by
  apply Fin.ext
  exact (hp 95 (by decide) (by decide)).trans head_eq

theorem suffix_covered (p : Snake 192) (hp : StartsWith p prefix 96) :
    ∀ v, InPath (suffix p) v → v ∈ region := by
  have hb : banFrom (vals p) 95 = ban := by
    rw [← ban_eq]
    apply banFrom_congr
    intro i hi
    have hi' : i < 193 := by omega
    simpa only [vals, dif_pos hi'] using hp i (by omega) hi'
  have hh : vals p 95 = head.val := by
    exact congrArg Fin.val (suffix_head p hp)
  have hv := tail_valid p 97 95 (by decide)
  rw [hb,hh] at hv
  intro v hsel
  obtain ⟨i,rfl⟩ := hsel
  apply region_mem
  by_cases hi : i.val = 0
  · left
    have he : i = 0 := Fin.ext hi
    rw [he]
    exact suffix_head p hp
  · right
    apply hv.in_region region_closed region_start (Or.inl rfl) (fun _ h => h)
    apply List.mem_map.mpr
    refine ⟨i.val-1,List.mem_range.mpr (by omega),?_⟩
    have he : 95+1+(i.val-1) = 95+i.val := by omega
    simp only [he,vals,dif_pos (show 95+i.val < 193 by omega),suffix]

end Snake9.Regrowth96.First96
''')
print('Wrote First96Data; core clause kinds:',dict(Counter(d['reasons'][i-1]['kind'] for i in core['original_clause_indices'])))
if '--data-only' in sys.argv:sys.exit(0)

header='''namespace Snake9.Regrowth96.First96
noncomputable section
local instance propDec (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
'''
footer='\nend\nend Snake9.Regrowth96.First96\n'
N=len(d['vertices'])
base=['false']+[f'decide (InPath q ({v} : Vertex))' for v in d['vertices']]+[f'decide (BallClauseLogic.Endpoint q ({v} : Vertex))' for v in d['vertices']]
def lookup_tree(values,lo=0):
    if len(values)==1:return values[0]
    mid=len(values)//2
    return f'(if i < {lo+mid} then {lookup_tree(values[:mid],lo)} else {lookup_tree(values[mid:],lo+mid)})'
countof={}; threshold={}; leavesof={}
for c in d['counters']:
    name='count'+str(c['outputs'][0])
    for k,w in enumerate(c['outputs'],1): countof[w]=name;threshold[w]=k;leavesof[w]=c['leaves']
expr=['false']+[f'b {i}' for i in range(1,2*N+1)]+[f'decide ({threshold[w]} ≤ {countof[w]} b)' for w in range(2*N+1,d['variables']+1)]
s='import First96Data\n'+header
s+='def baseVal (q : Snake 97) (i : Nat) : Bool := '+lookup_tree(base)+'\n'
s+='def countLit (b : Nat → Bool) (xs : List Int) : Nat := xs.countP (literal b)\n'
for c in d['counters']:
    s+=f'def {countof[c["outputs"][0]]} (b : Nat → Bool) : Nat := countLit b {lst(c["leaves"])}\n'
s+='def valuationOf (b : Nat → Bool) (i : Nat) : Bool := '+lookup_tree(expr)+'\n'
s+='def valuation (q : Snake 97) : Nat → Bool := valuationOf (baseVal q)\n'
used=set(abs(lit) for c in core['clauses'] for lit in c)
for w in sorted(used):
    ex=base[w] if w<=2*N else expr[w].replace(' b)',' (baseVal q))')
    s+=f'theorem value{w} (q : Snake 97) : valuation q {w} = {ex} := rfl\n'
def meaning(w):return 'meaning'+('Neg'+str(-w) if w<0 else str(w))
usedmean=set()
for idx in core['original_clause_indices']:
    r=d['reasons'][idx-1]
    if r['kind']=='counter_merge':
        i,j=r['i'],r['j']
        if i:usedmean.add(r['left'][i-1])
        if j:usedmean.add(r['right'][j-1])
        usedmean.add(r['outputs'][i+j-1])
for w in sorted(usedmean):
    if abs(w)<=2*N:
        s+=f'''theorem {meaning(w)} (b : Nat → Bool) : literal (valuationOf b) ({w}) = decide (1 ≤ countLit b [{w}]) := by
  change literal b ({w}) = decide (1 ≤ countLit b [{w}])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b ({w}) <;> decide
'''
    else:
        s+=f'theorem {meaning(w)} (b : Nat → Bool) : literal (valuationOf b) {w} = decide ({threshold[w]} ≤ {countof[w]} b) := rfl\n'
s+='''structure Conditions (q : Snake 97) : Prop where
  head_fixed : q.vertex 0 = head
  covered : ∀ v, InPath q v → v ∈ region

theorem absent_odd_bound (q : Snake 97) (h : Conditions q) :
    (oddSide.filter (fun v => !(decide (InPath q v)))).length ≤ oddSide.length - 49 := by
  have hb := absent_side_bound q true oddSide (fun v hv hp => odd_mem v (h.covered v hv) hp)
  exact hb

theorem absent_even_bound (q : Snake 97) (h : Conditions q) :
    (evenSide.filter (fun v => !(decide (InPath q v)))).length ≤ evenSide.length - 49 := by
  have hb := absent_side_bound q false evenSide (fun v hv hp => even_mem v (h.covered v hv) hp)
  exact hb

theorem other_count_bound (q : Snake 97) (h : Conditions q) :
    (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length ≤ 1 := by
  apply endpoint_count q others others_nodup
  rw [h.head_fixed]
  exact head_not_others
'''
# Bound elaboration memory by compiling declarations in separate modules.
body=s.removeprefix('import First96Data\n'+header)
declarations=re.split(r'(?=^(?:def|theorem|structure) )',body,flags=re.MULTILINE)
declarations=[x for x in declarations if x.strip()]
previous='First96Data'
semantic_modules=[]
for offset in range(0,len(declarations),24):
    name=f'First96SemanticsPart{offset//24:04d}'
    write(name,'import '+previous+'\n'+header.replace('instance propDec ',f'instance semDec{offset//24} ')+''.join(declarations[offset:offset+24])+footer)
    semantic_modules.append(name.replace('First96',PN))
    previous=name
write('First96Semantics','import '+previous+'\n')
(DEST/(PN+'Semantics.modules.json')).write_text(json.dumps(semantic_modules),encoding='utf-8')

def cntexpr(w):
    return f'{countof[w]} q' if w>2*N else f'countLit q [{w}]'
def vexpr(v): return f'({v} : Vertex)'
def clauseproof(num,clause,r):
    goal=' ∨ '.join(f'valuation q {abs(v)} = {"true" if v>0 else "false"}' for v in clause)
    out=f'theorem clause{num} (q : Snake 97) (h : Conditions q) : {goal} := by\n'
    kind=r['kind']
    if kind=='counter_merge':
        i,j=r['i'],r['j']; ow=r['outputs'][i+j-1]
        # The metadata records complete leaves independently of truncated wires.
        def leaves(w):return leavesof[w] if w>2*N else [w]
        L=leaves(r['left'][0]); RR=leaves(r['right'][0])
        A=f'countLit q {lst(L)}';B=f'countLit q {lst(RR)}';C=f'{countof[ow]} q'
        out+=f'  have hs : {C} = ({A}) + ({B}) := List.countP_append (p := literal (baseVal q)) (l₁ := {lst(L)}) (l₂ := {lst(RR)})\n'
        l=r['left'][i-1] if i else None;rr=r['right'][j-1] if j else None
        lit=lambda w:f'(literal (valuation q) ({w}))'
        if i and j:
            out+=f'  have hm := merge_two {lit(l)} {lit(rr)} {lit(ow)} ({A}) ({B}) ({C}) {i} {j} ({meaning(l)} q) ({meaning(rr)} q) ({meaning(ow)} q) hs\n'
        elif i:
            out+=f'  have hm := merge_left {lit(l)} {lit(ow)} ({A}) ({B}) ({C}) {i} ({meaning(l)} q) ({meaning(ow)} q) hs\n'
        else:
            out+=f'  have hm := merge_right {lit(rr)} {lit(ow)} ({A}) ({B}) ({C}) {j} ({meaning(rr)} q) ({meaning(ow)} q) hs\n'
        neg=lambda w:(f'(! (valuation q {abs(w)})) = false' if w<0 else f'valuation q {w} = false')
        hmgoal=' ∨ '.join([neg(w) for w in (l,rr) if w is not None]+[f'valuation q {ow} = true'])
        out+=f'  change {hmgoal} at hm\n'
        if any(w is not None and w<0 for w in (l,rr)):
            out+="  simpa only [Bool.not_eq_false'] using hm\n"
        else:
            out+='  simpa only [Bool.not_eq_false] using hm\n'
        out=out.replace(f'theorem clause{num} (q : Snake 97) (h : Conditions q)',f'theorem counterClause{num} (q : Nat → Bool)')
        out=out.replace('(baseVal q)','q').replace('valuation q','valuationOf q')
        out+=f'\ntheorem clause{num} (q : Snake 97) (h : Conditions q) : {goal} := counterClause{num} (baseVal q)\n'
        return out
    out+='  rw ['+', '.join(f'value{w}' for w in sorted(set(abs(v) for v in clause)))+']\n'
    out+='  simp only [decide_eq_true_eq, decide_eq_false_iff_not]\n'
    if kind=='degree_two':
        out+='  exact BallClauseLogic.degree_clause q '+' '.join(vexpr(v) for v in r['vertices'])+' '+ ' '.join(['(by decide)']*6)+'\n'
    elif kind=='endpoint_degree_one':
        out+='  exact BallClauseLogic.endpoint_degree_clause q '+' '.join(vexpr(v) for v in r['vertices'])+' '+' '.join(['(by decide)']*3)+'\n'
    elif kind=='endpoint_selected':
        v=r['vertex'];out+=f'  by_cases he : BallClauseLogic.Endpoint q {vexpr(v)}\n  · exact Or.inr he.1\n  · exact Or.inl he\n'
    elif kind in ('other_neighbor','neighbor_exists'):
        v=r['vertex'];ns=r['neighbors']
        if kind=='other_neighbor': ns=[x for x in ns if x!=r['excluded']]
        nlist=verts(ns)
        out+=f'  have hc : ∀ w : Vertex, Adj {vexpr(v)} w → w ∈ region → '
        if kind=='other_neighbor':out+=f'w ≠ {vexpr(r["excluded"])} → '
        out+=f'w ∈ {nlist} := by decide\n'
        if kind=='other_neighbor':
            out+=f'  have hg := other_cover q {vexpr(v)} {vexpr(r["excluded"])} {nlist} (fun w hw ha he => hc w ha (h.covered w hw) he)\n'
        else:
            out+=f'  have hg := neighbor_cover q (by decide) {vexpr(v)} {nlist} (fun w hw ha => hc w ha (h.covered w hw))\n'
        out+='  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg\n'
    elif kind=='head_selected':
        out+='  change InPath q head\n  rw [← h.head_fixed]\n  exact ⟨0,rfl⟩\n'
    elif kind=='head_endpoint':
        out+='  change BallClauseLogic.Endpoint q head\n  exact (endpoint_iff q head).mpr (Or.inl h.head_fixed.symm)\n'
    elif kind=='endpoint_parity':
        out+=f'  apply endpoint_parity_exclude q {vexpr(r["vertex"])}\n  · rw [h.head_fixed]; decide\n  · rw [h.head_fixed]; decide\n'
    elif kind=='other_endpoint_exists':
        out+='  have hg := other_endpoint q others (fun v hv hn => others_mem v (h.covered v hv) (by simpa only [h.head_fixed] using hn))\n'
        out+='  simpa only [others, List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg\n'
    elif kind=='square':
        out+='  exact square_clause q '+' '.join(vexpr(v) for v in r['vertices'])+' '+' '.join(['(by decide)']*6)+'\n'
    elif kind=='counter_bound':
        wire=abs(clause[0]);name=countof[wire]
        if r['label']=='other_endpoints':
            out+=f'  have he : {name} (baseVal q) = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by\n'
            out+='    rw [← List.countP_eq_length_filter]\n    rfl\n'
            out+='  have hb := other_count_bound q h\n'
        elif r['label']=='absent_parity_1':
            out+=f'  have he : {name} (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by\n'
            out+='    rw [← List.countP_eq_length_filter]\n    rfl\n'
            out+='  have hb := absent_odd_bound q h\n'
            out+='  rw [oddSide_length] at hb\n'
        elif r['label']=='absent_parity_0':
            out+=f'  have he : {name} (baseVal q) = (evenSide.filter (fun v => !(decide (InPath q v)))).length := by\n'
            out+='    rw [← List.countP_eq_length_filter]\n    rfl\n'
            out+='  have hb := absent_even_bound q h\n'
            out+='  rw [evenSide_length] at hb\n'
        elif r['label'] in ('selected_parity_0','selected_parity_1'):
            side='oddSide' if r['label'].endswith('1') else 'evenSide'
            parity='true' if r['label'].endswith('1') else 'false'
            out+=f'  have he : {name} (baseVal q) = ({side}.filter (fun v => decide (InPath q v))).length := by\n'
            out+='    rw [← List.countP_eq_length_filter]\n    rfl\n'
            out+=f'  have hb := selected_side_bound q {parity} {side} (by decide) (by decide)\n'
        else:raise ValueError(r)
        out+='  rw [he]\n  omega\n'
    else:raise ValueError(r)
    return out

for block in range((len(core['clauses'])+31)//32):
    s='import First96Semantics\nimport Dfs96FirstBooleanInputs\n'+header.replace('instance propDec ',f'instance blockDec{block} ')
    for k in range(block*32,min((block+1)*32,len(core['clauses']))):
        r=d['reasons'][core['original_clause_indices'][k]-1]
        s+=clauseproof(k+1,core['clauses'][k],r)+'\n'
    s+=f'theorem block{block} (q : Snake 97) (h : Conditions q) : Dfs96FirstBoolean.Block{block} (valuation q) :=\n'
    s+='  ⟨'+', '.join(f'clause{k+1} q h' for k in range(block*32,min((block+1)*32,len(core['clauses']))))+'⟩\n'
    write(f'First96Clauses{block:02d}',s+footer)

s='import Dfs96FirstBoolean\n'+''.join(f'import First96Clauses{b:02d}\n' for b in range(BLOCKS))+header.replace('instance propDec ','instance completeDec ')
s+='''theorem all_constraints (q : Snake 97) (h : Conditions q) :
    Dfs96FirstBoolean.Constraints (valuation q) :=
'''
s+='  ⟨'+', '.join(f'block{b} q h' for b in range(BLOCKS))+'⟩\n'
s+='''
theorem region_exclusion (q : Snake 97) (h : Conditions q) : False :=
  Dfs96FirstBoolean.constraints_unsat (valuation q) (all_constraints q h)

/-- Fixing these first 96 vertices excludes 192 edges. -/
theorem no192 (p : Snake 192) (hp : Dfs.StartsWith p pre 96) : False := by
  have hc : Conditions (suffix p) := ⟨suffix_head p hp, suffix_covered p hp⟩
  exact Dfs96FirstBoolean.constraints_unsat (valuation (suffix p)) (all_constraints _ hc)

theorem no_long_prefix {m : Nat} (hm : 192 ≤ m) (p : Snake m) :
    ¬ Dfs.StartsWith p pre 96 := by
  intro hp
  apply no192 (takePrefix p hm)
  intro i hi h193
  exact hp i hi (by omega)

theorem no_long_suffix {m : Nat} (hm : 192 ≤ m) (p : Snake m) :
    ¬ Dfs.EndsWith p pre 96 := no_long_prefix hm (reverseSnake p)

#print axioms no192
#print axioms no_long_prefix
#print axioms no_long_suffix
#print axioms region_exclusion
'''
write('First96Complete',s+footer)

