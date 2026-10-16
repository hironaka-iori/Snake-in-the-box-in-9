"""Emit proof obligations and concrete data; all claims are checked by Lean."""
import json,sys,re
from pathlib import Path
from collections import Counter
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'work'))
from build_regrowth_cnf import encode
path=json.loads((ROOT/'work/bank9.json').read_text())[0]['vertex_sequence']
d=encode(path)
core=json.loads((ROOT/'work/lean/totalizer_plain_core.json').read_text())
assert [d['clauses'][i-1] for i in core['original_clause_indices']]==core['clauses']
def lst(xs): return '['+', '.join(map(str,xs))+']'
def verts(xs): return '['+', '.join(f'({x} : Vertex)' for x in xs)+']'
def write(name,s): (HERE/(name+'.lean')).write_text(re.sub(r'\bprefix\b','pre',s),encoding='utf-8')
ban=sum(1<<v for v in d['banned']); R=sum(1<<v for v in d['vertices'] if v!=d['head'])
write('First112Data',f'''import RegrowthBridge
namespace Snake9.Regrowth.First112
open Dfs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 600
def prefix : Array Nat := #{lst(d['prefix'])}
def region : List Vertex := {verts(d['vertices'])}
def oddSide : List Vertex := {verts([v for v in d['vertices'] if v.bit_count()%2])}
def others : List Vertex := {verts([v for v in d['vertices'] if v!=d['head']])}
def head : Vertex := {d['head']}
def ban : Nat := {ban}
def reachable : Nat := {R}
theorem ban_eq : banFrom (fun i => prefix[i]!) 111 = ban := by decide
theorem head_eq : prefix[111]! = head.val := by decide
theorem region_closed : expand reachable &&& freeOf ban = reachable := by decide
theorem region_start : ∀ y : Fin 512,
    (expand (2^head.val) &&& freeOf ban).testBit y.val = true →
    reachable.testBit y.val = true := by decide
theorem region_mem : ∀ v : Vertex,
    v = head ∨ reachable.testBit v.val = true → v ∈ region := by decide
theorem odd_mem : ∀ v : Vertex, v ∈ region → bitParity v.val = true → v ∈ oddSide := by decide
theorem others_mem : ∀ v : Vertex, v ∈ region → v ≠ head → v ∈ others := by decide
theorem others_nodup : others.Nodup := by decide
theorem head_not_others : head ∉ others := by decide
theorem oddSide_length : oddSide.length = 63 := by decide

theorem suffix_head (p : Snake 192) (hp : StartsWith p prefix 112) :
    (suffix p).vertex 0 = head := by
  apply Fin.ext
  exact (hp 111 (by decide) (by decide)).trans head_eq

theorem suffix_covered (p : Snake 192) (hp : StartsWith p prefix 112) :
    ∀ v, InPath (suffix p) v → v ∈ region := by
  have hb : banFrom (vals p) 111 = ban := by
    rw [← ban_eq]
    apply banFrom_congr
    intro i hi
    have hi' : i < 193 := by omega
    simpa only [vals, dif_pos hi'] using hp i (by omega) hi'
  have hh : vals p 111 = head.val := by
    exact congrArg Fin.val (suffix_head p hp)
  have hv := tail_valid p 81 111 (by decide)
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
    have he : 111+1+(i.val-1) = 111+i.val := by omega
    simp only [he,vals,dif_pos (show 111+i.val < 193 by omega),suffix]

end Snake9.Regrowth.First112
''')
print('Wrote First112Data; core clause kinds:',dict(Counter(d['reasons'][i-1]['kind'] for i in core['original_clause_indices'])))

header='''namespace Snake9.Regrowth.First112
noncomputable section
local instance propDec (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
'''
footer='\nend\nend Snake9.Regrowth.First112\n'
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
expr=base+[f'decide ({threshold[w]} ≤ {countof[w]} q)' for w in range(2*N+1,d['variables']+1)]
s='import First112Data\n'+header
s+='def baseVal (q : Snake 81) (i : Nat) : Bool := '+lookup_tree(base)+'\n'
s+='def countLit (q : Snake 81) (xs : List Int) : Nat := xs.countP (literal (baseVal q))\n'
for c in d['counters']:
    s+=f'def {countof[c["outputs"][0]]} (q : Snake 81) : Nat := countLit q {lst(c["leaves"])}\n'
s+='def valuation (q : Snake 81) (i : Nat) : Bool := '+lookup_tree(expr)+'\n'
used=set(abs(lit) for c in core['clauses'] for lit in c)
for w in sorted(used):
    s+=f'theorem value{w} (q : Snake 81) : valuation q {w} = {expr[w]} := rfl\n'
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
        s+=f'''theorem {meaning(w)} (q : Snake 81) : literal (valuation q) ({w}) = decide (1 ≤ countLit q [{w}]) := by
  change literal (baseVal q) ({w}) = decide (1 ≤ countLit q [{w}])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal (baseVal q) ({w}) <;> decide
'''
    else:
        s+=f'theorem {meaning(w)} (q : Snake 81) : literal (valuation q) {w} = decide ({threshold[w]} ≤ {countof[w]} q) := rfl\n'
s+='''structure Conditions (q : Snake 81) : Prop where
  head_fixed : q.vertex 0 = head
  covered : ∀ v, InPath q v → v ∈ region

theorem absent_odd_bound (q : Snake 81) (h : Conditions q) :
    (oddSide.filter (fun v => !(decide (InPath q v)))).length ≤ 22 := by
  have hb := absent_bound q oddSide (fun v hv hp => odd_mem v (h.covered v hv) hp)
  rw [oddSide_length] at hb
  exact hb

theorem other_count_bound (q : Snake 81) (h : Conditions q) :
    (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length ≤ 1 := by
  apply endpoint_count q others others_nodup
  rw [h.head_fixed]
  exact head_not_others
'''
write('First112Semantics',s+footer)

def cntexpr(w):
    return f'{countof[w]} q' if w>2*N else f'countLit q [{w}]'
def vexpr(v): return f'({v} : Vertex)'
def clauseproof(num,clause,r):
    goal=' ∨ '.join(f'valuation q {abs(v)} = {"true" if v>0 else "false"}' for v in clause)
    out=f'theorem clause{num} (q : Snake 81) (h : Conditions q) : {goal} := by\n'
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
        out+='  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg\n'
    elif kind=='head_selected':
        out+='  change InPath q head\n  rw [← h.head_fixed]\n  exact ⟨0,rfl⟩\n'
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
            out+=f'  have he : {name} q = (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length := by\n'
            out+='    rw [← List.countP_eq_length_filter]\n    rfl\n'
            out+='  have hb := other_count_bound q h\n'
        elif r['label']=='absent_parity_1':
            out+=f'  have he : {name} q = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by\n'
            out+='    rw [← List.countP_eq_length_filter]\n    rfl\n'
            out+='  have hb := absent_odd_bound q h\n'
        else:raise ValueError(r)
        out+='  rw [he]\n  omega\n'
    else:raise ValueError(r)
    return out

for block in range((len(core['clauses'])+31)//32):
    s='import First112Semantics\nimport Dfs112FirstBooleanInputs\n'+header.replace('instance propDec ',f'instance blockDec{block} ')
    for k in range(block*32,min((block+1)*32,len(core['clauses']))):
        r=d['reasons'][core['original_clause_indices'][k]-1]
        s+=clauseproof(k+1,core['clauses'][k],r)+'\n'
    s+=f'theorem block{block} (q : Snake 81) (h : Conditions q) : Dfs112FirstBoolean.Block{block} (valuation q) :=\n'
    s+='  ⟨'+', '.join(f'clause{k+1} q h' for k in range(block*32,min((block+1)*32,len(core['clauses']))))+'⟩\n'
    write(f'First112Clauses{block:02d}',s+footer)

s='import Dfs112FirstBoolean\n'+''.join(f'import First112Clauses{b:02d}\n' for b in range(49))+header.replace('instance propDec ','instance completeDec ')
s+='''theorem all_constraints (q : Snake 81) (h : Conditions q) :
    Dfs112FirstBoolean.Constraints (valuation q) :=
'''
s+='  ⟨'+', '.join(f'block{b} q h' for b in range(49))+'⟩\n'
s+='''
/-- Fixing the first 112 vertices of the first bank path excludes 192 edges. -/
theorem no192 (p : Snake 192) (hp : Dfs.StartsWith p pre 112) : False := by
  have hc : Conditions (suffix p) := ⟨suffix_head p hp, suffix_covered p hp⟩
  exact Dfs112FirstBoolean.constraints_unsat (valuation (suffix p)) (all_constraints _ hc)

theorem no_long_prefix {m : Nat} (hm : 192 ≤ m) (p : Snake m) :
    ¬ Dfs.StartsWith p pre 112 := by
  intro hp
  apply no192 (takePrefix p hm)
  intro i hi h193
  exact hp i hi (by omega)

theorem no_long_suffix {m : Nat} (hm : 192 ≤ m) (p : Snake m) :
    ¬ Dfs.EndsWith p pre 112 := no_long_prefix hm (reverseSnake p)

#print axioms no192
#print axioms no_long_prefix
#print axioms no_long_suffix
'''
write('First112Complete',s+footer)
