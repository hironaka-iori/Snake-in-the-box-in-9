"""Trace exact share leaves/merges and emit a full geometric pilot certificate.

Trace data is untrusted: ParallelShareCertificate checks every clause and the
entire term sublist in Lean. The exact original CNF and compact core are matched.
"""
import collections
from dataclasses import dataclass
import importlib.util
import json
import sys
import runner
from generate_gate_pilot import square

HERE=runner.HERE
ROOT=runner.ROOT

@dataclass
class Node:
    bits:list
    lo:int
    hi:int
    leaf:bool=False
    def ref(self,s):
        return ('leaf',self.lo,s) if self.leaf else ('total',)

def load_encoding():
    src=HERE/'build/frozen/upstream/scripts/share_enc.py'
    text=src.read_text(encoding='utf-8')
    for g,kind in [('g1','one'),('g3','zero')]:
        old=f'{g} = self.fresh()';assert text.count(old)==1
        text=text.replace(old,old+f'; self.gvars[{g}] = ("{kind}", Q, P)')
    old='self.terms = []';assert text.count(old)==1
    text=text.replace(old,'self.trace_terms = []; self.terms = []')
    old='self.terms.append((ci, bits))';assert text.count(old)==1
    text=text.replace(old,old+'; self.trace_terms.append((ci, c, Q, P, bits))')
    sys.path.insert(0,str(src.parent))
    ns={'__name__':'parallel_full_trace','__file__':str(src)}
    exec(compile(text,str(src),'exec'),ns)
    base=ns['ShareEncoding']
    def counter(self,bound):
        self.total_info={};self.merge_refs={};cap=bound+1
        def merge(a,b):
            assert a.hi==b.lo
            start=len(self.clauses)
            out=base._merge(self,a.bits,b.bits,cap)
            for s,x in enumerate(out,1):self.total_info[x]=(a.lo,b.hi,s)
            offset=0
            for i in range(len(a.bits)+1):
                for j in range(len(b.bits)+1):
                    if i+j==0:continue
                    clause=([-a.bits[i-1]] if i else [])+([-b.bits[j-1]] if j else [])+[out[min(i+j,cap)-1]]
                    assert self.clauses[start+offset]==clause
                    refs=([a.ref(i)] if i else [])+([b.ref(j)] if j else [])
                    self.merge_refs[start+offset]=(refs+[('total',)])[:2]
                    offset+=1
            assert len(self.clauses)==start+offset
            return Node(out,a.lo,b.hi)
        acc=None;position=0
        for ci in range(len(self.window)-2):
            begin=position;nodes=[]
            for centre,bits in self.terms:
                if centre==ci:
                    nodes.append(Node(bits[:cap],position,position+1,True));position+=1
            while len(nodes)>1:
                nxt=[merge(nodes[i],nodes[i+1]) for i in range(0,len(nodes)-1,2)]
                if len(nodes)%2:nxt.append(nodes[-1])
                nodes=nxt
            u=nodes[0] if nodes else Node([],begin,begin)
            acc=u if acc is None else merge(acc,u)
            if len(acc.bits)>=cap:
                self.add([-acc.bits[cap-1]],'stot_bound')
                acc=Node(acc.bits[:cap-1],acc.lo,acc.hi)
        assert position==len(self.terms)
    traced=type('TracedShareEncoding',(base,),{'cnt_stot':counter})
    return traced,ns['window_from_dirs'],src

def term(ci,c,q,p,bits):
    a=(c^p[0]).bit_length()-1;b=(c^p[1]).bit_length()-1
    assert a<b and p==(c^(1<<a),c^(1<<b),c^(1<<a)^(1<<b))
    ks=[k for k in range(9) if k not in [a,b] and c^(1<<k) in q]
    assert len(ks)==1
    k=ks[0];y=c^(1<<k)
    assert sorted(q)==sorted([y,y^(1<<a),y^(1<<b),y^(1<<a)^(1<<b)])
    return c,k,a,b

def ref_expr(ref):
    return '.total' if ref[0]=='total' else f'(.leaf {ref[1]} {ref[2]})'

def main():
    manifest=runner.read(HERE/'runtime/manifest.json');runner.validate(manifest)
    cls,window_from_dirs,encoder=load_encoding();rec=manifest['cases'][1]
    window=window_from_dirs(rec['dirs']);enc=cls(window,[(0,21)]*6,3,20,counter='stot',exact=True)
    cuts=runner.read(HERE/'build/frozen/upstream/data/share/final_a_X20.jsonl.cuts.json')
    for cut in cuts[','.join(map(str,rec['dirs']))]:enc.add_cycle_cut(cut)
    cnf=(f'p cnf {enc.nv} {len(enc.clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in enc.clauses)).encode('ascii')
    assert runner.hashbytes(cnf)==rec['cnf_sha256']
    genpath=ROOT/'milestones/10-window-aggregate/scripts/gen_lean_sat.py'
    spec=importlib.util.spec_from_file_location('old_window_trace',genpath);gen=importlib.util.module_from_spec(spec);spec.loader.exec_module(gen)
    old=gen.TaggedEncoding(window,[(0,21)]*6,radius=3)
    assert old.clauses==enc.clauses[:enc.n_base]
    mapping=runner.read(HERE/'data/kernel-pilot-01-mapping.json')
    ids=mapping['original_variable_ids'];inverse={v:i+1 for i,v in enumerate(ids)}
    compact=[[gen.code((1 if v>0 else -1)*inverse[abs(v)]) for v in enc.clauses[ci-1]] for ci in mapping['original_clause_ids']]
    core_path=HERE/'lean/LocalWindowCnf/ParallelShare01.lean'
    body=core_path.read_text().split('noncomputable def raw : List (List Nat) := ',1)[1].split('\n',1)[0]
    assert compact==json.loads(body)
    # The pilot has no endpoint-register clauses. Keep the original primary map.
    old_meanings={inverse[x]:m for x,m in old.meaning.items() if x in inverse}
    assert all(m[0]=='p' for m in old_meanings.values())
    terms=[term(*row) for row in enc.trace_terms]
    meanings={v:f'(.boolean (.sel {q}))' for q,v in enc.var.items()}
    meanings.update({v:f'(.boolean {square(q)})' for q,v in enc.esq.items()})
    for v,(kind,q,p) in enc.gvars.items():meanings[v]=f'(.boolean ({kind} {square(q)} '+' '.join(map(str,p))+'))'
    for v,(lo,hi,s) in enc.total_info.items():meanings[v]=f'(.total ⟨{lo}, {hi}, {s}⟩)'
    tags=[]
    for ci in mapping['original_clause_ids']:
        i=ci-1;kind=enc.kinds[i]
        if i<enc.n_base:
            assert old.tags[i][0] in ['window','deg2'];tags.append('(.old '+gen.lean_tag(old.tags[i])+')')
        elif kind in ['empty->unselected','selected_or_empty','g1_def','g3_def']:tags.append('.boolean')
        elif kind=='tot':
            a,b=enc.merge_refs[i];tags.append(f'(.merge {ref_expr(a)} {ref_expr(b)})')
        elif kind=='stot_bound':tags.append('.bound')
        else:raise RuntimeError((i,kind))
    mean='['+', '.join('some '+meanings[v] if v in meanings else 'none' for v in ids)+']'
    termlist='['+', '.join('⟨'+', '.join(map(str,t))+'⟩' for t in terms)+']'
    source=f'''import ParallelShareCertificate
import LocalWindowUnsat.ParallelShare01

/-! Full geometric applicability for all 81 clauses of the frozen pilot core.
All table data is checked in the Lean kernel under a single assignment. -/
namespace Snake9.LocalWindow.ParallelShare01Certificate
open Snake9.ParallelShareBoolean Snake9.ParallelShareBlocks Snake9.ParallelShareClauses
open Snake9.ParallelShareCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def window : List Nat := {window}
def bounds : List (Nat × Nat) := List.replicate 6 (0, 21)
def oldMeaning : Tags.MT := {gen.lean_tree_terms(old_meanings,len(ids))}
def terms : List Term := {termlist}
def meanings : List (Option Meaning) := {mean}
def meaning (n : Nat) : Option Meaning := meanings.getD (n - 1) none
def tags : List ParallelShareCertificate.Tag := [{', '.join(tags)}]

theorem checked : checkAll oldMeaning [] window bounds terms meaning 20 tags ParallelShare01.raw = true :=
  by decide +kernel

theorem refuted : RefutedParallel window bounds 20 :=
  refuted_of_check oldMeaning [] window bounds terms meaning 20 tags ParallelShare01.raw
    checked ParallelShare01.unsat

#print axioms checked
#print axioms refuted
end Snake9.LocalWindow.ParallelShare01Certificate
'''
    dest=HERE/'lean/LocalWindowSat/ParallelShare01.lean';dest.parent.mkdir(parents=True,exist_ok=True)
    dest.write_text(source,encoding='utf-8',newline='\n')
    receipt=dict(scope='Generated full applicability data; completion requires Lean checked and refuted',
        cnf_sha256=rec['cnf_sha256'],encoder_sha256=runner.digest(encoder),old_generator_sha256=runner.digest(genpath),
        generated_source_sha256=runner.digest(dest),core_source_sha256=runner.hashbytes(core_path.read_text().replace('\r\n','\n').encode()),
        mapping_sha256=runner.digest(HERE/'data/kernel-pilot-01-mapping.json'),terms=len(terms),core_clauses=len(tags),
        families=dict(collections.Counter(enc.kinds[i-1] for i in mapping['original_clause_ids'])),generated_at=runner.now())
    runner.atomic(HERE/'data/parallel-share-full-pilot-inputs.json',receipt);print(json.dumps(receipt))

if __name__=='__main__':main()
