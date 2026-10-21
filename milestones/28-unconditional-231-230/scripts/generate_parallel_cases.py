"""General exact-core applicability exporter with checked clause shards.

Reads immutable, hash-validated cores already prepared by kernel_batch.py.
It does not rerun SAT search, modify the Boolean batch, or assume its completion.
"""
import argparse
import collections
import importlib.util
import json
from pathlib import Path
import runner
from generate_parallel_pilot import load_encoding,term,ref_expr
from generate_gate_pilot import square

HERE=runner.HERE
ROOT=runner.ROOT
KERNEL=HERE/'runtime/kernel'

def meaning_tree(values,nv):
    def build(r,s):
        if r+s>nv:return '(.leaf '+('(some '+values[r]+')' if r in values else 'none')+')'
        return f'(.node {build(r,2*s)} {build(r+s,2*s)})'
    return build(0,1)

def generate(index,out,chunk=128):
    out=Path(out);case=KERNEL/'cases'/f'{index:02d}'
    ready=runner.read(case/'ready.json');mod=f'ParallelShare{index:02d}'
    for p,h in ready['artifacts'].items():assert runner.digest(case/p)==h,p
    core_path=KERNEL/'src/LocalWindowCnf'/(mod+'.lean')
    core_rel='LocalWindowCnf/'+mod+'.lean'
    assert runner.digest(core_path)==ready['generated_files'][core_rel]
    meta_path=case/f'parallel_share_{index:02d}.json';meta=runner.read(meta_path)
    manifest=runner.read(HERE/'runtime/manifest.json');rec=manifest['cases'][index]
    for file,h in meta['source_hashes'].items():assert runner.digest(HERE/'build/frozen/cases'/f'{index:02d}'/file)==h
    cls,window_from_dirs,encoder=load_encoding();window=window_from_dirs(rec['dirs'])
    enc=cls(window,[(0,21)]*6,3,20,counter='stot',exact=True)
    cuts=runner.read(HERE/'build/frozen/upstream/data/share/final_a_X20.jsonl.cuts.json')
    for cut in cuts[','.join(map(str,rec['dirs']))]:enc.add_cycle_cut(cut)
    cnf=(f'p cnf {enc.nv} {len(enc.clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in enc.clauses)).encode('ascii')
    assert runner.hashbytes(cnf)==rec['cnf_sha256']==meta['source_hashes']['model.cnf']
    gp=ROOT/'milestones/10-window-aggregate/scripts/gen_lean_sat.py'
    spec=importlib.util.spec_from_file_location('legacy_clause_trace',gp);gen=importlib.util.module_from_spec(spec);spec.loader.exec_module(gen)
    old=gen.TaggedEncoding(window,[(0,21)]*6,radius=3)
    assert old.clauses==enc.clauses[:enc.n_base]
    ids=list(meta['original_variable_ids']);inverse={v:i+1 for i,v in enumerate(ids)}
    raw=[[gen.code((1 if v>0 else -1)*inverse[abs(v)]) for v in enc.clauses[ci-1]] for ci in meta['original_clause_ids']]
    body=core_path.read_text().split('noncomputable def raw : List (List Nat) := ',1)[1].split('\n',1)[0]
    assert raw==json.loads(body)
    # Counter inputs absent from the proof core still need meanings. Give them
    # fresh compact IDs beyond all IDs used by the Boolean refutation.
    for lits,k,kind in old.ctrs:
        for v in lits:
            if abs(v) not in inverse:
                ids.append(abs(v));inverse[abs(v)]=len(ids)
    old_meanings={inverse[x]:m for x,m in old.meaning.items() if x in inverse}
    ctrs=[]
    for lits,k,kind in old.ctrs:
        kt='.ends' if kind[0]=='ends' else f'(.{kind[0]} {kind[1]})'
        nums=[gen.code((1 if v>0 else -1)*inverse[abs(v)]) for v in lits]
        ctrs.append(f'⟨{nums}, {k}, {kt}⟩')
    terms=[term(*row) for row in enc.trace_terms]
    meanings={v:f'(.boolean (.sel {q}))' for q,v in enc.var.items()}
    meanings.update({v:f'(.boolean {square(q)})' for q,v in enc.esq.items()})
    for v,(kind,q,p) in enc.gvars.items():meanings[v]=f'(.boolean ({kind} {square(q)} '+' '.join(map(str,p))+'))'
    for v,(lo,hi,s) in enc.total_info.items():meanings[v]=f'(.total ⟨{lo}, {hi}, {s}⟩)'
    meanings={inverse[v]:m for v,m in meanings.items() if v in inverse}
    tags=[]
    for ci in meta['original_clause_ids']:
        i=ci-1;kind=enc.kinds[i]
        if i<enc.n_base:tags.append('(.old '+gen.lean_tag(old.tags[i])+')')
        elif kind in ['empty->unselected','selected_or_empty','g1_def','g3_def']:tags.append('.boolean')
        elif kind=='tot':
            a,b=enc.merge_refs[i];tags.append(f'(.merge {ref_expr(a)} {ref_expr(b)})')
        elif kind=='stot_bound':tags.append('.bound')
        elif kind=='cycle_cut':
            vertices={v:q for q,v in enc.var.items()}
            assert all(v<0 and -v in vertices for v in enc.clauses[i])
            assert gen.is_cycle_set([vertices[-v] for v in enc.clauses[i]])
            tags.append('(.old .cut)')
        else:raise RuntimeError((i,kind))
    ns=f'Snake9.LocalWindow.{mod}Applicability';prefix=f'ParallelShareApplicability.{mod}'
    header='set_option maxRecDepth 200000\nset_option maxHeartbeats 0\n'
    opened='open Snake9.ParallelShareBoolean Snake9.ParallelShareBlocks Snake9.ParallelShareClauses\nopen Snake9.ParallelShareCertificate\n'
    definitions=f'''import ParallelShareCertificateBatch
import LocalWindowCnf.{mod}
{header}
namespace {ns}
{opened}
def window : List Nat := {window}
def bounds : List (Nat × Nat) := List.replicate 6 (0, 21)
def oldMeaning : Tags.MT := {gen.lean_tree_terms(old_meanings,len(ids))}
def ctrs : List Tags.Ctr := [{', '.join(ctrs)}]
def terms : List Term := [{', '.join('⟨'+', '.join(map(str,t))+'⟩' for t in terms)}]
def meaningTree : MeaningTree := {meaning_tree(meanings,len(ids))}
def meaning (n : Nat) : Option Meaning := meaningTree.get n

theorem countersChecked : ctrs.all (Tags.ctrOK oldMeaning (Tags.centresK window bounds)) = true := by decide +kernel
theorem termsChecked : sublist terms (allTerms (Tags.centresK window bounds)) = true := by decide +kernel
'''
    pieces=[]
    for k,start in enumerate(range(0,len(raw),chunk)):
        pieces.append((tags[start:start+chunk],raw[start:start+chunk]))
        definitions+=f'\ndef tags{k} : List ParallelShareCertificate.Tag := [{", ".join(pieces[-1][0])}]\ndef raw{k} : List (List Nat) := {pieces[-1][1]}\n'
    definitions+=f'\nend {ns}\n'
    outputs={core_rel:core_path.read_bytes(),prefix.replace('.','/')+'/Data.lean':definitions.encode()}
    for k in range(len(pieces)):
        code=f'''import {prefix}.Data
{header}
namespace {ns}
{opened}
theorem check{k} : checkRaw oldMeaning ctrs window terms meaning 20 tags{k} raw{k} = true := by decide +kernel
end {ns}
'''
        outputs[prefix.replace('.','/')+f'/Check{k}.lean']=code.encode()
    partlist='['+', '.join(f'(tags{k}, raw{k})' for k in range(len(pieces)))+']'
    branches=' | '.join('rfl' for _ in pieces)
    proofs='\n'.join(f'  · exact check{k}' for k in range(len(pieces)))
    imports='\n'.join(f'import {prefix}.Check{k}' for k in range(len(pieces)))
    final=f'''{imports}
{header}
namespace {ns}
{opened}
def parts : List (List ParallelShareCertificate.Tag × List (List Nat)) := {partlist}
def tags : List ParallelShareCertificate.Tag := parts.flatMap Prod.fst
theorem exact_raw : parts.flatMap Prod.snd = {mod}.raw := by decide +kernel
theorem checkedRaw : checkRaw oldMeaning ctrs window terms meaning 20 tags {mod}.raw = true := by
  rw [← exact_raw]
  apply checkRaw_flatMap
  intro p hp
  simp only [parts, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with {branches}
{proofs}
theorem checked : checkAll oldMeaning ctrs window bounds terms meaning 20 tags {mod}.raw = true := by
  simp only [checkAll, countersChecked, termsChecked, checkedRaw, Bool.true_and]
theorem sat (S E : Nat → Bool) (ax : AxiomsP S E window (centresOf window bounds) 20) :
    ∃ tau, cnfTrue tau {mod}.cnf = true :=
  ⟨ParallelShareClauses.assignment (Tags.tau S E oldMeaning ctrs) S terms meaning,
    sound oldMeaning ctrs window bounds terms meaning 20 tags {mod}.raw checked S E ax⟩
theorem refuted_of_unsat (hu : Unsat {mod}.cnf) : RefutedParallel window bounds 20 :=
  refuted_of_check oldMeaning ctrs window bounds terms meaning 20 tags {mod}.raw checked hu
#print axioms sat
#print axioms refuted_of_unsat
end {ns}
'''
    outputs[prefix.replace('.','/')+'.lean']=final.encode()
    for rel,data in outputs.items():
        p=out/rel;p.parent.mkdir(parents=True,exist_ok=True)
        if p.exists():assert p.read_bytes()==data,('changed generated source',p)
        else:p.write_bytes(data)
    return dict(index=index,target=prefix,clauses=len(raw),terms=len(terms),core_variables=len(meta['original_variable_ids']),
        assignment_variables=len(ids),chunks=len(pieces),families=dict(collections.Counter(enc.kinds[i-1] for i in meta['original_clause_ids'])),
        source_hashes=meta['source_hashes'],mapping_sha256=runner.digest(meta_path),core_sha256=runner.digest(core_path),
        generated_files={r:runner.hashbytes(d) for r,d in outputs.items()},generated_at=runner.now())

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--index',type=int,required=True);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--chunk',type=int,default=128)
    a=ap.parse_args();r=generate(a.index,a.out,a.chunk);runner.atomic(a.out/f'generation-{a.index:02d}.json',r)
    print(json.dumps({k:v for k,v in r.items() if k!='generated_files'}))
