"""Generate the bounded initial-tree pilot; full replay requires --full explicitly.

This script never compiles sources. The full mode enforces a source-byte cap and
must be used only after the emitted pilot has been accepted by Lean.
"""
from pathlib import Path
import argparse, gzip, json, re, struct
import sys, subprocess
OUT=Path(__file__).resolve().parents[1]
ROOT=OUT.parents[1]
sys.path.insert(0,str(ROOT/'milestones/153-pair-conditioned-share17/replay'))
import prepare_replay as p

H=p.HERE; LEAN=OUT/'lean'; NS='Snake9.ReplayData153'
BASE='Snake9.Lrat153Replay';FAST='Snake9.LratFast153Replay'
CNF='Snake9.LocalWindow.ShareWindow153'
OPTIONS='set_option maxRecDepth 100000\nset_option maxHeartbeats 0\nset_option Elab.async false\n'
PRED='(fun c => Snake9.LocalWindow.clauseTrue τ (c.map Snake9.LocalWindow.decodeLit))'
files={}; sourcepins={}

def emit(module,body):files[module]=body if body.endswith('\n') else body+'\n'
def read_old(rel):
    path=p.ROOT/rel;sourcepins[rel]=p.sha(path);return path.read_text(encoding='utf-8')
def copied(rel,replacements):
    text=read_old(rel)
    for a,b in replacements:text=text.replace(a,b)
    return text
def nums(xs):return '['+', '.join(str(x) for x in xs)+']'
def hexs(xs):return '['+',\n'.join('nat_lit 0x'+x for x in xs)+']'
def pack_rows():
    with (H/'data/packed-steps.bin').open('rb') as f:
        while True:
            n=f.read(4)
            if not n:break
            n=struct.unpack('<I',n)[0];b=f.read(n);assert len(b)==n
            yield format(int.from_bytes(b,'little'),'x')
def cp_values(receipt,segment):
    cp=next(c for c in receipt['checkpoints'] if c['before_segment']==segment)
    path=H/cp['path'];assert p.sha(path)==cp['sha256']
    with gzip.open(path,'rt',encoding='ascii') as f:return json.load(f)

def initial(s):
    base=copied('milestones/144-countfree-share18/lean/LratCheck144.lean',
                [('Snake9.Lrat144',BASE)])
    emit('LratCheck153Replay',base)
    fast=copied('milestones/144-countfree-share18/lean/LratFast144.lean',
                [('LratCheck144','LratCheck153Replay'),('Snake9.LratFast144',FAST),('Snake9.Lrat144',BASE)])
    assert s['tree_height']==14 and s['word_width']==14
    fast=fast.replace('Lrat144.seqT','Lrat153Replay.seqT')
    emit('LratFast153Replay',fast)
    emit('InputTree153Replay',copied('milestones/145-countfree-012301/lean/InputTree145.lean',
        [('LratFast144','LratFast153Replay'),('Snake9.Lrat144',BASE),('Snake9.InputTree145','Snake9.ReplayInput153')]))
    emit('ReplayTools153',copied('milestones/145-countfree-012301/lean/ChunkTruthTools145.lean',
        [('InputTree145','InputTree153Replay'),('Snake9.InputTree153Replay','Snake9.ReplayInput153'),
         ('ShareWindow144','ShareWindow153'),('Snake9.Lrat144',BASE),('Snake9.ChunkData145',NS)]))
    # Derive the chunk decomposition for this exact CNF length.
    chunk_count=(len(p.cnf(p.CORE))+127)//128
    chunk_body=['import ReplayTools153',OPTIONS,'namespace Snake9.ReplayRawChunks153',
        'theorem chunks_true (τ : Nat → Bool)',
        f'    (h : Snake9.LocalWindow.cnfTrue τ {CNF}.cnf = true) :',
        '    '+(' ∧\n    '.join(CNF+'.raw'+str(i)+'.all '+PRED+' = true' for i in range(chunk_count)))+' := by',
        '  simpa only ['+CNF+'.cnf, Snake9.LocalWindow.cnfTrue, List.all_map, '+CNF+'.raw,',
        '    List.all_append, Bool.and_eq_true, List.all_nil, and_true, and_assoc] using h',
        '#print axioms chunks_true','end Snake9.ReplayRawChunks153']
    emit('ReplayRawChunks153','\n'.join(chunk_body))
    core=p.cnf(p.CORE);raw=[[2*abs(x)+(x<0) for x in c] for c in core]
    parts=[];at=0
    def walk(d,b,extract=True):
        nonlocal at
        if d==0:return '.nil','.empty',f'{BASE}.TreeTrue.nil'
        if at>=len(raw):return f'(perf {d} {b})',f'(.tautology {d} {b})',f'({FAST}.perf_true τ {d} {b})'
        if d==7 and extract:
            pi=len(parts);start=at;parts.append(None)
            tree,inp,proof=walk(d,b,False);stop=at
            cs=sorted({j//128 for j in range(start,stop)})
            parts[pi]={'tree':tree,'input':inp,'start':start,'stop':stop,'chunks':cs}
            return f'part{pi}',f'input{pi}',f'(part{pi}_true τ '+ ' '.join('h'+str(c) for c in cs)+')'
        ix=at;cl=nums(raw[at]);at+=1;k=b+(1<<(d-1))
        lt,li,lp=walk(d-1,b);rt,ri,rp=walk(d-1,k)
        return (f'(Tree.node {k} (rawMask {cl}) {lt} {rt})',
                f'(.node {k} {cl} {li} {ri})',
                f'({BASE}.TreeTrue.node ({BASE}.rawMask_true τ {cl} (List.all_eq_true.mp h{ix//128} {cl} (by decide +kernel)))\n {lp}\n {rp})')
    root,_,rootproof=walk(s['tree_height'],0);assert at==len(raw)
    data_modules=[];truth_modules=[]
    for first in range(0,len(parts),8):
        g=first//8;dm=f'ReplayParts153{g:02d}';tm=f'ReplayTruth153{g:02d}'
        data_modules.append(dm);truth_modules.append(tm)
        body=['import InputTree153Replay',OPTIONS,'namespace '+NS,
              'open Snake9.ReplayInput153 (InputTree)',f'open {BASE} (Tree rawMask)',f'open {FAST} (perf)']
        truth=['import '+dm,'import ReplayTools153',OPTIONS,'namespace '+NS]
        for i in range(first,min(first+8,len(parts))):
            x=parts[i];cl=nums([]) if x['start']==x['stop'] else '['+', '.join(nums(c) for c in raw[x['start']:x['stop']])+']'
            body += [f'def input{i} : InputTree := {x["input"]}',f'noncomputable def part{i} : Tree := {x["tree"]}',
                f'theorem part{i}_build : input{i}.build = part{i} := by rfl',
                f'theorem part{i}_clauses : input{i}.clauses = {cl} := by rfl']
            chunks=x['chunks'];expr=' ++ '.join(CNF+'.raw'+str(c) for c in chunks)
            off=x['start']-128*chunks[0];n=x['stop']-x['start']
            truth += [f'theorem part{i}_slice : input{i}.clauses = (({expr}).drop {off}).take {n} := by',f'  rw [part{i}_clauses]','  rfl',f'theorem part{i}_true (τ : Nat → Bool)']
            truth += [f'    (h{c} : {CNF}.raw{c}.all {PRED} = true)' for c in chunks]
            truth += [f'    : {BASE}.TreeTrue τ part{i} := by',f'  rw [← part{i}_build]',
                f'  apply build_true_of_slice τ input{i} ({expr}) {off} {n} part{i}_slice']
            if len(chunks)>1:
                truth += ['  rw [List.all_append]','  rw ['+', '.join('h'+str(c) for c in chunks)+']','  rfl']
            else:truth += [f'  exact h{chunks[0]}']
            truth += [f'#print axioms part{i}_true']
        body+=['end '+NS];truth+=['end '+NS];emit(dm,'\n'.join(body));emit(tm,'\n'.join(truth))
    emit('ReplayInitial153','\n'.join(['import '+m for m in data_modules]+[OPTIONS,'namespace '+NS,f'open {BASE} (Tree rawMask)',f'open {FAST} (perf)',f'noncomputable def start : Tree := {root}','end '+NS]))
    chunks=list(range((len(raw)+127)//128))
    assembly=['import ReplayInitial153','import ReplayRawChunks153']+['import '+m for m in truth_modules]
    assembly += [OPTIONS,'namespace '+NS,'theorem start_true (τ : Nat → Bool)',
        f'    (h : Snake9.LocalWindow.cnfTrue τ {CNF}.cnf = true) : {BASE}.TreeTrue τ start := by',
        '  obtain ⟨'+', '.join('h'+str(c) for c in chunks)+'⟩ := Snake9.ReplayRawChunks153.chunks_true τ h',
        '  exact '+rootproof,'#print axioms start_true','end '+NS]
    emit('ReplayAssembly153','\n'.join(assembly))
    order=['LratCheck153Replay','LratFast153Replay','InputTree153Replay','ReplayTools153','ReplayRawChunks153']+data_modules+['ReplayInitial153']+truth_modules+['ReplayAssembly153']
    return order,len(parts)

def pilot(s,r):
    rows=pack_rows();n=r['segments'][0]['after_step'];proof=[next(rows) for _ in range(n)]
    body=['import ReplayInitial153',OPTIONS,'namespace Snake9.ReplayPilot153',f'open {BASE} (Tree andB)',f'open {FAST}',
        'noncomputable def proof : List Nat := '+hexs(proof),
        'noncomputable def checkpoint : List Nat := '+hexs(cp_values(r,1)),
        f'noncomputable def afterPrefix : Tree := build {s["tree_height"]} checkpoint','end Snake9.ReplayPilot153']
    emit('ReplayPilotData153','\n'.join(body))
    emit('ReplayPilotCheck153','\n'.join(['import ReplayPilotData153',OPTIONS,'namespace Snake9.ReplayPilot153',
        f'open {BASE} (andB)',f'open {FAST}',
        'theorem prefix_check : andB (check Snake9.ReplayData153.start proof)',
        '    (cpOk (replay Snake9.ReplayData153.start proof) afterPrefix) = true := by',
        '  decide +kernel','#print axioms prefix_check','end Snake9.ReplayPilot153']))
    emit('ReplayPilotConsequence153','\n'.join(['import ReplayAssembly153','import ReplayPilotCheck153',OPTIONS,
        'namespace Snake9.ReplayPilot153',
        'theorem prefix_true (τ : Nat → Bool)',f'    (h : Snake9.LocalWindow.cnfTrue τ {CNF}.cnf = true) :',
        f'    {BASE}.TreeTrue τ afterPrefix :=',
        f'  {FAST}.cp_true τ prefix_check (Snake9.ReplayData153.start_true τ h)',
        '#print axioms prefix_true','end Snake9.ReplayPilot153']))
    return ['ReplayPilotData153','ReplayPilotCheck153','ReplayPilotConsequence153']

def full(s,r):
    order=[];groups=[];segments=r['segments'];nr=len(segments);stepstream=pack_rows()
    cps={c['before_segment']:c for c in r['checkpoints']}
    for a in range(32,nr,32):
        m=f'ReplayCheckpoint153_{a:05d}';order.append(m)
        emit(m,'\n'.join(['import LratFast153Replay',OPTIONS,'namespace Snake9.ReplayFull153',f'open {BASE} (Tree)',f'open {FAST}',
            f'noncomputable def start{a} : Tree := build {s["tree_height"]} '+hexs(cp_values(r,a)),'end Snake9.ReplayFull153']))
    for a in range(0,nr,32):
        b=min(a+32,nr);g=a//32;dm=f'ReplayData153_{g:04d}';imports=['ReplayInitial153'] if a==0 else [f'ReplayCheckpoint153_{a:05d}']
        if b<nr:imports.append(f'ReplayCheckpoint153_{b:05d}')
        data=['import '+m for m in imports]+[OPTIONS,'namespace Snake9.ReplayFull153',f'open {BASE} (Tree)',f'open {FAST}']
        if a==0:data+=['noncomputable def start0 : Tree := Snake9.ReplayData153.start']
        for k in range(a,b):
            n=segments[k]['after_step']-segments[k]['first_step']
            data += [f'noncomputable def proof{k} : List Nat := '+hexs([next(stepstream) for _ in range(n)])]
            if k+1<b:data += [f'noncomputable def start{k+1} : Tree := replay start{k} proof{k}']
        data+=['end Snake9.ReplayFull153'];emit(dm,'\n'.join(data));order.append(dm)
        checks=[]
        for c in range(a,b,4):
            cm=f'ReplayCheck153_{c:05d}';checks.append(cm);check=['import '+dm,OPTIONS,'namespace Snake9.ReplayFull153',f'open {BASE} (andB)',f'open {FAST}']
            for k in range(c,min(c+4,b)):
                prop=f'check start{k} proof{k}'
                if k+1==nr:prop=f'andB ({prop}) (hasEmpty (replay start{k} proof{k}) {r["final_tree_key"]})'
                elif k+1==b:prop=f'andB ({prop}) (cpOk (replay start{k} proof{k}) start{b})'
                check += [f'theorem ok{k} : {prop} = true := by','  decide +kernel',f'#print axioms ok{k}']
            check+=['end Snake9.ReplayFull153'];emit(cm,'\n'.join(check));order.append(cm)
        sm=f'ReplaySteps153_{g:04d}';groups.append(sm)
        steps=['import '+m for m in checks]+[OPTIONS,'namespace Snake9.ReplayFull153',f'open {BASE} (TreeTrue)',f'open {FAST}',
            f'theorem steps{g} (τ : Nat → Bool) (h{a} : TreeTrue τ start{a}) : '+('False' if b==nr else f'TreeTrue τ start{b}')+' := by']
        for k in range(a,b):
            if k+1==nr:steps += [f'  exact final_false τ ok{k} h{k}']
            else:
                method='cp_true' if k+1==b else 'replay_true'
                steps += [f'  have h{k+1} : TreeTrue τ start{k+1} := {method} τ ok{k} h{k}']
        if b<nr:steps += [f'  exact h{b}']
        steps += [f'#print axioms steps{g}','end Snake9.ReplayFull153'];emit(sm,'\n'.join(steps));order.append(sm)
    assert next(stepstream,None) is None
    final=['import ReplayAssembly153']+['import '+m for m in groups]+[OPTIONS,'namespace Snake9.ReplayFull153',f'open {BASE} (TreeTrue unsat_of_raw)',
        f'theorem unsat : Snake9.LocalWindow.Unsat {CNF}.cnf := by','  apply unsat_of_raw','  intro τ h',
        f'  have h0 : TreeTrue τ start0 := Snake9.ReplayData153.start_true τ h']
    for g,a in enumerate(range(0,nr,32)):
        b=min(a+32,nr)
        final += [f'  exact steps{g} τ h{a}'] if b==nr else [f'  have h{b} : TreeTrue τ start{b} := steps{g} τ h{a}']
    final += ['#print axioms unsat','end Snake9.ReplayFull153'];emit('ReplayUnsat153','\n'.join(final));order.append('ReplayUnsat153')
    return order

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--full',action='store_true');ap.add_argument('--max-source-mib',type=int,default=256)
    args=ap.parse_args()
    assert args.full, 'This adaptation only generates the full replay after the pilot audit'
    subprocess.run([sys.executable,'-B','-X','utf8',str(OUT/'scripts/finish_pilot.py'),'--verify-only'],cwd=ROOT,check=True)
    accepted=json.loads((OUT/'data/pilot-completion.json').read_text())
    assert accepted['status']=='PASS_14BIT_INITIAL_TREE_AND_CHECKPOINT_PILOT'
    prep=json.loads((OUT/'data/preparation.json').read_text())
    assert p.sha(Path(__file__))==prep['execution_scripts_sha256']['scripts/emit_full.py']
    for path,digest in prep['input_pins'].items():assert p.sha(ROOT/path)==digest,path
    s=json.loads((H/'data/sizing.json').read_text());r=json.loads((H/'data/packed-replay.json').read_text())
    assert r['status']=='PASS_COMPLETE_RENAMED_AND_PACKED_RUP_REPLAY'
    for x in r['artifacts']:assert p.sha(H/x['path'])==x['sha256']
    order,np=initial(s);order+=pilot(s,r)
    if args.full:order+=full(s,r)
    total=sum(len(x.encode()) for x in files.values());assert total<=args.max_source_mib*1048576
    LEAN.mkdir(parents=True,exist_ok=True)
    artifacts=[]
    for name,txt in files.items():
        path=LEAN/(name+'.lean')
        if path.exists():assert path.read_bytes()==txt.encode(), 'Refuse to replace a changed existing source: '+name
        else:path.write_bytes(txt.encode())
        artifacts.append({'module':name,'path':str(path.relative_to(OUT)).replace('\\','/'),'sha256':p.sha(path),'bytes':path.stat().st_size})
    cpcount=len(range(32,s['segment_count'],32));groups=(s['segment_count']+31)//32
    fullcount=len(order) if args.full else len(order)+cpcount+groups*2+(s['segment_count']+3)//4+1
    plan={'status':'SOURCE_PREPARED_UNCHECKED','mode':'full' if args.full else 'bounded_initial_tree_and_prefix_pilot',
        'module_order':order,'module_count':len(order),'source_bytes':total,'initial_subtrees':np,
        'cnf_dependency':'LocalWindowCnf.ShareWindow153','cnf_namespace':CNF,
        'pilot_deductions':r['segments'][0]['after_step'],'pilot_hints':r['segments'][0]['hints'],
        'full_expected_module_count':fullcount,'full_segments':s['segment_count'],'full_checkpoint_groups':groups,
        'full_source_size_basis':{'proof_literals_bytes':r['packed_source_hex_bytes'],'checkpoint_literals_upper_bytes':r['checkpoint_source_hex_upper_bytes']},
        'full_generation_command':'python -B scripts/emit_full.py --full --max-source-mib 256',
        'generator_sha256':p.sha(Path(__file__)),'copied_source_pins':sourcepins,'artifacts':artifacts,
        'lean_invoked':False,'solver_invoked':False,'axiom_expectation':'Only standard Lean axioms; no sorryAx, added axioms or native_decide.',
        'remaining':'Compile fresh checkers, full initial-tree bridge, prefix with checkpoint; then full packed replay and final unsat theorem. Actual-snake semantics belongs to parent pipeline.'}
    target=OUT/'data/full-source-plan.json';assert not target.exists()
    p.save(target,plan)
    print(json.dumps({k:v for k,v in plan.items() if k not in ('module_order','copied_source_pins','artifacts')},indent=2))

if __name__=='__main__':main()
