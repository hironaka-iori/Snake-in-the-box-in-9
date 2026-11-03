"""Export a saved milestone140 proof. No solver or Lean process is run."""
from pathlib import Path
from collections import Counter
from types import SimpleNamespace
import hashlib, importlib.util, json, re, sys, tempfile, time
sys.dont_write_bytecode = True
H = Path(__file__).resolve().parents[1]
R = H.parents[1]
PASS = 'PASS_COMPLETE_NATIVE_RUP_REPLAY'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda p: json.loads(p.read_text(encoding='utf-8-sig'))

def write(p, value):
    p.parent.mkdir(parents=True, exist_ok=True)
    if isinstance(value, str): value = value.encode('utf-8')
    with p.open('xb') as f: f.write(value)

def jswrite(p, value): write(p, json.dumps(value, indent=2)+'\n')

def load(p, name):
    spec = importlib.util.spec_from_file_location(name, p)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod

def cnf(nv, rows):
    return (f'p cnf {nv} {len(rows)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in rows)).encode('ascii')

def parse_cnf(p):
    rows, nv = [], None
    for line in p.read_text(encoding='ascii').splitlines():
        if not line or line.startswith('c'): continue
        if line.startswith('p'):
            _,_,v,n = line.split(); nv,count = int(v),int(n)
        else:
            row=list(map(int,line.split())); assert row[-1]==0
            rows.append(row[:-1])
    assert nv is not None and count==len(rows)
    return nv,rows

def wrapper(module, directions, base):
    assert base and module == 'CycleBase140' and directions == [0,1,2,0,3,2]
    return (H/'scripts/actual-wrapper.lean.txt').read_text(encoding='utf-8')


def run(mode='short'):
    assert mode in ('short','base')
    started=time.monotonic(); base=mode=='base'
    module='CycleBase140' if base else 'CycleShort140'
    name='base140' if base else 'short140'
    final_module='ActualBase140' if base else 'ActualShort140'
    final_theorem=f'Snake9.LocalWindow.{module}.'+('actual_exact_counts' if base else 'actual_short_caps')
    plan_path=H/f'data/proof-plan-{mode}.json'
    assert not plan_path.exists(), 'Preserve existing export receipt'
    certdir=H/f'work/certificate-{mode}'; recpath=H/f'data/native-{mode}.json'; rec=read(recpath)
    if base:
        assert rec['status']==PASS
        replay=rec['replay']
    else:
        assert rec['status']=='NATIVE_REPLAY_PENDING_HINT_LIMIT'
        replay=read(H/'data/replay-short.json')
        assert replay['native_record_sha256']==sha(recpath)
        for key in ('trim_sha256','input_sha256','core_ids_sha256'): assert replay[key]==rec[key]
    assert replay['status']==PASS and replay['every_trimmed_step_checked']
    assert replay['final_empty_clause_checked'] and replay['original_ids_preserved']
    for rel,digest in rec['source_files_sha256'].items(): assert sha(R/rel)==digest,rel
    for rel,digest in rec['preserved_files_sha256'].items(): assert sha(certdir/rel)==digest,rel
    for fname,key in [('input.cnf','input_sha256'),('trimmed.lrat','trim_sha256'),('core.cnf','core_sha256'),('core-ids.json','core_ids_sha256')]:
        assert sha(certdir/fname)==rec[key]
    satpath=R/'milestones/10-window-aggregate/scripts/gen_lean_sat.py'
    lrpath=R/'milestones/109-relaxed-graph-test/upstream/milestones/10-window-aggregate/scripts/gen_lean_lrat.py'
    assert sha(lrpath)=='2f4b1339817194163a080468d2e404dd7d14e7c048f8fc90e0a2691b243bf384'
    satgen=load(satpath,'satgen140_'+mode); lr=load(lrpath,'lrat140_'+mode)
    encpath=H/'work/short/encoding.json'; encoding=read(encpath)
    enc=satgen.TaggedEncoding(encoding['window'],encoding['bounds'],radius=9)
    original_nv,ordinary=parse_cnf(H/'work/short/base.cnf')
    assert enc.nv==original_nv and enc.clauses==ordinary
    assert json.loads(json.dumps(enc.meaning))==encoding['variable_meaning']
    ordinary_count=len(enc.clauses)
    extra=[] if base else read(H/'work/short/cycle-cuts.json')
    for cut in extra:
        assert satgen.is_cycle_set(cut) and set(cut)<=enc.B
        enc.add([-enc.var[v] for v in cut],('cut',))
    nv,original=parse_cnf(certdir/'input.cnf')
    assert nv==enc.nv and original==enc.clauses
    ids=read(certdir/'core-ids.json')
    assert ids==sorted(set(ids)) and len(ids)==rec['core_clauses']
    assert parse_cnf(certdir/'core.cnf')==(nv,[original[i-1] for i in ids])
    tags=[enc.tags[i-1] for i in ids]
    old_lemmas=lr.read_lrat(str(certdir/'trimmed.lrat'))
    assert len(old_lemmas)==replay['lemmas']==rec['lemmas']
    assert sum(len(h) for _,_,h in old_lemmas)==replay['hints']==rec['hints']
    active={abs(x) for i in ids for x in original[i-1]}
    active.update(abs(x) for _,cl,_ in old_lemmas for x in cl)
    assert active<=set(range(1,nv+1)) and len(active)<2400
    order=sorted(active)+sorted(set(range(1,nv+1))-active) if base else list(range(1,nv+1))
    rename={old:i+1 for i,old in enumerate(order)}; inverse={new:old for old,new in rename.items()}
    assert set(rename)==set(inverse)==set(range(1,nv+1))
    def lit(x): return rename[abs(x)]*(1 if x>0 else -1)
    full=[[lit(x) for x in row] for row in original]
    lemmas=[(cid,[lit(x) for x in cl],list(hs)) for cid,cl,hs in old_lemmas]
    assert all([inverse[abs(x)]*(1 if x>0 else -1) for x in cl]==old[1] and cid==old[0] and hs==old[2]
               for (cid,cl,hs),old in zip(lemmas,old_lemmas))
    assert max(rename[x] for x in active)<2400
    sem=SimpleNamespace(nv=nv,meaning={rename[x]:v for x,v in enc.meaning.items()},
        ctrs=[([lit(x) for x in lits],k,kind) for lits,k,kind in enc.ctrs])
    allocation=lr.plan(ids,lemmas); assert allocation[3]<=8191
    receipt=R/'milestones/112-critical-sum-refinement/data/Refined112.LocalWindowUnsat.Sum3142.Data0-audit.json'
    audit=read(receipt)
    candidates=[(R/p,d) for p,d in audit['dependencies'].items() if p.endswith('/LratFast.olean')]
    assert audit['exit_code']==0 and len(candidates)==1
    checker,checker_digest=candidates[0]; assert sha(checker)==checker_digest
    export=H/f'work/export-{mode}'; export.mkdir(exist_ok=False)
    for p in [Path(__file__),satpath,lrpath,satpath.with_name('wincert.py')]: write(export/'source-snapshots'/p.name,p.read_bytes())
    write(export/(name+'.cnf'),cnf(nv,full))
    write(export/(name+'.lrat'),''.join(' '.join(map(str,[cid,*cl,0,*hs,0]))+'\n' for cid,cl,hs in lemmas))
    meta=dict(module='LocalWindowCnf.'+module,core_ids=ids,window=encoding['window'],bounds=encoding['bounds'])
    jswrite(export/'meta'/(name+'.json'),meta)
    raw=[[satgen.code(x) for x in full[i-1]] for i in ids]
    used_extra=[dict(clause_id=ordinary_count+i+1,vertices=cut) for i,cut in enumerate(extra) if ordinary_count+i+1 in ids]
    used=sorted({t[1] for t in tags if t[0] in {'first','zero','mono','step','over'}})
    semantic=dict(module=module,core_ids=ids,tags=tags,tag_counts=dict(Counter(t[0] for t in tags)),
        old_to_new=rename,new_to_old=inverse,meaning=sem.meaning,counters=sem.ctrs,
        original_raw=[original[i-1] for i in ids],renamed_signed_raw=[full[i-1] for i in ids],raw=raw,
        used_extra_cycle_cuts=used_extra,active_variables=len(active),active_old_ids=sorted(active),
        used_counter_indices=used,used_counter_kinds={i:enc.ctrs[i][2] for i in used},
        window=encoding['window'],directions=encoding['directions'],bounds=encoding['bounds'],
        source_native_sha256=sha(recpath),status='GENERATED_SEMANTICS_LEAN_PENDING')
    jswrite(H/f'data/selected-core-semantics-{mode}.json',semantic)
    lr.set_width(13,fast=True,off=2400); lr.DATA_DEF='noncomputable def'; lr.GROUPED=True
    lr.read_lrat=lambda _:lemmas; lr.plan=lambda _ids,_lemmas:allocation
    files=[]
    with tempfile.TemporaryDirectory(prefix=f'snake140-{mode}-export-') as tmp:
        tmp=Path(tmp)
        cnfsrc=('import LocalWindowModel\nset_option maxRecDepth 100000\n'
            f'namespace Snake9.LocalWindow.{module}\n'
            f'def window : List Nat := {encoding["window"]}\n'
            'def bounds : List (Nat × Nat) := ['+','.join(f'({a},{b})' for a,b in encoding['bounds'])+']\n'
            'def raw : List (List Nat) := [\n'+',\n'.join('  '+str(row) for row in raw)+']\n'
            'def cnf : List (List Int) := raw.map (·.map decodeLit)\n'
            f'end Snake9.LocalWindow.{module}\n')
        write(tmp/'LocalWindowCnf'/(module+'.lean'),cnfsrc)
        satgen.LEAN=str(tmp); satgen.write_module(name,module,meta,sem,tags)
        stats=lr.export(name,str(export),6000,4,4,True,str(tmp),str(export/'meta'))
        assert stats['simulated'] and stats['hints']==rec['hints']
        write(tmp/(final_module+'.lean'),wrapper(module,encoding['directions'],base))
        for p in sorted(tmp.rglob('*.lean')):
            dest=H/'lean'/p.relative_to(tmp); write(dest,p.read_bytes()); files.append(dest)
    names={p.relative_to(H/'lean').as_posix()[:-5].replace('/','.'):p for p in files}
    sequence,pending=[],set(names)
    while pending:
        ready=sorted(n for n in pending if not set(re.findall(r'^import ([\w.]+)$',names[n].read_text(encoding='utf-8'),re.M))&pending)
        assert ready
        sequence.extend(ready); pending-=set(ready)
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b','\n'.join(p.read_text(encoding='utf-8') for p in files))
    pinned=[H/'scripts/actual-wrapper.lean.txt',Path(__file__),satpath,satpath.with_name('wincert.py'),lrpath,recpath,encpath,
        certdir/'input.cnf',certdir/'trimmed.lrat',certdir/'core-ids.json',
        R/'work/final_lean/LocalWindowModel.lean',R/'work/final_lean/LocalWindowTags.lean',
        R/'work/final_lean/LocalWindowBridge.lean',R/'milestones/79-retained-edge-guards/lean/CanonicalExclusions.lean',
        H/'scripts/export_base.py' if base else H/'data/replay-short.json']
    plan=dict(status='EXPORTED_AND_SIMULATED_LEAN_PENDING',stats=stats,module_order=sequence,
        final_module=final_module,cnf_module='LocalWindowCnf.'+module,final_theorem=final_theorem,
        refuted_theorem=f'Snake9.LocalWindow.{module}.refuted',expected_axiom_reports=4,
        artifacts=[dict(path=p.relative_to(H).as_posix(),sha256=sha(p)) for p in files],
        checker_module='LratFast',checker_object=str(checker),checker_object_sha256=checker_digest,
        checker_receipt=str(receipt),checker_receipt_sha256=sha(receipt),
        source_files_sha256={p.relative_to(R).as_posix():sha(p) for p in pinned},
        semantic_data_sha256=sha(H/f'data/selected-core-semantics-{mode}.json'),
        export_artifacts=[dict(path=p.relative_to(H).as_posix(),sha256=sha(p)) for p in sorted(export.rglob('*')) if p.is_file()],
        active_variables=len(active),original_variables=nv,used_extra_cycle_cuts=len(used_extra),
        used_counter_indices=used,used_counter_kinds={i:enc.ctrs[i][2] for i in used},
        seconds=time.monotonic()-started,lean_started=False,
        scope='Python checks and packed replay passed. Lean sources and actual-snake bridge remain unchecked until separate Lean receipts pass. No global upper bound is claimed.')
    jswrite(plan_path,plan)
    print(json.dumps(dict(plan=str(plan_path),stats=stats,modules=len(sequence),active=len(active)),indent=2))

if __name__=='__main__': run('short')
