"""Slice case7302's RUP-only LRAT, independently simulate, then select safely.

Input CNF and semantic Lean sources are never changed. Preparation retains only
ancestors of the final empty clause after tracing each lemma's unit reasons
backward from its first conflict. Retained hints keep their original order.
Deleting proof deletion commands is sound because clauses remain available.

Usage: slice_lrat.py 7302 --prepare ; slice_lrat.py 7302 --select
Selection requires the successful bit-mask/slot simulation in g.export(check=True).
It never runs Lean. The final Lean kernel replay remains required.
"""
from pathlib import Path
import gc,hashlib,json,os,shutil,subprocess,sys,time

TASK=Path(__file__).resolve().parents[1];ROOT=TASK.parents[1];HERE=ROOT/'milestones/73-countfree-share-catalogue'
assert len(sys.argv)==3 and sys.argv[1]=='7302' and sys.argv[2] in ['--prepare','--select']
OUT=HERE/'cases/case7302';CASE=json.loads((OUT/'data/case.json').read_text())
SLUG=CASE['slug'];MOD=CASE['namespace'];CERT=OUT/'certificates'
read=lambda p:json.loads(p.read_text())
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for chunk in iter(lambda:f.read(1024*1024),b''):h.update(chunk)
    return h.hexdigest()
def save(p,d):
    p.parent.mkdir(parents=True,exist_ok=True)
    p.write_text(json.dumps(d,indent=2)+'\n',encoding='utf-8')
def safe(p):
    resolved=p.resolve();root=OUT.resolve()
    assert resolved!=root and resolved.is_relative_to(root),str(resolved)
    return resolved
def allowed_lean(p):
    r=p.relative_to(OUT/'lean').as_posix()
    return r==f'LocalWindowUnsat/{MOD}.lean' or r.startswith(f'LocalWindowUnsat/{MOD}/') or (r.startswith('Lrat') and '/' not in r)
def semantic_hashes():
    return {p.relative_to(OUT).as_posix():sha(p) for p in (OUT/'lean').rglob('*.lean') if not allowed_lean(p)}
def no_lean_process():
    command="@(Get-CimInstance Win32_Process | Where-Object { $_.Name -match '^(lean|lake)(\\.exe)?$' } | Select-Object ProcessId,Name,CommandLine) | ConvertTo-Json -Compress"
    run=subprocess.run(['powershell','-NoProfile','-Command',command],capture_output=True,text=True,check=True)
    found=json.loads(run.stdout) if run.stdout.strip() else []
    assert not found, 'Lean/lake process exists; do not move or select proof files: '+str(found)
def no_compiled_lrat():
    found=[]
    for p in (OUT/'build').rglob('*.olean'):
        r=p.relative_to(OUT/'build').as_posix()
        if '/LocalWindowUnsat/' in '/'+r or p.name.startswith('Lrat'):found.append(r)
    assert not found, 'Existing LRAT compiled objects require a separate review: '+str(found[:10])

sys.path.insert(0,str(ROOT/'milestones/10-window-aggregate/scripts'))
import gen_lean_lrat as g

def ancestors(final,by_id,input_ids):
    needed=set();todo=[final]
    while todo:
        c=todo.pop()
        if c in input_ids or c in needed:continue
        needed.add(c);todo.extend(by_id[c][2])
    return needed

def trim_rup(clause,hints,clauses):
    """Trace false-literal reasons, independent of the exporter bit-mask checker."""
    reason={lit:None for lit in clause};conflict=None
    for index,h in enumerate(hints):
        pending=[lit for lit in clauses[h] if lit not in reason]
        if not pending:
            conflict=index;break
        if len(pending)==1:
            false_lit=-pending[0]
            if false_lit not in reason:reason[false_lit]=index
    assert conflict is not None, 'Original hint list did not produce a RUP conflict'
    needed={conflict};todo=list(clauses[hints[conflict]])
    while todo:
        lit=todo.pop();index=reason[lit]
        if index is None or index in needed:continue
        assert index<conflict
        needed.add(index)
        for dep in clauses[hints[index]]:
            if dep!=-lit:
                assert dep in reason and (reason[dep] is None or reason[dep]<index)
                todo.append(dep)
    return [hint for i,hint in enumerate(hints) if i in needed]

def prepare():
    started=time.monotonic();generation=OUT/'data/lrat-generation.json';gen=read(generation)
    assert gen['status']=='COMPACT_LRAT_GENERATED' and 'selected_transformation' not in gen
    cnf=CERT/(SLUG+'.cnf');lrat=CERT/(SLUG+'.lrat')
    assert sha(cnf)==gen['cnf_sha256'] and sha(lrat)==gen['lrat_sha256']
    stage=safe(OUT/'build'/('lrat-slice-'+gen['lrat_sha256'][:12]));assert not stage.exists(), 'Preparation already exists'
    stage.mkdir();backup=stage/'original';backup.mkdir()
    originals=[lrat,generation,OUT/'data/export.json',OUT/'data'/f'{SLUG}.json',cnf]
    archive=[]
    for p in originals:
        dest=backup/p.relative_to(OUT);dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,dest)
        assert sha(dest)==sha(p);archive.append(dict(original=p.relative_to(OUT).as_posix(),backup=dest.relative_to(OUT).as_posix(),sha256=sha(dest),bytes=dest.stat().st_size))
    semantic=semantic_hashes();meta=read(OUT/'data'/f'{SLUG}.json')
    core=g.read_cnf_core(str(cnf),meta['core_ids']);input_ids=set(meta['core_ids'])
    assert meta['core_ids']==list(range(1,len(core)+1)), 'Preserve the complete original input clause numbering'
    lemmas=g.read_lrat(str(lrat));before=dict(lemmas=len(lemmas),hints=sum(len(x[2]) for x in lemmas))
    by_id={row[0]:row for row in lemmas};assert len(by_id)==len(lemmas)
    assert lemmas[-1][1]==[] and all(a[0]<b[0] for a,b in zip(lemmas,lemmas[1:]))
    assert not input_ids.intersection(by_id)
    known=set(input_ids)
    for cid,clause,hints in lemmas:
        assert all(h in known for h in hints);known.add(cid)
    first=ancestors(lemmas[-1][0],by_id,input_ids)
    print('Original',before,'final-clause ancestors',len(first),flush=True)
    clauses={c:tuple(dict.fromkeys(cl)) for c,cl in zip(meta['core_ids'],core)}
    clauses.update({c:tuple(dict.fromkeys(cl)) for c,cl,_ in lemmas})
    sliced={};hint_before=hint_after=0
    for count,(cid,clause,hints) in enumerate(row for row in lemmas if row[0] in first):
        hs=trim_rup(clause,hints,clauses);sliced[cid]=(cid,clause,hs)
        hint_before+=len(hints);hint_after+=len(hs)
        if count and count%20000==0:print('Traced',count,'lemmas;',hint_before,'->',hint_after,'hints',flush=True)
    needed=ancestors(lemmas[-1][0],sliced,input_ids)
    selected=[sliced[c] for c,_,_ in lemmas if c in needed]
    candidate=stage/'candidate';(candidate/'certificates').mkdir(parents=True);(candidate/'data').mkdir();(candidate/'lean').mkdir()
    dest=candidate/'certificates'/(SLUG+'.lrat')
    with dest.open('w',encoding='ascii',newline='\n') as out:
        for c,cl,hs in selected:out.write(' '.join(map(str,[c]+cl+[0]+hs+[0]))+'\n')
    shutil.copyfile(cnf,candidate/'certificates'/cnf.name)
    shutil.copyfile(OUT/'data'/f'{SLUG}.json',candidate/'data'/f'{SLUG}.json')
    _,_,_,slots=g.plan(meta['core_ids'],selected)
    off=1<<meta['active_variables'].bit_length();bits=max(13,slots.bit_length(),(off+meta['active_variables']+1).bit_length());assert bits<=15
    transformed=dict(lemmas=len(selected),hints=sum(len(h) for _,_,h in selected),slots=slots,word_bits=bits,ancestor_only_lemmas=len(first),trimmed_ancestor_hints=hint_after)
    assert transformed['hints']<before['hints']
    print('Candidate',transformed,'starting independent export simulation',flush=True)
    del lemmas,by_id,clauses,sliced,selected,known;gc.collect()
    base_name=f'LratOffset{off}';base_module=f'LratCheckOffset{off}';fast_name=f'LratFastOffset{off}W{bits}'
    g.set_width(bits,True,4000);g.OFF=off;g.BASE_NS=f'Snake9.{base_name}'
    g.CHECKER_IMPORT=f'import {fast_name}';g.CHECKER_OPEN=f'open Snake9.{fast_name}\nopen Snake9.{base_name} (Tree TreeTrue andB)';g.DATA_DEF='noncomputable def'
    report=g.export(SLUG,str(candidate/'certificates'),30000,4,6,True,str(candidate/'lean'),str(candidate/'data'))
    assert report['simulated'] and report['lemmas']==transformed['lemmas'] and report['hints']==transformed['hints']
    assert semantic_hashes()==semantic and sha(cnf)==gen['cnf_sha256']
    save(stage/'candidate-export.json',report)
    receipt=dict(status='SLICED_CANDIDATE_SIMULATED',case=7302,stage=str(stage),originals=archive,
      original_lrat_sha256=gen['lrat_sha256'],candidate_lrat_sha256=sha(dest),cnf_sha256=sha(cnf),
      input_clauses_preserved=len(core),before=before,after=transformed,export=report,
      semantic_sources_sha256=semantic,source_sha256=sha(Path(__file__)),exporter_sha256=sha(Path(g.__file__)),
      seconds=time.monotonic()-started,
      transformations=['Keep derived-clause ancestors of final empty clause.','Trace unit-reason dependencies backward from first conflict, retaining original hint order.','Repeat final-empty ancestor closure after hint pruning.','Omit deletion commands; retain every original input clause and every retained derived clause until last-use slot reuse by the unchanged exporter.'],
      scope='Independent Python bit-mask/slot/checkpoint simulation passed. Candidate not yet selected; no Lean replay or local theorem claimed.')
    save(OUT/'data/lrat-slice-candidate.json',receipt)
    print('SLICED_CANDIDATE_SIMULATED',transformed,'seconds',receipt['seconds'],flush=True)

def select():
    receipt_path=OUT/'data/lrat-slice-candidate.json';r=read(receipt_path)
    assert r['status']=='SLICED_CANDIDATE_SIMULATED';stage=safe(Path(r['stage']));candidate=stage/'candidate'
    assert sha(candidate/'certificates'/(SLUG+'.lrat'))==r['candidate_lrat_sha256']
    assert sha(CERT/(SLUG+'.cnf'))==r['cnf_sha256'] and sha(CERT/(SLUG+'.lrat'))==r['original_lrat_sha256']
    assert semantic_hashes()==r['semantic_sources_sha256']
    assert sha(Path(g.__file__))==r['exporter_sha256']
    no_lean_process();no_compiled_lrat()
    old=[OUT/'lean/LocalWindowUnsat'/MOD,OUT/'lean/LocalWindowUnsat'/(MOD+'.lean')]+list((OUT/'lean').glob('Lrat*.lean'))
    backup=stage/'original-lean';backup.mkdir();moved=[]
    for source in old:
        source=safe(source);assert source.exists()
        files=[source] if source.is_file() else list(source.rglob('*'))
        hashes={p.relative_to(OUT/'lean').as_posix():sha(p) for p in files if p.is_file()}
        target=safe(backup/source.relative_to(OUT/'lean'));assert not target.exists();target.parent.mkdir(parents=True,exist_ok=True)
        source.rename(target)
        for rel,h in hashes.items():assert sha(backup/rel)==h
        moved.append(dict(source=str(source.relative_to(OUT)),backup=str(target.relative_to(OUT)),hashes=hashes))
    save(stage/'original-lean-manifest.json',moved)
    chosen=CERT/(SLUG+'.lrat');temp=chosen.with_suffix('.selected.tmp');shutil.copyfile(candidate/'certificates'/chosen.name,temp)
    assert sha(temp)==r['candidate_lrat_sha256'];os.replace(temp,chosen)
    gen=read(stage/'original/data/lrat-generation.json')
    gen.update(lrat_sha256=r['candidate_lrat_sha256'],selected_transformation='backward-final-empty-and-unit-reason-slice',
      original_lrat_sha256=r['original_lrat_sha256'],candidate_receipt_sha256=sha(receipt_path),
      original_generation_receipt_sha256=sha(stage/'original/data/lrat-generation.json'),
      scope='Original compact LRAT generation followed by sound dependency slicing and independent export simulation. Every original input clause is unchanged. Lean replay remains required.')
    save(OUT/'data/lrat-generation.json',gen)
    no_lean_process()
    command=[sys.executable,'-X','utf8',str(HERE/'scripts/export_lrat.py'),'7302']
    log=OUT/'logs/lrat-slice-export.log'
    with log.open('w',encoding='utf-8') as f:run=subprocess.run(command,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT,timeout=300)
    assert run.returncode==0,log.read_text()[-4000:]
    exported=read(OUT/'data/export.json')
    for k in ['lemmas','hints','slots','segments','checkpoints','check_modules']:assert exported[k]==r['export'][k]
    assert exported['simulated'] and exported['word_bits']==r['after']['word_bits']
    sub=OUT/'lean/LocalWindowUnsat'/MOD
    assert len(list(sub.glob('Data*.lean')))==exported['segments']+1
    assert len(list(sub.glob('Check*.lean')))==exported['check_modules']
    assert semantic_hashes()==r['semantic_sources_sha256'] and sha(CERT/(SLUG+'.cnf'))==r['cnf_sha256']
    selected=dict(status='SLICED_LRAT_SELECTED_AND_RESIMULATED',case=7302,
      original_lrat_sha256=r['original_lrat_sha256'],selected_lrat_sha256=sha(chosen),input_cnf_sha256=r['cnf_sha256'],
      candidate_receipt_sha256=sha(receipt_path),export_receipt_sha256=sha(OUT/'data/export.json'),
      generation_receipt_sha256=sha(OUT/'data/lrat-generation.json'),backup_manifest=str((stage/'original-lean-manifest.json').relative_to(OUT)),
      backup_manifest_sha256=sha(stage/'original-lean-manifest.json'),semantic_sources_unchanged=True,
      before=r['before'],after=exported,source_sha256=sha(Path(__file__)),
      generated_sources_sha256={p.relative_to(OUT).as_posix():sha(p) for p in (OUT/'lean').rglob('*.lean') if allowed_lean(p)},
      scope='Selected only after independent simulation; re-exported by unchanged export_lrat.py with simulation again. Original LRAT, receipts and complete uncompiled LRAT Lean tree preserved. No Lean replay started; no local theorem claimed.')
    save(OUT/'data/lrat-slice-selection.json',selected)
    print(selected['status'],{k:exported[k] for k in ['lemmas','hints','slots','segments','check_modules','word_bits']},flush=True)

if sys.argv[2]=='--prepare':prepare()
else:select()
