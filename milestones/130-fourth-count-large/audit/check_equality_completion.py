"""Independent receipt and statement audit of the completed equality-case proof."""
from pathlib import Path
from collections import Counter
import ast,datetime,hashlib,json,re,time

H=Path(__file__).resolve().parents[1];R=H.parents[1]
P=R/'milestones/129-fourth-count-three'
ALLOWED={'propext','Classical.choice','Quot.sound'}
PINS={};CACHE={}
def path(p,base=R):
 p=Path(p);return (p if p.is_absolute() else base/p).resolve()
def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def sha(p):
 p=path(p)
 if p not in CACHE:CACHE[p]=digest(p)
 name=p.relative_to(R).as_posix() if p.is_relative_to(R) else str(p)
 PINS[name]=CACHE[p];return CACHE[p]
def verify(p,d):assert sha(p)==d,('Hash mismatch',str(p))
def read(p):
 sha(p);return json.loads(path(p).read_text(encoding='utf-8-sig'))
def imports(text):
 rows=[]
 for line in text.splitlines():
  if line.startswith('import '):
   match=re.fullmatch(r'import ([\w.]+)',line);assert match,line
   rows.append(match.group(1))
 return rows
def dependency_pins(q):
 out={}
 for name,d in q['dependencies'].items():
  p=path(name);verify(p,d);out[p]=d
 return out
def axiom_audit(text,log,q,field):
 expected=[];namespaces=[]
 for line in text.splitlines():
  ns=re.fullmatch(r'namespace ([\w.]+)',line)
  end=re.fullmatch(r'end(?: ([\w.]+))?',line)
  printed=re.fullmatch(r'#print axioms ([\w.]+)',line)
  if ns:namespaces.append(ns.group(1))
  elif end:
   assert namespaces and (end.group(1) is None or end.group(1)==namespaces[-1]),line
   namespaces.pop()
  elif printed:
   name=printed.group(1)
   expected.append(name if name.startswith('Snake9.') else '.'.join(namespaces+[name]))
 assert not namespaces
 pairs=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log,re.S)
 pairs.extend((n,'') for n in re.findall(r"'([^']+)' does not depend on any axioms",log))
 rows=[dict(theorem=n,axioms=re.findall(r'[A-Za-z][\w.]*',a)) for n,a in pairs]
 assert [x['theorem'] for x in rows]==expected,(expected,rows)
 assert rows==q.get(field,[])
 assert all(set(x['axioms'])<=ALLOWED for x in rows)
 assert 'error:' not in log and 'sorryAx' not in log
 assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',text)
 return rows
def resolved_imports(text,q,deps):
 rows=[]
 for name in imports(text):
  candidates=[Path(p)/(name.replace('.','/')+'.olean') for p in q['paths']]
  found=next((p.resolve() for p in candidates if p.exists()),None)
  assert found is not None,('Unresolved import',name)
  assert found in deps,('Import object is not pinned',name,str(found))
  verify(found,deps[found]);rows.append(dict(module=name,object=str(found),sha256=sha(found)))
 return rows
def independent_receipt(rp,module,source_root,checker):
 q=read(rp);assert q['status']=='PASS' and q['exit_code']==0 and not q.get('timeout',False)
 src=source_root/(module+'.lean');verify(src,q['source_sha256'])
 log=path(q['log']);verify(log,q['log_sha256'])
 verify(log.parent/'source.lean.txt',q['source_sha256'])
 verify(log.parent/'checker.py.txt',q['checker_sha256']);verify(checker,q['checker_sha256'])
 for field in ['object','importable_object']:verify(q[field],q[field+'_sha256'])
 deps=dependency_pins(q);text=src.read_text();ax=axiom_audit(text,log.read_text(),q,'axioms')
 return dict(module=module,receipt=str(rp),receipt_sha256=sha(rp),source_sha256=sha(src),
  object=q['importable_object'],object_sha256=sha(q['importable_object']),log_sha256=sha(log),
  checker_sha256=sha(checker),dependency_count=len(deps),axioms=ax,
  direct_imports=resolved_imports(text,q,deps),seconds=q['seconds']),text

def main():
 start=time.monotonic();sha(Path(__file__))
 progress_path=P/'data/replay-progress.json';final_path=H/'data/independent-actual-final-audit.json'
 deadline=time.monotonic()+600;observations=[]
 while True:
  try:
   progress=json.loads(progress_path.read_text())
   ready=progress['status']=='PASS_COMPLETE_CNF_REFUTATION' and final_path.exists()
   if ready:
    final=json.loads(final_path.read_text());ready=final.get('status')=='PASS'
  except (json.JSONDecodeError,OSError):ready=False
  if ready:break
  observations.append(dict(time=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    replay_status=progress.get('status'),checked=len(progress.get('checked_modules',[])),actual_receipt_exists=final_path.exists()))
  if time.monotonic()>=deadline:
   out=dict(status='PENDING_EQUALITY_COMPLETION_AFTER_BOUNDED_WAIT',observations=observations,scope='No completed equality-case result claimed.')
   (H/'data/equality-completion-review.json').write_text(json.dumps(out,indent=2)+'\n');return
  time.sleep(min(30,deadline-time.monotonic()))
 progress=read(progress_path);plan=read(P/'data/proof-plan.json')
 assert progress['active'] is None and len(progress['checked_modules'])==progress['total_modules']==221
 assert progress['finished_at']
 for name,d in progress['fixed_dependencies'].items():verify(name,d)
 planned=plan['module_order'];executed=progress['ordered_modules']
 assert len(planned)==len(set(planned))==len(executed)==len(set(executed))==221
 assert set(planned)==set(executed)
 assert [x['module'] for x in progress['checked_modules']]==executed
 artifacts={x['path']:x['sha256'] for x in plan['artifacts']}
 assert len(artifacts)==221
 sources={m:P/'lean'/(m.replace('.','/')+'.lean') for m in planned}
 texts={};local_imports={}
 for m,src in sources.items():
  verify(src,artifacts[src.relative_to(P).as_posix()]);texts[m]=src.read_text()
  local_imports[m]=[d for d in imports(texts[m]) if d in sources]
 for order in [planned,executed]:
  positions={m:i for i,m in enumerate(order)}
  for m,ds in local_imports.items():assert all(positions[d]<positions[m] for d in ds)
 dfs=[];seen=set();visiting=set()
 def visit(m):
  if m in seen:return
  assert m not in visiting;visiting.add(m)
  for d in local_imports[m]:visit(d)
  visiting.remove(m);seen.add(m);dfs.append(m)
 final_module='Recovered129G.LocalWindowUnsat.Triple129'
 visit(final_module);assert dfs==executed and seen==set(planned)
 modules=[];kernel_segments=[];checker_versions=Counter()
 for item in progress['checked_modules']:
  m=item['module'];cnf=m=='Recovered129G.LocalWindowCnf.Triple129'
  rp=P/'data'/('independent-core-cnf-audit.json' if cnf else m+'-audit.json')
  verify(rp,item['receipt_sha256']);q=read(rp)
  assert q['status']==('PASS' if cnf else 'PASS_TRIPLE_REPLAY_MODULE')
  assert q['exit_code']==0 and not q.get('timeout',False)
  verify(sources[m],q['source_sha256'])
  obj=P/'build-replay'/(m.replace('.','/')+'.olean')
  verify(obj,q['importable_object_sha256' if cnf else 'olean_sha256'])
  log=path(q['log'],P);verify(log,q['log_sha256'])
  snap=log.parent/'source.lean.txt' if cnf else P/q['source_snapshot']
  verify(snap,q['source_sha256']);checker=snap.parent/'checker.py.txt'
  verify(checker,q['checker_sha256']);checker_versions[q['checker_sha256']]+=1
  if cnf:
   verify(P/'audit/check_core_cnf.py',q['checker_sha256'])
   for field in ['object','importable_object']:verify(q[field],q[field+'_sha256'])
  else:verify(P/'scripts/run_replay.py',q['checker_sha256'])
  deps=dependency_pins(q);ax=axiom_audit(texts[m],log.read_text(),q,'axioms' if cnf else 'theorem_audits')
  direct=resolved_imports(texts[m],q,deps)
  kernel_segments.extend(map(int,re.findall(r'^theorem ok(\d+)\s*:',texts[m],re.M)))
  modules.append(dict(module=m,receipt_sha256=sha(rp),source_sha256=sha(sources[m]),
    object_sha256=sha(obj),log_sha256=sha(log),source_snapshot_sha256=sha(snap),
    checker_snapshot_sha256=sha(checker),dependency_count=len(deps),direct_imports=direct,
    axioms=ax,seconds=q['seconds']))
 assert sorted(kernel_segments)==list(range(1,436))
 final_text=texts[final_module]
 assert 'theorem unsat : Unsat cnf := by' in final_text
 used=Counter(map(int,re.findall(r'\bok(\d+)\b',final_text)))
 assert used==Counter(range(1,436))
 final_ax=modules[-1]['axioms'];assert len(final_ax)==1 and final_ax[0]['theorem']=='Snake9.LocalWindow.Triple129.unsat'
 assert sum(len(m['axioms']) for m in modules)==1
 semantic=read(P/'data/selected-core-semantics.json')
 assert len(semantic['raw'])==len(semantic['tags'])==3500
 verify(sources['Recovered129G.LocalWindowCnf.Triple129'],semantic['cnf_source_sha256'])
 helpers=[]
 for module,rp,checker in [
  ('CoreSemantics129',P/'data/independent-core-semantics-audit.json',P/'audit/check_core_semantics.py'),
  ('ActualSplit129',P/'logs/actual-split-1793689366716282000/record.json',P/'audit/check_split.py')]:
  # The preserved snapshot pins the actual historical checker if its descriptive filename differs.
  if not checker.exists():
   q=read(rp);matches=[p for p in (P/'audit').glob('*.py') if sha(p)==q['checker_sha256']]
   assert matches,('No matching current helper checker',module);checker=matches[0]
  report,_=independent_receipt(rp,module,P/'lean',checker);helpers.append(report)
 actual,actual_text=independent_receipt(final_path,'ActualFourthThree130',H/'lean',H/'scripts/check_final.py')
 assert [a['theorem'] for a in actual['axioms']]==[
  'Snake9.ActualFourthThree130.triple_lower','Snake9.ActualFourthThree130.six_lower',
  'Snake9.ActualFourthThree130.fourth_at_least_four_of_total22']
 declarations=re.findall(r'^theorem ([\w]+)\b',actual_text,re.M)
 assert declarations==['triple_lower','six_lower','fourth_at_least_four_of_total22']
 assert 'hunsat' not in actual_text and '(hfourth : coreAlpha p (r+4) = 3)' in actual_text
 assert actual_text.count('Triple129.unsat')==2
 assert '(hr : r+7 ≤ m)' in actual_text and 'canon (dsOf p r 7) = [0,1,2,0,3,2,4]' in actual_text
 assert '12 ≤ coreAlpha p (r+3)+coreAlpha p (r+5)+coreAlpha p (r+6)' in actual_text
 assert '23 ≤ ∑ j ∈ Finset.range 6, coreAlpha p (r+j+1)' in actual_text
 assert '(htotal : (∑ j ∈ Finset.range 6, coreAlpha p (r+j+1)) ≤ 22)' in actual_text
 assert '4 ≤ coreAlpha p (r+4)' in actual_text
 for name,d in tuple(PINS.items()):assert digest(path(name))==d,('Changed during audit',name)
 criteria={k:True for k in [
  'terminal_replay_status_and_full_coverage','plan_artifact_hashes','all_receipts_successful_without_timeout',
  'sources_objects_logs_and_snapshots_match','checker_snapshots_match_current_fixed_checkers',
  'all_recorded_dependency_pins_match','direct_import_objects_match_pins',
  'both_plan_and_execution_orders_are_topological','execution_is_exact_source_import_depth_first_order',
  'all435_kernel_segment_theorems_present_and_used_once','full_unsat_statement_has_no_external_refutation_premise',
  'all_printed_axioms_match_logs_receipts_and_allowed_set','concrete_semantics_and_split_helpers_checked',
  'three_actual_theorem_statements_and_premises_inspected','actual_assembly_consumes_complete_unsat_theorem',
  'all_inputs_unchanged_at_end']}
 out=dict(status='PASS_COMPLETE_EQUALITY_CASE_ACTUAL_SNAKE_AUDIT',
  completed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),seconds=time.monotonic()-start,
  replay_modules=221,kernel_segments=435,selected_clauses=3500,
  module_order=dict(same_plan_and_execution_sequence=planned==executed,same_modules=True,
    both_valid_topological_orders=True,executed_equals_source_depth_first_order=True,
    planned_order=planned,executed_order=executed),
  replay_axiom_reports=final_ax,helper_reviews=helpers,actual_assembly=actual,
  actual_source=actual_text,module_reviews=modules,checker_versions=dict(checker_versions),
  criteria=criteria,waiting_observations=observations,
  proof_scope='For fitting actual canonical0120324 windows with fourth count3, the other-three sum is at least12 and the six-count sum at least23. Any total22 window therefore has fourth count at least4.',
  limitations=['No claim about the complementary fourth-at-least-four case.',
    'No unconditional six-count floor23 for every0120324 window.',
    'No improved global snake upper bound.',
    'The audit checks saved compiler evidence and dependency identities; it does not rerun Lean or native proof replay.'],
  source_files_sha256=dict(sorted(PINS.items())))
 dest=H/'data/equality-completion-review.json';assert not dest.exists();dest.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
 print(json.dumps({k:v for k,v in out.items() if k not in ['module_order','helper_reviews','actual_assembly','actual_source','module_reviews','source_files_sha256']},indent=2))
 print('Verified files',len(PINS),'Plan/execution order identical',planned==executed)

if __name__=='__main__':main()
