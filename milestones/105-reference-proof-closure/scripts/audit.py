"""Audit the exact-union interface and its source selection without closing the union."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not (HERE/'data/check.lock').exists()
env=read(HERE/'data/environment.json')
for group in ['sources','receipts','objects']:
    for path,digest in env[group].items():assert sha(ROOT/path)==digest,path
name='ReferenceAssembly105';rp=HERE/'data'/(name+'-audit.json');r=read(rp);src=HERE/'lean'/(name+'.lean')
assert r['status']=='PASS_REFERENCE_CLOSURE_MODULE' and r['exit_code']==0 and not r['timeout']
assert sha(src)==r['source_sha256']==sha(HERE/r['source_snapshot'])
assert sha(HERE/'build'/(name+'.olean'))==r['olean_sha256'] and sha(HERE/r['log'])==r['log_sha256']
assert sha((HERE/r['source_snapshot']).parent/'checker.py.txt')==r['checker_sha256']
for path,digest in r['dependencies'].items():assert sha(ROOT/path)==digest,path
text=src.read_text(encoding='utf-8')
assert not re.search(r'\b(sorry|admit|native_decide)\b|^def |^abbrev |^axiom ',text,re.M)
assert len(r['theorem_audits'])==text.count('#print axioms')==5
for a in r['theorem_audits']:assert set(a['axioms'])<={'propext','Classical.choice','Quot.sound'}
subprocess.run([sys.executable,'-B','-X','utf8',str(HERE/'scripts/select_sources.py')],check=True)
s=read(HERE/'data/source-selection.json')
assert s['selected_entries']==1378 and s['distinct_full_source_roots']==1383
assert len(s['unselected_source_roots'])==5 and s['full_source_keys_not_needed']==5
assert s['selected_counts']=={'R4':732,'K6':635,'R4b':11}
assert s['absent_generated_semantic_sources']==0 and s['absent_generated_refutation_sources']==1378
for u in s['upstream']:assert sha(ROOT/u['local_path'])==u['sha256']
out=dict(status='PASS_EXACT_REFERENCE_UNION_INTERFACE',modules=[dict(module=name,receipt_sha256=sha(rp),theorem_audits=5)],
    theorem_audits=r['theorem_audits'],new_definitions=0,
    source_selection_sha256=sha(HERE/'data/source-selection.json'),environment_sha256=sha(HERE/'data/environment.json'),
    selected_reference_keys=1378,full_source_roots=1383,unused_source_roots=5,
    reference_union_refutation_checked=False,complete_graph_potential_certificates_checked=False,
    scope='Five general implications passed Lean. The exact reference-union refutation, complete graph checks, and five conditional share premises remain unproved here. The source audit supplies no closed refutation.')
(HERE/'data/proof-summary.json').write_text(json.dumps(out,indent=2)+'\n')
print(out['status'],'5 theorem audits; no definitions; union and complete graph still pending')
