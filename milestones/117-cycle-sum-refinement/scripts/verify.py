"""Check exact proof evidence, finite comparisons and the unchanged manuscript."""
from pathlib import Path
from fractions import Fraction
import hashlib,json,re
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
def sha(path):
    h=hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda:f.read(1024*1024),b''):h.update(block)
    return h.hexdigest()
pins={}
def pin(path):pins[path.relative_to(ROOT).as_posix()]=sha(path)
for name in ['probe-audit.json','witness-audit.json','graph-audit.json','replay-core0.json','012034-middle5-outer15-certificate.json']:
    pin(HERE/'data'/name)
probes=read(HERE/'data/probe-audit.json')
assert len(probes['probes'])==5
for row in probes['probes']:assert sha(HERE/row['probe'])==row['sha256']
assert len(read(HERE/'data/witness-audit.json')['witnesses'])==1
probe=read(HERE/'data/probes/012034-middle5-outer15.json')
assert probe['directions']==[0,1,2,0,3,4] and probe['bounds']==[[0,21],[0,21],[0,5],[0,21],[0,21]]
assert probe['positions']==[0,1,3,4] and probe['cap']==15 and probe['cycle_cuts']==[]
meta=read(HERE/'data/012034-middle5-outer15-certificate.json')
work=HERE/'work/012034-middle5-outer15'
assert meta['status']=='NATIVE_SUM_CERTIFICATE_REPLAYED_LEAN_PENDING'
assert meta['window']==[0,1,3,7,6,14,30] and meta['positions']==[0,1,3,4] and meta['sum_cap']==15
for name,key in [('full.cnf','cnf_sha256'),('core.cnf','core_sha256'),('full.trim.lrat','lrat_sha256')]:assert sha(work/name)==meta[key]
assert (meta['core_clauses'],meta['lemmas'],meta['hints'])==(5662,159380,13252922)
refine=read(HERE/'data/refine-core0.json');replay=read(HERE/'data/replay-core0.json')
assert sha(HERE/'data/refine-core0.json')==replay['refinement_sha256']
assert sha(HERE/refine['cnf'])==refine['cnf_sha256']==replay['core_cnf_sha256']
assert sha(HERE/refine['trim'])==refine['trim_sha256']==replay['lrat_sha256']
assert replay['status']=='PASS_REFINED_RUP_IN_ORIGINAL_FORMULA'
assert (replay['deductions'],replay['hints'],len(replay['active_variables']))==(142180,8712029,1709)
receipt_path=HERE/'data/SumGeometry117-audit.json';receipt=read(receipt_path)
assert receipt['status']=='PASS_CONDITIONAL_SUM_GEOMETRY_AND_COMPARISON' and receipt['exit_code']==0
source=HERE/'lean/SumGeometry117.lean';object_path=HERE/'build-geometry/SumGeometry117.olean'
assert sha(source)==receipt['source_sha256']==sha(HERE/receipt['source_snapshot'])
assert sha(object_path)==receipt['olean_sha256'] and sha(HERE/receipt['log'])==receipt['log_sha256']
assert sha(HERE/'scripts/check_geometry.py')==receipt['checker_sha256']==sha(HERE/receipt['checker_snapshot'])
for path,digest in receipt['dependencies'].items():assert sha(Path(path))==digest,path
assert len(receipt['theorem_audits'])==3
for item in receipt['theorem_audits']:assert set(item['axioms'])<={'propext','Classical.choice','Quot.sound'}
text=source.read_text(encoding='utf-8')
assert '(hlocal :' in text and not re.search(r'\b(def|sorry|admit|native_decide)\b',text)
for path in [source,receipt_path,HERE/receipt['log'],HERE/receipt['source_snapshot'],HERE/receipt['checker_snapshot']]:pin(path)
result=read(HERE/'data/middle5-outer16/results.json')
assert len(result['rules'])==11 and result['coefficients']==[24]*5
expected=[('2915/6','1730/3','1324108/5623',235,18),('496','602','551765/2348',234,3)]
for profile,(mean,span,bound,integer,length) in zip(result['profiles'],expected):
    assert profile['all_edge_inequalities_checked']
    assert (profile['mean'],profile['range'],profile['comparison_bound'],profile['comparison_integer_bound'],len(profile['cycle']))==(mean,span,bound,integer,length)
    assert Fraction(1098960*profile['d']+8*profile['p']+profile['range_scaled'],4200*profile['d']+profile['p'])==Fraction(bound)
assert Fraction(2915,6)-Fraction(6309,13)==Fraction(41,78)
assert Fraction(7656,13)-Fraction(1730,3)==Fraction(478,39)
assert 111960*6-227*2915==10055
previous=read(ROOT/'milestones/115-total-count-certificate/data/universal345-total22/results.json')
assert previous['edges']-result['edges']==23285
pin(HERE/'data/middle5-outer16/results.json')
oldpaper=read(ROOT/'milestones/116-paper-revision/data/checkpoint.json')['paper_sha256']
assert sha(ROOT/'paper/snake9_research.tex')==oldpaper==sha(Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex'))
archive=read(HERE/'data/large-artifact-archives.json')
for row in archive['files']:
    assert sha(HERE/row['original'])==row['sha256'] and sha(HERE/row['archive'])==row['archive_sha256']
out=dict(status='PASS_EXACT117_EVIDENCE',source_pins=pins,successful_lean_modules=1,printed_axiom_reports=3,
    new_definitions=0,actual_local_theorem_checked=False,native_original_replay_checked=True,native_refined_replay_checked=True,
    new_global_bound=False,maintained_edge_interval=[191,235],conditional_target=234,paper_revision=116,paper_sha256=oldpaper,
    scope='Exact hashes and retained successful receipts, conditional Lean transfer/arithmetic, local controls and saved finite comparison data. No clean dependency rebuild, concrete Lean contradiction, revised global interpretation or new upper bound.')
target=HERE/'data/verification.json';assert not target.exists();target.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(out['status'],'one conditional Lean module, three axiom reports, no new bound')
