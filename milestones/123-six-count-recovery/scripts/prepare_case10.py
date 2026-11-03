"""Recover and reduce the saved case10 certificate without a new solver run."""
from pathlib import Path
import gzip,hashlib,importlib.util,json,sys
H=Path(__file__).resolve().parents[1];R=H.parents[1];P=R/'milestones/32-seven-count-four-screen'
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
sys.path[:0]=[str(R/'milestones/10-window-aggregate/scripts'),str(R/'work/share_packages')]
from gen_lean_sat import TaggedEncoding
from wincert import Encoding,window_from_dirs
case=read(P/'data/cases.json')[10];meta=read(P/'data/four10.json')
assert case==dict(dirs=[0,1,2,3,0,4,2],bounds=[[4,4]]*6)
assert meta['dirs']==case['dirs'] and meta['bounds']==case['bounds']
def clauses(p):return [list(map(int,line.split()))[:-1] for line in p.read_text().splitlines() if line.strip() and not line.startswith(('c','p'))]
enc=TaggedEncoding(window_from_dirs(case['dirs']),[tuple(x) for x in case['bounds']],radius=4)
plain=Encoding(enc.window,[tuple(x) for x in case['bounds']],radius=4)
assert plain.clauses==enc.clauses==clauses(P/'certificates/four10.full.cnf')
rename={int(k):v for k,v in meta['original_to_new'].items()}
assert set(rename)==set(enc.meaning) and set(rename.values())==set(range(1,enc.nv+1))
lit=lambda a:(1 if a>0 else -1)*rename[abs(a)]
compact=[[lit(a) for a in enc.clauses[k-1]] for k in meta['source_original_clause_ids']]
assert compact==clauses(P/'certificates/four10.cnf')
assert len(compact)==4488 and max(abs(a) for c in compact for a in c)==meta['active_variables']==1640
work=H/'work/four10';work.mkdir(exist_ok=True)
(work/'four10.cnf').write_bytes((P/'certificates/four10.cnf').read_bytes())
sources=[P/'data/cases.json',P/'data/four10.json',P/'data/native-inventory.json',P/'logs/four10-export.txt',
    P/'certificates/four10.full.cnf',P/'certificates/four10.cnf',P/'certificates/four10.lrat',
    P/'lean/LocalWindowCnf/FourRun10.lean',P/'lean/LocalWindowSat/FourRun10.lean']
archive=H/'audit/case10-original';archive.mkdir(exist_ok=True)
saved=[]
for p in sources:
    q=archive/(p.relative_to(P).as_posix().replace('/','__')+'.gz');data=p.read_bytes()
    q.write_bytes(gzip.compress(data,compresslevel=6,mtime=0))
    assert gzip.decompress(q.read_bytes())==data
    saved.append(dict(source=p.relative_to(R).as_posix(),sha256=sha(p),archive=q.relative_to(H).as_posix(),archive_sha256=sha(q)))
tool=R/'milestones/109-relaxed-graph-test/upstream/milestones/10-window-aggregate/scripts/gen_lean_core.py'
spec=importlib.util.spec_from_file_location('core123',tool);gen=importlib.util.module_from_spec(spec);spec.loader.exec_module(gen)
trim=work/'four10.lrat';nl,nh,ids=gen.trim_lrat(str(P/'certificates/four10.lrat'),str(trim),len(compact))
old=read(P/'logs/four10-export.txt')
out=dict(status='ENCODING_REBUILT_AND_SAVED_REFUTATION_TRIMMED_LEAN_PENDING',case=case,
    original_lemmas=old['lemmas'],original_hints=old['hints'],trimmed_lemmas=nl,trimmed_hints=nh,
    retained_core_ids=ids,retained_core_clauses=len(ids),active_variables=1640,meaning_variables=enc.nv,
    cnf_sha256=sha(work/'four10.cnf'),lrat_sha256=sha(trim),sources=saved,
    generator=tool.relative_to(R).as_posix(),generator_sha256=sha(tool),script_sha256=sha(Path(__file__)),
    encoding_pins={p.relative_to(R).as_posix():sha(p) for p in [R/'milestones/10-window-aggregate/scripts/gen_lean_sat.py',R/'milestones/10-window-aggregate/scripts/wincert.py']},
    scope='Ordinary full encoding and renamed core match saved inputs. Backward proof reduction only; replay and arbitrary-snake theorem not yet checked.')
(H/'data/case10-recovery.json').write_text(json.dumps(out,indent=2)+'\n')
print('Original',old['lemmas'],old['hints'],'trimmed',nl,nh,'core',len(ids),flush=True)
