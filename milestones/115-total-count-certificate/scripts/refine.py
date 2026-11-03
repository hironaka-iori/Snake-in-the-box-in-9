"""Bounded native proof refinement; preserve originals and every attempt."""
from pathlib import Path
import argparse, datetime, hashlib, importlib.util, json, os, shutil, subprocess, tempfile, time

HERE=Path(__file__).resolve().parents[1]; ROOT=HERE.parents[1]
OLD=ROOT/'milestones/114-total-count-pressure'
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
    return h.hexdigest()
parser=argparse.ArgumentParser()
parser.add_argument('name');parser.add_argument('--seed',type=int,default=1)
parser.add_argument('--preset',choices=['default','unsat','plain'],default='default')
parser.add_argument('--parent');parser.add_argument('--timeout',type=int,default=60)
args=parser.parse_args()
assert args.name.replace('-','').isalnum()
for d in ['data','logs','work']:(HERE/d).mkdir(exist_ok=True)
record=HERE/'data'/('refine-'+args.name+'.json');assert not record.exists()
meta_path=OLD/'data/012310-total18-certificate.json';meta=read(meta_path)
assert meta['status']=='NATIVE_SUM_CERTIFICATE_REPLAYED_LEAN_PENDING'
fullpath=OLD/'work/012310-total18/full.cnf';assert sha(fullpath)==meta['cnf_sha256']
full=[[int(x) for x in l.split()[:-1]] for l in fullpath.read_text().splitlines() if l and not l.startswith(('p','c'))]
ids=meta['core_ids'];parent_sha=None
if args.parent:
    parent_path=HERE/'data'/('refine-'+args.parent+'.json');parent=read(parent_path)
    assert parent['status']=='UNSAT_TRIMMED_NOT_REPLAYED'
    ids=parent['used_original_ids'];parent_sha=sha(parent_path)
assert len(ids)==len(set(ids)) and all(0<i<=len(full) for i in ids)
scratch=Path(tempfile.mkdtemp(prefix='snake115-'+args.name+'-'))
cnf=scratch/'core.cnf';raw=scratch/'core.raw.lrat';trim=scratch/'core.trim.lrat'
cnf.write_bytes((f'p cnf {meta["variables"]} {len(ids)}\n'+''.join(' '.join(map(str,full[i-1]))+' 0\n' for i in ids)).encode())
exe=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin/cadical.exe')
assert sha(exe)=='4fb5f4f94a3632c185ea763f7da627d40038cca38d9481952d00d04cc881c94f'
command=[str(exe),'-q','--lrat','--no-binary','--seed='+str(args.seed)]
if args.preset!='default':command.append('--'+args.preset)
command += [str(cnf),str(raw)]
out=dict(status='RUNNING',pid=os.getpid(),started_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    name=args.name,command=command,timeout_seconds=args.timeout,solver_sha256=sha(exe),script_sha256=sha(Path(__file__)),
    prior_certificate_sha256=sha(meta_path),full_cnf_sha256=sha(fullpath),parent_sha256=parent_sha,
    input_ids=ids,input_clauses=len(ids),scratch=str(scratch),cnf_sha256=sha(cnf),variables=meta['variables'])
def save():record.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
save();start=time.monotonic()
try:
    proc=subprocess.run(command,capture_output=True,timeout=args.timeout)
    stdout,stderr=proc.stdout,proc.stderr
    out.update(status='UNSAT_LRAT_UNCHECKED' if proc.returncode==20 and b's UNSATISFIABLE' in stdout else 'FAILED',exit_code=proc.returncode)
except subprocess.TimeoutExpired as exc:
    stdout,stderr=exc.stdout or b'',exc.stderr or b'';out['status']='TIMEOUT'
out['solver_seconds']=time.monotonic()-start
for label,content in [('stdout',stdout),('stderr',stderr)]:
    p=HERE/'logs'/(args.name+'.'+label+'.log');p.write_bytes(content);out[label+'_sha256']=sha(p)
save();print(args.name,out['status'],round(out['solver_seconds'],3),flush=True)
if out['status']=='UNSAT_LRAT_UNCHECKED':
    generator=ROOT/'milestones/109-relaxed-graph-test/upstream/milestones/10-window-aggregate/scripts/gen_lean_core.py'
    sp=importlib.util.spec_from_file_location('core115',generator);cg=importlib.util.module_from_spec(sp);sp.loader.exec_module(cg)
    start=time.monotonic();nl,nh,used=cg.trim_lrat(str(raw),str(trim),len(ids))
    out.update(status='UNSAT_TRIMMED_NOT_REPLAYED',lemmas=nl,hints=nh,used_core=len(used),
        used_original_ids=[ids[i-1] for i in used],trimming_generator_sha256=sha(generator),trim_seconds=time.monotonic()-start)
folder=HERE/'work'/args.name;folder.mkdir()
for label,p in [('cnf',cnf),('raw',raw),('trim',trim)]:
    if p.exists():
        target=folder/p.name;shutil.copyfile(p,target);assert sha(target)==sha(p)
        out[label]=target.relative_to(HERE).as_posix();out[label+'_sha256']=sha(target);out[label+'_bytes']=target.stat().st_size
out['scope']='Native proof generation and dependency trim only. Complete independent replay and Lean certification remain separate.'
save();print(args.name,out['status'],'steps',out.get('lemmas'),'hints',out.get('hints'),flush=True)
