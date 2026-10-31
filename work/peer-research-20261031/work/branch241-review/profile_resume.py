import sys,gzip,json,time,cProfile,pstats,io
from pathlib import Path
H=Path(__file__).resolve().parent;B=H.parent/'branch241-next';sys.path[:0]=[str(B),str(B/'encoding')]
from github_query import build
from solver import Solver
from rup_check import check
D=H/'loop_k3_cap254_r4_d0120_all8';t=time.perf_counter()
with gzip.open(D/'checkpoint.json.gz','rt') as f:s=json.load(f)
with gzip.open(D/'static8.json.gz','rt') as f:m=json.load(f)
E,_,_,_=build([0,1,3,7,6],254);cs=E.cnf.clauses+[[-E.var[v] for v in c] for c in m['cycles'] if not set(c)&E.forbidden];base_done=time.perf_counter()
prof=cProfile.Profile();prof.enable();solver=Solver(cs+[p['clause'] for p in s['prefix_proof']],E.cnf.nv,primary=E.var.values(),phase_true=E.var.values());prof.disable();init_done=time.perf_counter()
check(cs,s['prefix_proof'],False);check_done=time.perf_counter();a=json.dumps(s,separators=(',',':')).encode();encode_done=time.perf_counter();gzip.compress(a,compresslevel=1);zip_done=time.perf_counter()
r={'load_build_seconds':base_done-t,'solver_init_seconds':init_done-base_done,'full_prefix_check_seconds':check_done-init_done,'checkpoint_encode_seconds':encode_done-check_done,'checkpoint_compress_seconds':zip_done-encode_done,'proof_steps':len(s['prefix_proof']),'checkpoint_plain_bytes':len(a)}
stream=io.StringIO();pstats.Stats(prof,stream=stream).sort_stats('cumtime').print_stats(15);(H/'resume_profile.txt').write_text(stream.getvalue());(H/'resume_profile.json').write_text(json.dumps(r,indent=2));print(json.dumps(r,indent=2));print(stream.getvalue())
