import gzip,hashlib,json,sys,tempfile,subprocess
from pathlib import Path
from pysat.solvers import Glucose4
from pysat.formula import CNF
from search import encode,here
binary=sys.argv[1];replay='--replay' in sys.argv
record=[]
for L in (190,191):
    words=(here.parent/f'q9_gap_generations/prior{L}.words').read_text().splitlines()
    candidates=[r for f in sorted(here.glob(f'run{L}_*.jsonl')) for r in map(json.loads,f.read_text().splitlines()) if r[4]=='UNSAT']
    for mode in (0,1):
        _,row,axes,extra,_,_,_,_=min((r for r in candidates if int(any(x>=0 for x in r[3]))==mode),key=lambda r:abs(r[5]-300))
        cnf=encode(words[row],axes,extra,0,return_clauses=True)
        proof_file=here/f'global{L}-{mode}.drat.gz'
        if not replay:
            with Glucose4(bootstrap_with=cnf,with_proof=True) as sat:
                assert sat.solve() is False
                data=('\n'.join(sat.get_proof())+'\n').encode()
            with gzip.open(proof_file,'wb') as fh:fh.write(data)
        else:
            with gzip.open(proof_file,'rb') as fh:data=fh.read()
        with tempfile.TemporaryDirectory() as temp:
            f=Path(temp)/'case.cnf';trace=Path(temp)/'proof.drat'
            CNF(from_clauses=cnf).to_file(str(f));trace.write_bytes(data)
            result=subprocess.run([binary,str(f),str(trace)],capture_output=True)
            assert b's VERIFIED' in result.stdout,(result.returncode,result.stdout[-400:])
            print(json.dumps([L,row,axes,extra,hashlib.sha256(f.read_bytes()).hexdigest(),proof_file.name,'VERIFIED']),flush=True)
