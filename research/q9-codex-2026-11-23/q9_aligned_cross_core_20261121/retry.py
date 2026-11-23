from pathlib import Path
import subprocess,json,sys
D=Path(__file__).resolve().parent
rows=(D/'cases.dat').read_text().splitlines()
mode=sys.argv[1]; cap=int(sys.argv[2])
with (D/(mode+'_retry.dat')).open('w') as dst,(D/(mode+'_retry_index.jsonl')).open('w') as ix:
    for l in (D/(mode+'.log')).open():
        f=l.split()
        if f[0]!='ROW':continue
        row,omit,nodes,leaves,graphs,low,dead,unknown,cut,found=map(int,f[1:])
        if not (cut or unknown):continue
        n,k,m,*v=map(int,rows[row].split());core=v[:k];pool=v[k:]
        if omit>=0:core.remove(omit)
        print(n,len(core),m,*core,*pool,file=dst)
        print(json.dumps([row,omit]),file=ix)
with (D/(mode+'_retry.dat')).open() as inp,(D/(mode+'_retry.log')).open('w') as out:
    subprocess.run(['/tmp/q9_cross_core21',str(cap),'0','192','711226'],stdin=inp,stdout=out,check=True)
