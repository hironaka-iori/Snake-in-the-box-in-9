from pathlib import Path
from subprocess import run,TimeoutExpired
import json,sys
D=Path(__file__).resolve().parent
def main():
    low,high,limit=map(int,sys.argv[1:]);rows=[]
    for line in (D/'sections.pts').open():
        i,m,b,n=map(int,line.split(maxsplit=4)[:4])
        if low<=n<=high:rows.append((i,m,b,n,line))
    rows.sort(key=lambda x:(x[1].bit_count()==1,-x[3],x[0],x[1],x[2]))
    for i,m,b,n,line in rows:
        try:
            p=run([str(D/'sweep_custom'),str(low),str(high),'0'],input=line,text=True,capture_output=True,timeout=limit,check=True)
            print(p.stdout.strip(),flush=True)
            if 'FOUND' in p.stdout:break
        except TimeoutExpired:print(i,m,b,n,'LIMIT',limit,flush=True)
if __name__=='__main__':main()
