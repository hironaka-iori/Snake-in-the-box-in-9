"""Enumerate every cut for a fixed goal. Mirror cuts are kept: donors are oriented."""
from pathlib import Path
import subprocess
import sys

root=Path(__file__).resolve().parent
n=int(sys.argv[1])
for cut in sorted(range(1,n),key=lambda k:abs(k-n/2)):
    cmd=[str(root/'hinge'),str(n),str(cut),'1','0',str(root/'donors.txt'),'1']
    result=subprocess.run(cmd,check=True,capture_output=True,text=True)
    last=result.stdout.splitlines()[-1]
    assert last.startswith(('FOUND ','DONE '))
    print(cut,last,flush=True)
    if last.startswith('FOUND '):
        break
