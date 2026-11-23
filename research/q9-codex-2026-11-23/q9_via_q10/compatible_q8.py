"""Largest continuous archived Q8 second arm compatible with the archived 98-edge first arm."""
from pathlib import Path
import subprocess
root=Path(__file__).resolve().parent
bank=(root.parent/'q8_catalogue_96_98.words').read_text().split()
def canon(w):
    m={}
    return ''.join(m.setdefault(x,chr(65+len(m))) for x in w)
def test(n,tool):
    b=root/f'q8_{n}.words'
    if not b.exists():
        s=set()
        for w in bank:
            for i in range(len(w)-n+1):
                a=w[i:i+n];s.add(canon(a));s.add(canon(a[::-1]))
        b.write_text('\n'.join(sorted(s))+'\n')
    cmd=[str(root/tool),str(root/'q8_98.words'),str(b)]
    cmd+=['0','3477'] if tool=='cross_arms' else ['0','0','1000000','3477']
    result=subprocess.run(cmd,check=True,text=True,capture_output=True)
    last=result.stdout.strip().splitlines()[-1]
    (root/f'q8_98_{tool}_{n}.log').write_text(result.stdout)
    print(tool,n,last.split()[:4],flush=True)
    return last.startswith('FOUND ')
for tool in ('cross_arms','floating'):
    lo,hi=0,99
    while hi-lo>1:
        n=(lo+hi)//2
        if test(n,tool):lo=n
        else:hi=n
    print('maximum_secondary_arm',tool,lo,flush=True)
