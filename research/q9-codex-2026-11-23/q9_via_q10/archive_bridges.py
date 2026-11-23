import subprocess
from pathlib import Path
root=Path(__file__).resolve().parent
words=(root.parent/'q9_gap_generations/prior191.words').read_text().split()
def canon(w):
    m={};return ''.join(m.setdefault(x,chr(65+len(m))) for x in w)
for n in (94,92,88,82,76,70):
    arm=root/f'known191_{n}.words'
    s=set()
    for w in words:
        for j in range(len(w)-n+1):
            z=w[j:j+n];s.update((canon(z),canon(z[::-1])))
    arm.write_text('\n'.join(sorted(s))+'\n')
    print('BANK',n,len(s),flush=True)
for a,b,t,lo,hi in [(98,94,192,0,2),(98,92,192,0,2),(98,88,192,0,2),(98,82,192,0,2),(97,94,192,0,52),(97,92,192,0,52),(98,76,192,0,2),(96,94,192,0,80),(96,92,192,0,80),(98,70,192,0,2),(97,88,192,0,52),(96,88,192,0,128)]:
    log=root/f'bridge8_{a}_9_{b}.log'
    with log.open('w') as out:subprocess.run([str(root/'detours'),str(root/f'q8_{a}.words'),str(root/f'known191_{b}.words'),str(t),str(lo),str(hi),'17437'],stdout=out,check=True)
    line=log.read_text().splitlines()[-1];print(a,b,line,flush=True)
    if line.startswith('FOUND'):break
