from pathlib import Path
import subprocess
root=Path(__file__).resolve().parent
def canon(w):
    m={};return ''.join(m.setdefault(c,chr(65+len(m))) for c in w)
paths=(root.parent/'q9_gap_generations/prior191.words').read_text().split()
for a,b in [(95,95),(94,95),(95,93),(94,94),(93,94),(92,94),(95,90),(94,91),(95,88),(94,88),(92,88),(90,90),(94,84),(93,82),(91,82),(95,78),(90,78),(95,72)]:
    f=root/f'known191_{b}.words'
    if not f.exists():
        keys={canon(z) for w in paths for j in range(len(w)-b+1) for z in (w[j:j+b],w[j:j+b][::-1])}
        f.write_text('\n'.join(sorted(keys))+'\n')
    log=root/f'short_{a}_{b}.log'
    with log.open('w') as out:subprocess.run([str(root/'detours'),str(root/f'eligible8_{a}.words'),str(f),'192','0','1000000','83833'],stdout=out,check=True)
    last=log.read_text().splitlines()[-1];print(a,b,last,flush=True)
    if last.startswith('FOUND'):break
