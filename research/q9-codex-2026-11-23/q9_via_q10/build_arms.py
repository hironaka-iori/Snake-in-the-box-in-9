from pathlib import Path
import subprocess
import sys
root=Path(__file__).resolve().parent
def save(file,keys):file.write_text('\n'.join(sorted(keys))+'\n')
def canonical(w):
    m={}
    return ''.join(m.setdefault(x,chr(65+len(m))) for x in w)
for n in map(int,sys.argv[1:]):
    q8=set()
    for w in (root.parent/'q8_catalogue_96_98.words').read_text().split():
        for j in range(len(w)-n+1):
            q8.update((canonical(w[j:j+n]),canonical(w[j:j+n][::-1])))
    save(root/f'q8_{n}.words',q8)
    unions=set()
    for d in (10,11,12,13):
        dst=root/f'arms_{d}_{n}.words'
        log=root/f'arms_{d}_{n}.log'
        if not log.exists() or not log.read_text().splitlines()[-1].startswith('DONE'):
            src=root/(f'donors{d}.txt' if d>11 else 'donors.txt')
            with log.open('w') as f:subprocess.run([str(root/'arm_bank'),str(d),str(n),str(src),str(dst)],check=True,stdout=f)
        unions.update(dst.read_text().split())
    save(root/f'combined{n}.words',unions)
    print(n,len(q8),len(unions),len(q8&unions),flush=True)
