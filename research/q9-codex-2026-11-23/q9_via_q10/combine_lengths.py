from pathlib import Path
import subprocess
import sys
root=Path(__file__).resolve().parent
for spec in sys.argv[1:]:
    a,b=spec.split('-')
    with (root/f'join_{a}_{b}.log').open('w') as out:
        subprocess.run([str(root/'cross_arms'),str(root/(a+'.words')),str(root/(b+'.words')),'0','31397'],check=True,stdout=out)
    last=(root/f'join_{a}_{b}.log').read_text().splitlines()[-1]
    print(a,b,last,flush=True)
    if last.startswith('FOUND'):break
