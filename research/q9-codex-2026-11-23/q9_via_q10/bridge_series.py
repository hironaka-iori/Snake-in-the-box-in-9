import itertools
from pathlib import Path
import subprocess
import sys
root=Path(__file__).resolve().parent
def canon(w):
    m={}
    return ''.join(m.setdefault(c,chr(65+len(m))) for c in w)
if sys.argv[1]=='controls':
    bank=(root.parent/'q9_gap_generations/prior191.words').read_text().split()
    for i,w in enumerate(bank):
        left,right=canon(w[:95][::-1]),canon(w[97:])
        a=root/'check_bridge_a.words';b=root/'check_bridge_b.words';a.write_text(left+'\n');b.write_text(right+'\n')
        res=subprocess.run([str(root/'floating'),str(a),str(b),'191','0','1','7'],text=True,capture_output=True,check=True)
        fields=res.stdout.split();assert fields[0]=='FOUND'
        p=list(map(int,fields[3:]));assert len(p)>=192 and len(set(p))==len(p)
        assert all((x^p[j]).bit_count()!=1 if j+1<i else (x^p[j]).bit_count()==1 for i,x in enumerate(p) for j in range(i))
        print(i,len(p)-1,flush=True)
else:
    for a,b,n in (('q8_98','q8_97',196),('q8_97','q8_97',195),('q8_98','q8_96',195),('q8_98','combined98',196),('q8_98','combined97',196),('q8_98','combined96',195),('q8_97','q8_96',193),('q8_96','q8_96',192),('q8_97','combined97',195)):
        file=root/f'float_{a}_{b}.log'
        with file.open('w') as out:subprocess.run([str(root/'floating'),str(root/(a+'.words')),str(root/(b+'.words')),str(n),'0','1000000','113'],stdout=out,check=True)
        last=file.read_text().splitlines()[-1];print(a,b,n,last,flush=True)
        if last.startswith('FOUND'):break
