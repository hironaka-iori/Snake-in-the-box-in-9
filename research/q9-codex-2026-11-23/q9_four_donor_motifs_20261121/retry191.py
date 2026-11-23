from pathlib import Path
import subprocess
D=Path(__file__).resolve().parent
cases=[int(l.split()[1]) for l in (D/'stepping.log').read_text().splitlines() if l.startswith('LIMIT')]
fields=[l for l in (D/'wide.log').read_text().splitlines() if l.startswith('FIELD')]
for i in cases:
    labels,raw=fields[i-1].split(" vertices");vs=list(map(int,raw.split()));pos=0;arcs=[]
    for tag in labels.split()[2:]:
        a,b=map(int,tag.split('/')[-1].split('-'));n=b-a+1;arcs.append(vs[pos+2:pos+n-2]);pos+=n
    goal=191;missing=goal+1-sum(map(len,arcs))
    data=[goal,missing+1,missing,len(arcs)]
    for s in arcs:data.extend([len(s),*s])
    result=subprocess.check_output(['/tmp/q9_four_donor_191_retry'],input=' '.join(map(str,data))+'\n',text=True)
    print(i,result.strip(),flush=True)

