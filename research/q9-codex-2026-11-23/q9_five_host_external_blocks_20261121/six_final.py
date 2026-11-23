from pathlib import Path
from cd_retry import exact_cube
from pool_sat import rows
D=Path(__file__).resolve().parent
hosts=list(map(set,rows('q8_all_191_positive.hosts')))
for l in (D/'six_probe.log').read_text().splitlines():
    t=l.split()
    if t[0]!='LIMIT':continue
    row,mask,base=map(int,t[1:4]);S=hosts[row]|{v for v in range(512) if v&~mask==base}
    st,w=exact_cube(S,192,150000)
    print(st,row,mask,base,'outside',len(S-hosts[row]),'vertices',*(w or []),flush=True)
    if w:break
print('DONE',flush=True)

