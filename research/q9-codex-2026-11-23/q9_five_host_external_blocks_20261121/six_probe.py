from pathlib import Path
from cd_retry import exact_cube
from pool_sat import rows
D=Path(__file__).resolve().parent
raw=list(map(set,rows('q8_all_191_positive.hosts')))
todo={}
for line in (D/'cover_sat.log').read_text().splitlines():
    t=line.split()
    if t[0]!='LIMIT':continue
    row,mask,base=map(int,t[1:4])
    if mask.bit_count()!=6:continue
    todo.setdefault((row,mask),[]).append(base)
for (row,mask),bases in sorted(todo.items()):
    b=sorted(bases)[(row+mask)%len(bases)]
    F={x for x in range(512) if (x&~mask)==b}
    st,w=exact_cube(raw[row]|F,192,12000)
    print(st,row,mask,b,'external',len(F-raw[row]),'vertices',*(w or []),flush=True)
    if w:break
print('DONE',flush=True)

