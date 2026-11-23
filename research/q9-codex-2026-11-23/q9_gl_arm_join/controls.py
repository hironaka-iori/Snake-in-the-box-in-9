from bank import *
from random import Random
ws=(D/'sources.txt').read_text().split();mut={}
for line in (D/'transformed.txt').open():
    w,i,u,v,orig=line.split()
    if int(u) and not int(orig):mut.setdefault(ws[int(i)],[]).append(w)
def c(w):return min(normalize(w),normalize(w[::-1]))
opts=[]
with gzip.open(D.parent/'q9_port_followup_public191.txt.gz','rt') as f:
    for i,row in enumerate(f):
        p=list(map(int,row.split()));w=''.join(str((a^b).bit_length()-1) for a,b in zip(p,p[1:]))
        for cut in range(93,99):
            for gap in [0,1]:
                a=c(w[:cut]);b=c(w[cut+gap:])
                if a in mut and b in mut:opts.append((i,cut,gap,a,b))
rng=Random(90467);rng.shuffle(opts);selected=[];mothers=set()
for i,cut,gap,a,b in opts:
    if i in mothers:continue
    mothers.add(i);aa=rng.choice(mut[a]);bb=rng.choice(mut[b]);selected.append((i,cut,gap,a,b,aa,bb))
    if len(selected)>=16:break
(D/'controls.json').write_text(json.dumps(selected))
with (D/'control_words.txt').open('w') as f:
    for i,c,g,a,b,x,y in selected:print(x,y,sep='\n',file=f)
with (D/'control_pairs.txt').open('w') as f:
    for i,c,g,a,b,x,y in selected:
        print(i,g,x,y,file=f)
        print(i,g,a,b,file=f)
