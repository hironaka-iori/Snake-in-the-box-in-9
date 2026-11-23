"""Read every other workspace plain .txt/.words/.pts/.paths row shaped as a Q9 word/path."""
from verify import *
ref=defaultdict(set); sources=Counter(); classes={}
files=sorted(f for f in ROOT.rglob('*') if f.is_file() and f.suffix in {'.txt','.words','.pts','.paths'} and HERE not in f.parents)
for f in files:
    for line in f.open(errors='replace'):
        t=line.split()
        if len(t)==1 or (len(t)==2 and t[0].isdigit()):
            word=t[-1]
            if len(word) not in (189,190,191,192) or set(word)-set('012345678'):continue
        elif len(t) in (190,191,192,193) and all(x.isdigit() for x in t):
            p=list(map(int,t))
            if max(p)>511 or len(set(p))!=len(p) or not all((a^b).bit_count()==1 for a,b in zip(p,p[1:])):continue
            word=wfrom(p)
        else:continue
        w=canon(word)
        if w not in classes:
            p=vertices(w);classes[w]=len(chords(p)) if len(set(p))==len(p) else -1
        e=classes[w]
        if e<0:continue
        ref[len(w),e].add(w);sources[str(f.relative_to(ROOT))]+=1
comparison={}
for n in (189,190,191):
    raw=readwords(HERE/f'true{n}_all.words')
    new=raw-ref[n,0]
    (HERE/f'true{n}_outside_plainfiles.words').write_text(''.join(w+'\n' for w in sorted(new)))
    comparison[f'true{n}']=dict(found=len(raw),reference=len(ref[n,0]),outside=len(new))
for e in (1,2):
    raw=set()
    for f in ['insertion.log','repair.log','insertion190.log','insertion189b.log','repair2.log']:
        for line in (HERE/f).open():
            t=line.split()
            if (t[0]=='NEAR' and int(t[1])==e) or (t[0]=='PATH' and int(t[1])==192 and int(t[2])==e):raw.add(t[-1])
    new=raw-ref[192,e]
    (HERE/f'near192_chords{e}_outside_plainfiles.words').write_text(''.join(w+'\n' for w in sorted(new)))
    comparison[f'near192_{e}']=dict(found=len(raw),reference=len(ref[192,e]),outside=len(new))
print(json.dumps(dict(scanned_files=len(files),matched_files=sources,comparison=comparison),indent=2))
