import gzip,json,re,sys
from collections import Counter,defaultdict
from pathlib import Path
d=Path(__file__).resolve().parent
r=d.parent
def canon(w):
    def norm(w):
        m={}
        return bytes(m.setdefault(i,len(m))+48 for i in w)
    return min(norm(w),norm(w[::-1]))
fields=re.compile(rb'[0-8]{189,191}')
bank={k:set() for k in (189,190,191)}
files=[]
for p in sorted(set(r.glob('**/*.words'))|set(r.glob('**/*.words.gz'))):
    if d in p.parents:continue
    if p.suffix=='.gz':
        with gzip.open(p,'rb') as f: data=f.read()
    else:data=p.read_bytes()
    words=set(token for token in data.split() if fields.fullmatch(token))
    if words:files.append(str(p.relative_to(r)))
    for w in words:
        for n in range(189,len(w)+1):
            for i in range(len(w)-n+1):bank[n].add(canon(w[i:i+n]))
observed={k:set() for k in bank}
for name in sys.argv[1:]:
    for line in (d/(name+'.witness')).read_text().splitlines():
        row=list(map(int,line.split()));n=row[0]
        if n<189:continue
        p=row[16:]; assert len(p)==n+1
        w=bytes(48+(a^b).bit_length()-1 for a,b in zip(p,p[1:]))
        observed[n].add(canon(w))
result={'read_files':files,'files_containing_tokens':len(files),'bank_sizes':{},'generated_sizes':{},'outside_sizes':{}}
for n in bank:
    new=sorted(observed[n]-bank[n])
    result['bank_sizes'][n]=len(bank[n]);result['generated_sizes'][n]=len(observed[n]);result['outside_sizes'][n]=len(new)
    (d/('outside_wordbanks'+str(n)+'.words')).write_bytes(b''.join(w+b'\n' for w in new))
(d/'shorter.json').write_text(json.dumps(result,indent=2)+'\n');print({k:v for k,v in result.items() if k!='read_files'})
