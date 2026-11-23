"""Independently validate all generated transition words and compare normalized shapes."""
from pathlib import Path
import gzip,json,re,sys
D=Path(__file__).resolve().parent;R=D.parent
def canonical(w):
    def norm(s):
        assigned={};return ''.join(str(assigned.setdefault(c,len(assigned))) for c in s)
    return min(norm(w),norm(w[::-1]))
def verify(w):
    assert re.fullmatch(r'[0-8]+',w)
    p=[0]
    for d in w:p.append(p[-1]^1<<int(d))
    assert len(set(p))==len(p)
    for i in range(len(p)):
        assert all(((p[i]^v).bit_count()==1)==(j+1==i) for j,v in enumerate(p[:i]))
    return p
def main():
    bank={n:set() for n in range(187,193)}
    names=json.loads((R/'q9_fresh189_multirewire_20261121/bank_files.json').read_text())+['q9_fresh189_multirewire_20261121/combinednew189.words','q9_mobile_middle/planted189.words']
    for name in names:
        f=R/name;data=gzip.open(f,'rb').read() if name.endswith('.gz') else f.read_bytes()
        for raw in set(data.split()):
            if not re.fullmatch(rb'[0-8]{187,192}',raw):continue
            w=raw.decode()
            for n in bank:
                for i in range(len(w)-n+1):bank[n].add(canonical(w[i:i+n]))
    found=set();logs={}
    for label in sys.argv[1:]:
        words=set();stats=[]
        for line in (D/(label+'.log')).read_text().splitlines():
            if line.startswith('W '):words.add(canonical(line[2:]))
            if line.startswith(('D ','B ')):stats.append(list(map(int,line.split()[1:])))
        for w in words-found:verify(w)
        found|=words
        logs[label]=dict(rows=len(stats),words=len(words),poses=sum(s[1] for s in stats) if label.startswith('cross') else len(stats),limited=sum(s[2] if label.startswith('cross') else s[4] for s in stats),best=max((len(w) for w in words),default=0))
    report={}
    for n in sorted(set(map(len,found))):
        candidates={w for w in found if len(w)==n}
        new=sorted(candidates-bank.get(n,set()))
        (D/f'new{n}.words').write_text(''.join(w+'\n' for w in new))
        report[n]=dict(total=len(candidates),comparison=len(bank.get(n,set())),outside=len(new))
    print(json.dumps(dict(logs=logs,by_edges=report),indent=2))
if __name__=='__main__':main()
