from pathlib import Path
import gzip,itertools,json,collections
D=Path(__file__).resolve().parent;R=D.parent
def valid(p):return len(p)==len(set(p)) and all(((x^y).bit_count()==1)==(i+1==j) for j,x in enumerate(p) for i,y in enumerate(p[:j]))
def canon(ms):
    cols=sorted(range(9),key=lambda k:tuple((m>>k)&1 for m in ms),reverse=True)
    table={v:i for i,v in enumerate(cols)}
    return tuple(sum(1<<table[k] for k in range(9) if (m>>k)&1) for m in ms)
def emit():
    records={}
    def add(p,origin,idx,offset):
        ms=tuple(x^y for x,y in zip(p[::2],p[2::2]));assert len(ms)==48 and all(v.bit_count()==2 for v in ms)
        for rev in range(2):
            k=canon(ms[::-1] if rev else ms);v=records.setdefault(k,{});v.setdefault(origin,[idx,offset,rev])
    pub=[list(map(int,l.split())) for l in gzip.open(R/'q9_port_followup_public191.txt.gz','rt')]
    for i,p in enumerate(pub):
        assert len(p)==192 and valid(p)
        for j in range(96):add(p[j:j+97],'public',i,j)
    for dim in range(10,14):
        ws=(R/'q9_via_q10'/f'arms_{dim}_96.words').read_text().split()
        for i,w in enumerate(ws):
            p=[0]
            for c in w:p.append(p[-1]^1<<(ord(c)-65))
            assert len(p)==97 and valid(p)
            add(p,str(dim),i,0)
    words=sorted(records);(D/'arms.txt').write_text(''.join(' '.join(map(str,k))+'\n' for k in words))
    (D/'provenance.json').write_text(json.dumps([records[k] for k in words],separators=(',',':')))
    print(len(words),collections.Counter(f for a in records.values() for f in a))
if __name__=='__main__':emit()
