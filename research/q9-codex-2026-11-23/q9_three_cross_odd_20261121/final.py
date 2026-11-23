import argparse,gzip,hashlib,json,subprocess,sys
from collections import Counter
from fractions import Fraction
from pathlib import Path
D=Path(__file__).resolve().parent;R=D.parent;sys.path.insert(0,str(R))
from verify_q9_intact98_all_crossings import integer_bound
def bank():
    frozen=gzip.open(D/'catalogue.words.gz','rb').read();assert frozen==(R/'q8_catalogue_96_98.words').read_bytes()
    words=frozen.decode().split();G={};cases=[]
    for i,w in enumerate(words):
        P=[0]
        for c in w:P.append(P[-1]^(1<<int(c)))
        assert len(set(P))==len(P) and all(((v^P[j]).bit_count()==1)==(j+1==k) for k,v in enumerate(P) for j in range(k))
        G[i]=P;covered=set(P)
        for v in P:covered.update(v^(1<<k) for k in range(8))
        cases.extend((i,x) for x in sorted(set(range(256))-covered))
    assert len(cases)==1496 and len(set(cases))==1496
    return G,cases,hashlib.sha256(frozen).hexdigest()
def choose(cases):
    chosen={}
    for f in ['reuse','timing4','odd8_evenindex','odd8_oddindex','refined1_verified','diffuse_pilot','diffuse_all','hard12']:
        for l in (D/(f+'.jsonl')).read_text().splitlines():
            r=json.loads(l);k=r['i'],r['x'];assert cases[r['rank']]==k
            scr=Fraction(r['bound'],r['scale'])
            if k not in chosen or scr<chosen[k][0]:chosen[k]=scr,dict(rank=r['rank'],i=k[0],x=k[1],cert=r['cert'],bound=r['bound'],scale=r['scale'],source=f)
    assert set(chosen)==set(cases)
    return [chosen[key][1] for key in cases]
def control(G):
    raw=[l.split() for l in (D/'positive.log').read_text().splitlines() if l.startswith('WIT ')]
    b=max(raw,key=lambda r:int(r[1]));n,i,x=map(int,b[1:4]);p=list(map(int,b[4:]));assert len(p)==n+1==len(set(p))
    assert all(((z^p[j]).bit_count()==1)==(j+1==k) for k,z in enumerate(p) for j in range(k))
    assert {z for z in p if z<256}==set(G[i])|{x};ports={z%256 for a,z in zip(p,p[1:]) if a^z==256}
    assert ports=={G[i][0],G[i][-1],x};assert p[0]==x and p[-1]>=256 and (p[0]^p[-1]).bit_count()%2
    return dict(edges=n,case=[i,x],ports=sorted(ports),pairs=n*(n+1)//2,path=p)
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--prepare',action='store_true');a=ap.parse_args()
    G,cases,digest=bank();rows=choose(cases)
    file=D/'manifest.jsonl'
    if a.prepare:
        file.write_text(''.join(json.dumps(r,separators=(',',':'))+'\n' for r in rows));return
    assert [json.loads(l) for l in file.read_text().splitlines()]==rows
    native={ (r['i'],r['x']):r for l in (D/'native_final.jsonl').read_text().splitlines() if (r:=json.loads(l))}
    assert len(native)==len(cases);summary=Counter();lengths=Counter();dedup=set();high=Fraction(0)
    for r in rows:
        i,x=r['i'],r['x'];arr=G[i];L=set(arr)|{x};P={x,arr[0],arr[-1]};m=x.bit_count()%2;ec=[int(z==1-m) for z in (0,1)];delta=sum((-1)**v.bit_count() for v in L)
        c=json.load(gzip.open(D/r['cert'],'rt'));v=integer_bound(c,L,P,ec,delta)+len(L)*c['scale']
        assert c['scale']==r['scale'] and v==r['bound']==native[i,x]['bound'];assert v<194*c['scale']
        summary[r['source']]+=1;lengths[len(arr)-1]+=1;dedup.add(i);high=max(high,Fraction(v,c['scale']))
    con=control(G);(D/'positive_verified.json').write_text(json.dumps(con,indent=2)+'\n')
    out=dict(donor_bank_sha256=digest,bank_words=len(G),distinct_donors_with_isolated_vertex=len(dedup),cases=len(cases),per_donor_length=dict(sorted(lengths.items())),two_replay_counts={'native':len(rows),'stdlib':len(rows)},edge_targets={193:len(rows),195:len(rows)},max_total_vertex_bound=[high.numerator,high.denominator],odd_edges_upper=191,selected_sources=summary,positive_edges=con['edges'],positive_pairs=con['pairs'])
    (D/'summary.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
if __name__=='__main__':main()
