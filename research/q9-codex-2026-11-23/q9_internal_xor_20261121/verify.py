from collections import Counter,defaultdict
from itertools import accumulate
from operator import xor
from pathlib import Path
import json,sys

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent

def canon(w):
    def one(word):
        m={};return ''.join(m.setdefault(c,str(len(m))) for c in word)
    return min(one(w),one(w[::-1]))
def vertices(w):
    assert set(w)<=set('012345678')
    return list(accumulate((1<<int(c) for c in w),xor,initial=0))
def chords(p):
    ids={v:i for i,v in enumerate(p)}
    assert len(p)==len(ids) and all(0<=v<512 for v in p)
    assert all((a^b).bit_count()==1 for a,b in zip(p,p[1:]))
    return [(i,j) for i,v in enumerate(p) for d in range(9) if (j:=ids.get(v^1<<d,-1))>i+1]
def quadratic(p):
    return [(i,j) for i,v in enumerate(p) for j in range(i+2,len(p)) if (v^p[j]).bit_count()==1]
def wfrom(p):
    return canon(''.join(str((x^y).bit_length()-1) for x,y in zip(p,p[1:])))
def readwords(f):return {canon(w) for w in f.read_text().split()}
if __name__=='__main__':
    names=sys.argv[1:] or ['insertion.log','repair.log']
    known={n:readwords(ROOT/'q9_gap_generations'/f'prior{n}.words') for n in (189,190,191)}
    one_ref=set()
    for f in ['q9_onechord_expanded_800.txt','q9_threechord_one_paths.txt','q9_reordered_segments_20261120/new_onechord.paths','q9_onechord_allperm_closure.txt','q9_onechord_pivot_closure.txt','q9_twochord_ball_one_paths.txt','q9_onechord_cross120_paths.txt','q9_onechord_cross96_paths.txt']:
        for l in (ROOT/f).read_text().splitlines():
            p=list(map(int,l.split()))
            if len(p)==193:one_ref.add(wfrom(p))
    two_ref={w for l in (ROOT/'q9_new189_nearmisses.words').read_text().splitlines() for k,w in [l.split()] if k=='2'}
    candidates=defaultdict(dict); true=defaultdict(set)
    for name in names:
        for l in (HERE/name).read_text().splitlines():
            t=l.split()
            if t[0]=='PATH':_,n,e,w=t
            elif t[0]=='NEAR':_,e,w=t
            else:continue
            if w in candidates[len(w)]:continue
            p=vertices(w);c=chords(p)
            assert len(c)==int(e) and w==canon(w)
            if len(c)<=1:assert sorted(c)==quadratic(p)
            candidates[len(w)][w]=len(c)
            for size in [189,190,191,192]:
                for i in range(len(w)-size+1):
                    if not any(i<=a<b<=i+size for a,b in c):
                        true[size].add(canon(w[i:i+size]))
    summary={'candidate_counts':{n:dict(Counter(d.values())) for n,d in candidates.items()},'near_reference':{'one':len(one_ref),'two':len(two_ref)}}
    for e,r in [(1,one_ref),(2,two_ref)]:
        bank={w for w,c in candidates[192].items() if c==e}
        novel=bank-r
        summary[f'chords_{e}']={'found':len(bank),'outside_reference':len(novel)}
        (HERE/f'near192_chords{e}_outside_reference.words').write_text(''.join(w+'\n' for w in sorted(novel)))
    for n in (189,190,191,192):
        novel=true[n]-known.get(n,set())
        summary[f'true{n}']={'found':len(true[n]),'reference':len(known.get(n,set())),'outside_reference':len(novel)}
        for w in true[n]:assert not quadratic(vertices(w))
        (HERE/f'true{n}_outside_reference.words').write_text(''.join(w+'\n' for w in sorted(novel)))
        (HERE/f'true{n}_all.words').write_text(''.join(w+'\n' for w in sorted(true[n])))
    print(json.dumps(summary,indent=2))
