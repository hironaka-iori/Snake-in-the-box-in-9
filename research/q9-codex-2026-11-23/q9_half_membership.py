"""Expose the two halves as selected vertex classes of one exact path."""
from pysat.card import CardEnc, EncType

from q9_anchor_distances import exclude_interval


def partition(f,phase,pool,midpoint,step):
    n=len(phase)
    x,y=midpoint
    assert (x^y).bit_count()==1
    left=[pool.id() for _ in phase]
    right=[pool.id() for _ in phase]
    for v,bits in enumerate(phase):
        f.extend([[-left[v],v+1],[-right[v],v+1],[-v-1,left[v],right[v]],
                  [-left[v],-right[v]]])
        cutoff=(step-v.bit_count())//2
        exclude_interval(f,left[v],bits,cutoff+1,(1<<len(bits))-1)
        exclude_interval(f,right[v],bits,0,cutoff)
        for axis in range(n.bit_length()-1):
            w=v^(1<<axis)
            if (v,w)!=(x,y):
                f.append([-left[v],-right[w]])
    f.extend([[left[x]],[right[y]]])
    for parity in (0,1):
        group=[left[v] for v in range(n) if v.bit_count()%2==parity]
        count=(step+2-parity)//2
        f.extend(CardEnc.equals(group,count,vpool=pool,encoding=EncType.cardnetwrk).clauses)
