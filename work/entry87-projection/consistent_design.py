"""Six-bit path model with exact translation marginals on index triples.

Experimental alternative encoding. A step joins two preassigned parity classes.
For any subsequence x,y,z, Hamming distances obey both triangle inequalities
and the perimeter bound d(x,y)+d(y,z)+d(z,x)<=2d.
"""
import argparse,json
from itertools import combinations
from pathlib import Path
from time import monotonic
from solve import paths,save
from exact_cover import components_partition
from saturation import signs,separation


def distance_network(q,bits):
    tr=components_partition(q,bits);n=len(tr);d=len(bits)
    # The values 0..d and their pairwise compositions in the finite cube.
    # If x,y and y,z differ on sets of sizes a,b, their intersection has
    # size from max(0,a+b-d) through min(a,b), and all such sizes occur.
    composition=[[0]*(1<<(d+1)) for _ in range(1<<(d+1))]
    atom=[[sum(1<<(a+b-2*k) for k in range(max(0,a+b-d),min(a,b)+1))
           for b in range(d+1)] for a in range(d+1)]
    for a in range(1,len(composition)):
        for b in range(1,len(composition)):
            i=(a&-a).bit_length()-1;j=(b&-b).bit_length()-1
            composition[a][b]=atom[i][j]|composition[a&(a-1)][b]|composition[a][b&(b-1)]
    g=[[1 if i==j else 0 for j in range(n)] for i in range(n)]
    adjacent=signs(q,tr)
    for a,b in combinations(range(n),2):
        op=(a^b)&1
        dist=sum(1<<k for k in range(op,min(b-a,d)+1,2))
        if b==a+1:dist&=2
        elif not op and separation(tr[a],tr[b])<=1:dist&=~1
        elif op and adjacent[a,b][1]:dist&=~2
        g[a][b]=g[b][a]=dist
    orig=sum(g[a][b].bit_count() for a,b in combinations(range(n),2))
    rounds=0
    while True:
        changed=False
        for k in range(n):
            for i in range(n):
                if i==k:continue
                for j in range(i+1,n):
                    if j==k:continue
                    a=g[i][j]&composition[g[i][k]][g[k][j]]
                    if a!=g[i][j]:
                        changed=True;g[i][j]=g[j][i]=a
        rounds+=1
        if not changed:break
    final=sum(g[a][b].bit_count() for a,b in combinations(range(n),2))
    return g,dict(bits=bits,runs=n,rounds=rounds,strengthened_values=orig-final,
                  contradiction=any(not g[a][b] for a,b in combinations(range(n),2)))


if __name__=="__main__":
    ap=argparse.ArgumentParser()
    ap.add_argument("--bits",default="145678")
    args=ap.parse_args()
    q=paths()[1];bits=list(map(int,args.bits))
    m,r=distance_network(q,bits)
    print(r)
