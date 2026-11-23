from pathlib import Path
D=Path(__file__).resolve().parent
p=(D.parent/'q9_fourcross_new94/joint.py').read_text();s=p[:p.index('def run(')]
s=s.replace('import sys,json','import sys,json,os,time').replace('def search(src,id,low,short,anchor,initial,target,c,cap,log):','def search(src,id,low,short,anchor,initial,target,c,cap,log,m):\n    start=time.monotonic()')
s=s.replace('    eq(crosses,2)','''    eq(crosses,2)
    # A 92-edge main path has 47 projected vertices of its endpoint colour and 46 of the other.
    for h in (0,1):
        lowcount=L//2+int(m==h)+sum(v.bit_count()%2==h for v in short)
        for layer in (0,1):
            required=lowcount if not layer else target//2+int(c==h)-lowcount
            vertices=[v for v in avail if (v>=256)==bool(layer) and v.bit_count()%2==h]
            eq([X[v] for v in vertices if v not in yes],required-sum(v in yes for v in vertices))
        crossh=[pool.id(('cross',v)) for v in avail if v<256 and v+256 in X and v not in short and v.bit_count()%2==h]
        eq(crossh,2*int(h==m))
    # Each of the four antipodal pairs in a Q3 leaves an induced six-cycle in its complement.
    for axes in combinations(range(9),3):
        shifts=[0]
        for j in axes:shifts+=[z^1<<j for z in shifts]
        mask=shifts[-1]
        for b in range(512):
            if b&mask:continue
            cube={b^z for z in shifts}
            for z in shifts[:4]:
                cycle=cube-{b^z,b^z^mask}
                if cycle<=X.keys():F.append([-X[v] for v in sorted(cycle-yes)])''')
s=s.replace("dict(seed=src,id=id,anchor_edges=", "dict(seed=src,id=id,lower_end_color=m,seconds=round(time.monotonic()-start,2),anchor_edges=")
s+='''\nif __name__=='__main__':
    cases=json.loads((D/'cases.json').read_text());idx=int(sys.argv[1]);r=cases[idx];target=int(sys.argv[2]);budget=int(sys.argv[3]);log=sys.argv[4]
    branches=[(int(v[0]),int(v[1])) for v in sys.argv[5:]]
    for c,m in branches:search(r['source'],r['row'],[0]*(r['L']+1),r['short'],r['anchor'],set(r['hint']),target,c,budget,log,m)
'''
(D/'strengthened.py').write_text(s)
