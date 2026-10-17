import json, math
from verify_real import order_path, alphas
bank = json.load(open('/home/user/Snake-in-the-box-in-9/work/bank9.json'))
seqs = [('bank%d'%i, e['vertex_sequence']) for i,e in enumerate(bank)]
for r in json.load(open('real_r9_a.json')):
    seqs.append(('real'+''.join(map(str,r['alpha'])), order_path(r['selected'])))
A = [(n, alphas(s)) for n,s in seqs]
print(' k   min internal k-window mean (bank)   (incl. low-alpha snakes)   -> averaging-argument ceiling v<=9214/(35+m)-ish, edges')
for k in [1,2,3,4,5,6,8,10,15,20,30,40,60,80,100,150,190]:
    def mn(group):
        best=(1e9,None)
        for n,a in group:
            a=a[1:-1]
            if len(a)<k: continue
            s=sum(a[:k]); b=s; 
            for i in range(k,len(a)):
                s+=a[i]-a[i-k]; b=min(b,s)
            if b/k<best[0]: best=(b/k,n)
        return best
    mb=mn(A[:131]); ma=mn(A)
    print('%4d   %6.3f (%s)        %6.3f (%s)     edges<= %d / %d'%(k,mb[0],mb[1],ma[0],ma[1], math.floor(9214/(35+mb[0]))-1, math.floor(9214/(35+ma[0]))-1))
