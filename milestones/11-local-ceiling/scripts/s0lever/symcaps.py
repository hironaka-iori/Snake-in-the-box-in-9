import pickle, statistics as st, math
import os
D=os.path.dirname(os.path.abspath(__file__)) + '/'
store=pickle.load(open(D+'charges.pkl','rb'))
floor=lambda mu: 9214/(35+mu)-1
groups={'bank':[n for n in store if n.startswith('bank')],'adv208':['adv208'],'adv224':['adv224']}
def m(names,f): return st.mean(sum(f(store[n]['g'][x]) for x in store[n]['g'])/store[n]['v'] for n in names)
syms={
 'min(alpha,6) [current]': lambda g: min(g['alpha'],6),
 'min(alpha,6)+floor(min(share,2))': lambda g: min(g['alpha'],6)+math.floor(min(g['dom']-g['alpha'],2)),
 'min(alpha,6)+floor2(min(share,3))/2': lambda g: min(g['alpha'],6)+math.floor(2*min(g['dom']-g['alpha'],3))/2,
 'floor(min(dom,8))': lambda g: math.floor(min(g['dom'],8)),
 'floor(min(dom,10))': lambda g: math.floor(min(g['dom'],10)),
 'floor(min(dom,12))': lambda g: math.floor(min(g['dom'],12)),
 'floor(min(dom,16))': lambda g: math.floor(min(g['dom'],16)),
 'floor(min(dom,20))': lambda g: math.floor(min(g['dom'],20)),
 'alpha+e0/18 linear (dmax=9)': lambda g: float(g['alpha'])+0,  # placeholder replaced below
}
del syms['alpha+e0/18 linear (dmax=9)']
for name,f in syms.items():
    print(f'{name:38s}'+' | '.join(f'{g} {m(n,f):5.2f} ({floor(m(n,f)):5.1f})' for g,n in groups.items()))
