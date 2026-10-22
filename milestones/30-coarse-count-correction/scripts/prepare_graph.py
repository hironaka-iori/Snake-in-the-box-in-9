"""Derive the new diagnostic from the previous pinned graph implementation."""
from pathlib import Path
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
s=(ROOT/'milestones/29-overlapping-share-windows/scripts/selective_graph.py').read_text()
s=s.replace('from joint import HERE,ROOT,candidates,dkey','HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]\nsys.path.insert(0,str(ROOT/"milestones/29-overlapping-share-windows/scripts"))\nfrom joint import candidates,dkey')
s=s.replace('def main():', '''def periodic(a):
    for n in range(len(a),0,-1):
        if any(all(a[len(a)-n+j]==(3,3,6)[(p+j)%3] for j in range(n)) for p in range(3)):return n
    return 0

def advance(a,run,pr,s):
    al=a+(s,);nr=min(6,run+1) if s==4 else 0
    np=min(6,pr+1) if periodic(al)==5 else periodic(al)
    return nr,np

def main():''')
s=s.replace('for run in ([4,5,6] if a==(4,4,4,4) else [trailing(a)]):states.append((c,a,run))','''for run in ([4,5,6] if a==(4,4,4,4) else [trailing(a)]):
                for pr in ([4,5,6] if periodic(a)==4 else [periodic(a)]):states.append((c,a,run,pr))''')
s=s.replace('len(states)==44132','len(states)==44336')
s=s.replace('U=[];V=[];LO=[];HI=[];CUT=[];records=[]','''phases=[(3,3,6,3,3,6,3),(3,6,3,3,6,3,3),(6,3,3,6,3,3,6),(6,3,3,6,3,3,6)]
    keys7=[key(c['dirs'],tuple((z,z) if z<6 else (6,21) for z in a)) for c,a in zip(candidates(),phases)]
    cutkeys=set(keys7[:2]);bonuskeys=set(keys7[2:])
    U=[];V=[];LO=[];HI=[];OLD=[];CUT=[];BONUS=[];records=[]''')
s=s.replace('for u,(c,a,run) in enumerate(states):','for u,(c,a,run,pr) in enumerate(states):')
s=s.replace('nr=min(6,run+1) if s==4 else 0;v=sid[(nc,al[1:],nr)]','''nr,npr=advance(a,run,pr,s);v=sid[(nc,al[1:],nr,npr)]
                seven=next((p for p in phases if p[-5:]==al),None) if pr==6 and periodic(al)==5 else None
                k7=key(ds,tuple((z,z) if z<6 else (6,21) for z in seven)) if seven else None''')
s=s.replace('LO.append(120*s+lb.get(keys[-1],0));HI.append(120*s+ub.get(keys[-1],10**6))','LO.append(3*(120*s+lb.get(keys[-1],0)));HI.append(3*(120*s+ub.get(keys[-1],10**6)))')
s=s.replace('CUT.append(run==6 and s==4 and dkey(ds) in special)','OLD.append(run==6 and s==4 and dkey(ds) in special);CUT.append(k7 in cutkeys);BONUS.append(120*int(k7 in bonuskeys))')
s=s.replace('CUT=np.array(CUT)','CUT=np.array(CUT);OLD=np.array(OLD);BONUS=np.array(BONUS)')
s=s.replace('added_states=68','added_states=272,additional_states_since_milestone29=204')
s=s.replace('removed_edges=int(CUT.sum()),runs=[]','removed_edges=int((CUT & ~OLD).sum()),corrected_edges=int(((BONUS>0) & ~OLD & ~CUT).sum()),runs=[]')
s=s.replace("[('before',np.ones(len(U),dtype=bool)),('after',~CUT)]","[('before',~OLD),('after',~OLD & ~CUT)]")
s=s.replace("for mode,weights in [('lower',LO),('witness',HI)]:","for mode,base in [('lower',LO),('witness',HI)]:\n            weights=base+(BONUS if label=='after' else 0)")
s=s.replace('120*len(edges)','360*len(edges)')
s=s.replace("weight=int(weights[e]))","weight=int(weights[e]),base_weight=int(base[e]),excess_bonus=int(BONUS[e]) if label=='after' else 0)")
(HERE/'scripts/correction_graph.py').write_text(s,encoding='utf-8')
print('Generated correction diagnostic.')
