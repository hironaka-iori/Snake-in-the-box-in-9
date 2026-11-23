"""Check all integer face-dual records for one specified Q8 facet path using the standard library."""
import argparse
from collections import Counter
from itertools import combinations
import json
from pathlib import Path

def parity(x):
    return x.bit_count() & 1

def check(condition, message):
    if not condition:
        raise ValueError(message)

def branches(arm):
    low_arm=set(arm)
    allowed=[]
    for v in range(256):
        if v not in low_arm and all((v^a).bit_count()!=1 for a in arm[1:-1]):
            allowed.append(v)
    check(allowed==[61,144,240],"unexpected additional lower vertices")
    check(all((a^b).bit_count()>1 for a in allowed for b in low_arm|set(allowed) if a!=b),"extra vertex has a lower neighbor")
    result={}
    for mask in range(1<<len(allowed)):
        extra=tuple(x for i,x in enumerate(allowed) if mask>>i&1)
        lower=low_arm|set(extra)
        degrees={v:sum(v^(1<<i) in lower for i in range(8)) for v in lower}
        mandatory={v for v,d in degrees.items() if d==0}
        tips=sorted(v for v,d in degrees.items() if d==1)
        check(tips==sorted([arm[0],arm[-1]]),"invalid lower tips")
        for used in (1,2,3):
            crossing=tuple(v for i,v in enumerate(tips) if used>>i&1)
            ports=mandatory|set(crossing)
            low_end=[v for v,d in degrees.items() if d+int(v in ports)==1]
            remaining=2-len(low_end)
            for even_high in range(remaining+1):
                upper=(even_high,remaining-even_high)
                full=tuple(upper[c]+sum(parity(v)==c for v in low_end) for c in (0,1))
                delta=sum(1 if not parity(v) else -1 for v in lower)-(full[0]-full[1])//2
                result[crossing,extra,full]=(lower,ports,upper,delta)
    return result

def integer_bound(cert,lower,ports,counts,delta,allow_singleton_at_port=True):
    scale=cert['scale']; fees=cert['end_weights'];balance=cert['balance_weight']
    check(type(scale) is int and scale>0 and type(balance) is int, "invalid scale or balance")
    check(len(fees)==2 and all(type(z) is int for z in fees),"invalid endpoint fees")
    dirs=[]
    for ax in cert['axes']:
        check(ax and all(type(i) is int and 0<=i<8 for i in ax) and len(set(ax))==len(ax),"invalid face axes")
        dirs.append(tuple(1<<i for i in ax))
    masks=[sum(ds) for ds in dirs];check(len(set(masks))==len(masks),"repeated face family")
    free=set(range(256))-(lower-ports)
    prices={}
    for m,v,z,w in cert['weights']:
        check(all(type(a) is int for a in (m,v,z,w)) and m in masks and v in free and 0<=z<=m and not z&~m,"invalid matching price")
        check((m,v,z) not in prices,"duplicate matching price")
        prices[m,v,z]=w
    acc=sum(n*f for n,f in zip(counts,fees))+delta*balance
    sig={}
    for v in sorted(free):
        neigh=[1<<d for d in range(8) if v^(1<<d) in free]
        colour=1-parity(v);options=[]
        for degree in range(3):
            full_degree=degree+int(v in ports)
            if full_degree==1 and v in ports and not allow_singleton_at_port:
                continue
            if not (full_degree==2 or full_degree==1 and counts[colour]>0):
                continue
            for ds in combinations(neigh,degree):
                options.append((sum(ds),full_degree==1))
        vs=[] if v in ports else [0]
        for z,end in options:
            vs.append(scale-(1 if parity(v)==0 else -1)*balance-int(end)*fees[colour]+sum(prices.get((m,v,z&m),0) for m in masks))
        check(vs,"no possible state for required upper vertex")
        acc+=max(vs)
        for m in masks:
            sig[m,v]={z&m for z,_ in options}
    for m,ds in zip(masks,dirs):
        for base in range(256):
            if base&m:continue
            cell=[v for v in sorted(free) if v&~m==base]
            idx={v:j for j,v in enumerate(cell)}
            required=sum(1<<j for j,v in enumerate(cell) if v in ports)
            adj=[[(idx[v^d],d) for d in ds if v^d in idx] for v in cell]
            best=None
            for pick in range(1<<len(cell)):
                if pick&required!=required:continue
                seen=0;score=0
                for i,v in enumerate(cell):
                    if not pick>>i&1:continue
                    z=sum(d for j,d in adj[i] if pick>>j&1)
                    if z not in sig[m,v]:break
                    score-=prices.get((m,v,z),0)
                    if seen>>i&1:continue
                    # A connected forest component with n vertices has 2(n-1) edge incidences.
                    component=[i];seen|=1<<i;incidences=0
                    for u in component:
                        for j,_ in adj[u]:
                            if pick>>j&1:
                                incidences+=1
                                if not seen>>j&1:
                                    seen|=1<<j;component.append(j)
                    if incidences!=2*(len(component)-1):break
                else:
                    best=score if best is None else max(best,score)
            check(best is not None,"infeasible affine face");acc+=best
    return acc

def old_single_root_limits(filename,arm):
    limits={}
    for line in filename.read_text().splitlines():
        record=json.loads(line); c=record["certificate"]; path=c["arm"]; root=path[0]
        check(path==arm or path==list(reversed(arm)),"single-root donor mismatch")
        check(c["end_parity"]==0 and parity(root)==0 and root not in limits,"expected one old odd-U bound per orientation")
        families={sum(1<<i for i in ax):ax for ax in c["directions"]}
        weights=[]
        for m,v,k,w in c["matching_weights"]:
            axes=families[m];check(0<=k<(1<<len(axes)),"invalid compressed direction signature")
            weights.append((m,v,sum(1<<j for i,j in enumerate(axes) if k>>i&1),w))
        dual=dict(scale=c["scale"],axes=c["directions"],weights=weights,end_weights=[0,c["end_weight"]],balance_weight=c.get("parity_weight",0))
        num=integer_bound(dual,set(arm),{root},(0,1),1,False)
        check(num==c["integer_numerator"]==record["integer_numerator"],"old odd-U certificate failed")
        odd=num//c["scale"]
        check(odd==record["vertices_upper"],"old odd-U floor mismatch")
        if not odd%2:odd-=1
        # Any even U>=2 has an induced prefix with U-1 vertices from the same root.
        limits[root]=odd+1
    check(set(limits)=={arm[0],arm[-1]},"missing odd-U certificate orientation")
    return limits

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("records",nargs="?",type=Path,default=Path("q9_intact98_all_crossing_certificates.jsonl"))
    parser.add_argument("--arm-file",type=Path,default=Path("q8_free_layer_full98_duals.jsonl"))
    parser.add_argument("--single-odd",type=Path,help="also audit historical odd-U certificates and combine shortening bounds")
    args=parser.parse_args()
    with args.arm_file.open() as f:arm=json.loads(next(f))['certificate']['arm']
    check(len(arm)==len(set(arm))==99 and all(type(v) is int and 0<=v<256 for v in arm),"bad donor")
    check(all(((a^b).bit_count()==1)==(j==i+1) for i,a in enumerate(arm) for j,b in enumerate(arm) if j>i),"donor is not an induced path")
    expected=branches(arm);actual={};group={}
    for line in args.records.read_text().splitlines():
        row=json.loads(line);key=tuple(tuple(row[k]) for k in ('crossing','extras','full'))
        check(key in expected and key not in actual,f"unexpected or duplicate branch {key}")
        low,ports,upper,delta=expected[key]
        check(tuple(row['upper_ends'])==upper and row['delta']==delta,f"incorrect endpoint census {key}")
        n=integer_bound(row['cert'],low,ports,upper,delta)
        check(n==row['numerator'],f"numerator differs {key}: recomputed {n}")
        full=key[2];edge=len(low)-1+n//row['cert']['scale']
        # Opposite-colour endpoints give odd length, equal colours give even length.
        if (edge&1)!=int(full==(1,1)):edge-=1
        check(edge==row['edges_upper'],f"edge bound differs {key}")
        actual[key]=edge
        g=f"{len(key[0])} donor crossing(s), {len(key[1])} extra lower endpoint(s)"
        group.setdefault(g,[]).append(edge)
    check(actual.keys()==expected.keys(),f"missing {len(expected)-len(actual)} of {len(expected)} required branches")
    worst=max([98,*actual.values()])
    combined={}
    if args.single_odd:
        limits=old_single_root_limits(args.single_odd,arm)
        merged=[min(v,98+limits[k[0][0]]) if len(k[0])==1 and not k[1] else v for k,v in actual.items()]
        combined=dict(single_root_U_upper=limits,combined_edges_upper=max([98,*merged]))
    print(json.dumps(dict(**combined,arm_edges=98,additional_lower_vertices=[61,144,240],verified_records=len(actual),no_crossing_bound=98,
                      overall_edges_upper=worst,worst_keys=[k for k,v in actual.items() if v==worst],
                      branch_groups={g:dict(count=len(v),max=max(v)) for g,v in group.items()}),indent=2))
if __name__=='__main__':main()
