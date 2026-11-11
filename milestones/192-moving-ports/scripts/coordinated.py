from pathlib import Path
import collections,hashlib,json,time
R=Path('E:/Snake-in-a-box');H=R/'milestones/192-moving-ports';bank=json.loads((R/'work/bank9.json').read_text());start=time.monotonic()
def canonical(p):
    t=[(u^v).bit_length()-1 for u,v in zip(p,p[1:])]
    def relabel(t):
        labels={};s=[]
        for a in t:
            if a not in labels:labels[a]=len(labels)
            s.append(labels[a])
        return tuple(s)
    return min(relabel(t),relabel(t[::-1]))
known={canonical(r['vertex_sequence']):i for i,r in enumerate(bank)};assert len(known)==131
rows=[];certificates=[];newclasses={};witnesses=[];extension=None
for index,row in enumerate(bank):
    p=row['vertex_sequence'];L=len(p)-1;assert L==191 and len(set(p))==192
    assert all(((p[i]^p[j]).bit_count()==1)==(j==i+1) for i in range(192) for j in range(i+1,192))
    alt={i:p[i-1]^p[i]^p[i+1] for i in range(1,L)}
    deps={i:{j for j in range(L+1) if j!=i and (alt[i]==p[j] or (((alt[i]^p[j]).bit_count()==1)!=(abs(i-j)==1)))} for i in alt}
    conflicts={i:{j for j in alt if j>i and (alt[i]==alt[j] or (((alt[i]^alt[j]).bit_count()==1)!=(j==i+1)))} for i in alt}
    def close(required,forbidden=set()):
        chosen=set(required);todo=list(required);trace=[]
        while todo:
            i=todo.pop()
            if i in [0,L]:return chosen,trace,{'kind':'fixed_endpoint','index':i}
            if i in forbidden:return chosen,trace,{'kind':'forbidden_flip','index':i}
            for j in sorted(deps[i]):
                if j not in chosen:chosen.add(j);todo.append(j);trace.append([i,j])
        for i in sorted(chosen):
            bad=conflicts[i]&chosen
            if bad:return chosen,trace,{'kind':'pair_conflict','indices':[i,min(bad)]}
        return chosen,trace,None
    seen=set();closures=[]
    for i in alt:
        selected,trace,bad=close({i});key=tuple(sorted(selected))
        if key in seen:continue
        seen.add(key)
        if bad:continue
        q=[alt[j] if j in selected else v for j,v in enumerate(p)]
        assert len(set(q))==192 and all(((q[a]^q[b]).bit_count()==1)==(b==a+1) for a in range(192) for b in range(a+1,192))
        code=canonical(q);changed_ports=[]
        for k in range(9):
            oldcuts=[j for j in range(L) if p[j]^p[j+1]==1<<k]
            newcuts=[j for j in range(L) if q[j]^q[j+1]==1<<k]
            assert len(oldcuts)==len(newcuts)
            if len(oldcuts)==2 and oldcuts!=newcuts:changed_ports.append({'coordinate':k,'old_cuts':oldcuts,'new_cuts':newcuts})
        record={'seed_index':index,'required_index':i,'flipped_indices':list(key),'flips':len(key),'known_class':known.get(code),'changed_ports':changed_ports,'path':q}
        closures.append({k:v for k,v in record.items() if k!='path'});witnesses.append(record)
        if code not in known:newclasses.setdefault(code,record)
    endcases=[]
    for side,root in [('left',0),('right',L)]:
        for direction in range(9):
            w=p[root]^(1<<direction);other=L if root==0 else 0
            record={'seed_index':index,'side':side,'direction':direction,'extension_vertex':w}
            if w==p[other] or (w^p[other]).bit_count()==1:
                record.update(obstruction={'kind':'other_fixed_endpoint','index':other});endcases.append(record);continue
            required={i for i in alt if p[i]==w or (p[i]^w).bit_count()==1}
            forbidden={i for i in alt if alt[i]==w or (alt[i]^w).bit_count()==1}
            selected,trace,bad=close(required,forbidden);record.update(required=sorted(required),forbidden=sorted(forbidden),propagation=trace,forced=sorted(selected),obstruction=bad)
            if bad is None:
                q=[alt[j] if j in selected else v for j,v in enumerate(p)];q=q+[w] if side=='right' else [w]+q
                assert len(set(q))==193 and all(((q[a]^q[b]).bit_count()==1)==(b==a+1) for a in range(193) for b in range(a+1,193))
                extension={'seed_index':index,'path':q,'record':record}
            endcases.append(record)
    certificates.append({'seed_index':index,'dependencies':{str(i):sorted(v) for i,v in deps.items() if v},'conflicts':{str(i):sorted(v) for i,v in conflicts.items() if v},'endpoint_cases':endcases})
    rows.append({'seed_index':index,'distinct_nonempty_valid_closures':len(closures),'closures':closures,'endpoint_candidates':len(endcases),'endpoint_obstructions':dict(collections.Counter(r['obstruction']['kind'] if r['obstruction'] else 'NONE' for r in endcases))})
    if extension:break
out={'status':'LONGER_WITNESS_FOUND' if extension else 'COMPLETE_NO_EXTENSION','seconds':time.monotonic()-start,'seeds':len(rows),'endpoint_candidates':sum(r['endpoint_candidates'] for r in rows),'valid_minimum_closures':sum(r['distinct_nonempty_valid_closures'] for r in rows),'closure_sizes':dict(collections.Counter(r['flips'] for r in witnesses)),'new_q9_classes':len(newclasses),'closures_moving_two_crossing_ports':sum(bool(r['changed_ports']) for r in witnesses),'rows':rows,'extension':extension,'scope':'Any simultaneous subset of alternate-square substitutions at original internal path positions, followed by one endpoint extension. Endpoint positions themselves remain fixed until extension. Binary pairwise constraints are solved by implication closure of forced substitutions and pair conflicts. Every positive constraint has a false antecedent outside the closure, so assigning all remaining flips false is complete for feasibility. This excludes this transformation family only, not arbitrary induced paths or arbitrary replacements. Native certificates; generic interpretation and full finite census not yet Lean-certified.'}
(H/'data/coordinated-squares.json').write_text(json.dumps(out,indent=2)+'\n');(H/'data/coordinated-certificates.json').write_text(json.dumps(certificates,indent=2)+'\n');(H/'data/coordinated-witnesses.json').write_text(json.dumps({'minimum_closures':witnesses,'new_classes':list(newclasses.values()),'extension':extension},indent=2)+'\n');(H/'scripts/coordinated.py').write_bytes(Path(__file__).read_bytes());print(json.dumps({k:v for k,v in out.items() if k not in ['rows','extension']},indent=2),flush=True)
