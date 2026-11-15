from pathlib import Path
H=Path(__file__).resolve().parents[1]
s=(H/'scripts/square_separation.py').read_text(encoding='utf-8').replace('import hashlib,json,sys,time','import hashlib,heapq,json,sys,time')
s=s.replace("base=P/'data'/f'forest-{root}'/'model.json'","base=H/'data'/f'square-{root}'/'model.json'")
s=s.replace("F=H/'data'/f'square-{root}'","F=H/'data'/f'long-{root}'")
a=s.index('    squares=[];');b=s.index("    rows=model['rows'];solver=",a)
s=s[:a]+'''    squares=model['square_witnesses'];inherited_subset_witnesses=model['subset_witnesses']
    cut_witnesses=[];cut_known=set()
    def parity_candidates(values):
        graph=[[] for _ in range(2*len(V))]
        for ei,(u,v) in enumerate(edges):
            d=max(0.0,min(1.0,values[ix[u]]+values[ix[v]]-2*values[iy[u,v]]))
            for bit in [0,1]:
                for flip in [0,1]:
                    a=2*pos[u]+bit;b=2*pos[v]+(bit^flip);cost=1-d if flip else d
                    graph[a].append((b,cost,ei,flip));graph[b].append((a,cost,ei,flip))
        found={}
        for vi in range(len(V)):
            start=2*vi;target=start+1;dist={start:0.0};previous={};todo=[(0.0,start)];done=set()
            while todo:
                d,u=heapq.heappop(todo)
                if u in done:continue
                done.add(u)
                if u==target:break
                for v,c,ei,flip in graph[u]:
                    if v in done:continue
                    nd=d+c
                    if nd<dist.get(v,float('inf'))-1e-12:
                        dist[v]=nd;previous[v]=(u,ei,flip);heapq.heappush(todo,(nd,v))
            if dist[target]>=1-1e-8:continue
            path=[target];transition=[]
            while path[-1]!=start:
                u,ei,flip=previous[path[-1]];transition.append((ei,flip));path.append(u)
            path.reverse();transition.reverse();seen={}
            for k,state in enumerate(path):
                v=state//2
                if v in seen:a=seen[v];b=k;break
                seen[v]=k
            C=[V[state//2] for state in path[a:b]];ce=transition[a:b];odd=[i for i,(ei,f) in enumerate(ce) if f]
            assert len(C)>=4 and len(C)==len(set(C)) and len(odd)%2==1
            assert all(set(edges[ei])=={C[i],C[(i+1)%len(C)]} for i,(ei,f) in enumerate(ce))
            key=tuple(sorted(ce))
            if key in cut_known:continue
            terms={}
            for ei,flip in ce:
                u,v=edges[ei];sign=1 if flip else -1
                for index,coefficient in [(ix[u],sign),(ix[v],sign),(iy[u,v],-2*sign)]:terms[index]=terms.get(index,0)+coefficient
            terms=sorted((i,c) for i,c in terms.items() if c);rhs=len(odd)-1
            violation=sum(c*values[i] for i,c in terms)-rhs
            if violation>1e-7:found[key]=({'cycle':C,'odd_edge_indices':odd,'violation_at_discovery':violation},terms,rhs)
        return found
'''+s[b:]
s=s.replace("'name':'forest221_'+str(len(added))","'name':'long_forest221_'+str(len(added))")
s=s.replace("        entry={'iteration':iteration,","        parity=parity_candidates(values)\n        entry={'new_violated_parity_cycles':len(parity),'iteration':iteration,")
s=s.replace('if not candidates or iteration==60:break','if (not candidates and not parity) or iteration==60:break')
needle="    model['base_model_sha256']=sha(base);"
insert='''        for key,(witness,terms,rhs) in sorted(parity.items()):
            cut_known.add(key);row={'name':'cut_parity221_'+str(len(cut_witnesses)),'terms':terms,'sense':'le','rhs':rhs}
            witness.update(iteration=iteration,row_index=len(rows));cut_witnesses.append(witness);rows.append(row);install(row)
'''
s=s.replace(needle,insert+needle)
s=s.replace("model['square_witnesses']=squares;","model['square_witnesses']=squares;model['cut_parity_witnesses']=cut_witnesses;")
s=s.replace('Round221 adds every square parity row and additional necessary subset rows.','Round221 extends the square model by witnessed longer cycle parity rows and additional subset rows.')
s=s.replace("'added_square_rows':len(squares),","'inherited_square_rows':len(squares),'added_parity_cycles':len(cut_witnesses),")
s=s.replace("'no_new_violations_at_tolerance':not bool(candidates)","'no_new_violations_at_tolerance':not bool(candidates or parity)")
s=s.replace('data/square-summary.json','data/long-summary.json')
(H/'scripts/long_separation.py').write_text(s,encoding='utf-8',newline='\n')
s=(H/'scripts/run_square.py').read_text(encoding='utf-8').replace('square_separation.py','long_separation.py').replace('square-execution.json','long-execution.json').replace('square-stdout.log','long-stdout.log').replace('square-stderr.log','long-stderr.log').replace('square-summary.json','long-summary.json').replace("H.parent/'220-subset-forest/data/forest-0/model.json',H.parent/'220-subset-forest/data/forest-78/model.json'","H/'data/square-0/model.json',H/'data/square-78/model.json'")
(H/'scripts/run_long.py').write_text(s,encoding='utf-8',newline='\n')
print('PREPARED_LONG_PARITY_SEPARATION')
