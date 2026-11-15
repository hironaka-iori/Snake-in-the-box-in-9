from pathlib import Path
H=Path(__file__).resolve().parents[1];P=H.parent/'220-subset-forest'
s=(P/'scripts/subset_separation.py').read_text(encoding='utf-8')
s=s.replace("P=H.parent/'219-linear-partner'","P=H.parent/'220-subset-forest'")
s=s.replace("base=P/'data'/f'edge-{root}'/'model.json'","base=P/'data'/f'forest-{root}'/'model.json'")
s=s.replace("F=H/'data'/f'forest-{root}'","F=H/'data'/f'square-{root}'")
start=s.index('    initial=[]\n');end=s.index("    rows=model['rows'];solver=",start)
insert='''    squares=[];edge_set={tuple(e) for e in edges};square_rows=[]
    inherited_subset_witnesses=model['subset_witnesses']
    for C in model['cycles']:
        if len(C)!=4:continue
        first=min(C);ordered=[first];old=None;current=first
        while True:
            choices=sorted(v for v in C if tuple(sorted((current,v))) in edge_set and v!=old)
            nxt=choices[0]
            if nxt==first:break
            assert nxt not in ordered;ordered.append(nxt);old,current=current,nxt
        assert len(ordered)==4
        ce=[tuple(sorted((u,v))) for u,v in zip(ordered,ordered[1:]+ordered[:1])]
        for mask in range(16):
            if mask.bit_count()%2!=1:continue
            terms={}
            for i,(u,v) in enumerate(ce):
                sign=1 if mask>>i&1 else -1
                for index,a in [(ix[u],sign),(ix[v],sign),(iy[u,v],-2*sign)]:terms[index]=terms.get(index,0)+a
            row={'name':'square_parity_'+str(len(square_rows)),'terms':[[i,a] for i,a in sorted(terms.items()) if a],'sense':'le','rhs':mask.bit_count()-1}
            squares.append({'cycle':ordered,'odd_edge_indices':[i for i in range(4) if mask>>i&1],'row_index':len(model['rows'])})
            model['rows'].append(row);square_rows.append(row)
    print(json.dumps({'root':root,'square_count':len(squares)//8,'square_rows':len(square_rows)}),flush=True)
'''
s=s[:start]+insert+s[end:]
s=s.replace("obj.SetMaximization();added=[];known=set();steps=[];started=time.monotonic()","obj.SetMaximization();added=[];known={(w['vertex'],tuple(w['subset'])) for w in inherited_subset_witnesses};steps=[];started=time.monotonic()")
s=s.replace("'name':'forest_'+str(len(added))","'name':'forest221_'+str(len(added))")
s=s.replace("model['source_sha256_220']","model['source_sha256_221']")
s=s.replace("model['subset_witnesses']=added;model['scope']+=' Round220 adds necessary induced-forest subset rows. Floating separation does not prove closure.'","model['subset_witnesses']=inherited_subset_witnesses+added;model['square_witnesses']=squares;model['scope']+=' Round221 adds every square parity row and additional necessary subset rows. Floating separation does not prove closure.'")
s=s.replace("'added_subset_count':len(added)","'added_square_rows':len(squares),'added_subset_count':len(added)")
s=s.replace('data/forest-summary.json','data/square-summary.json')
(H/'scripts/square_separation.py').write_text(s,encoding='utf-8',newline='\n')
s=(P/'scripts/run_forest.py').read_text(encoding='utf-8').replace('subset_separation.py','square_separation.py').replace('forest-execution.json','square-execution.json').replace('forest-stdout.log','square-stdout.log').replace('forest-stderr.log','square-stderr.log').replace('forest-summary.json','square-summary.json').replace("H.parent/'219-linear-partner/data/edge-0/model.json',H.parent/'219-linear-partner/data/edge-78/model.json'","H.parent/'220-subset-forest/data/forest-0/model.json',H.parent/'220-subset-forest/data/forest-78/model.json'")
(H/'scripts/run_square.py').write_text(s,encoding='utf-8',newline='\n')
print('PREPARED_SQUARE_SEPARATION')
