from pathlib import Path
H=Path(__file__).resolve().parents[1]
p=H/'scripts/emit_cover.py';s=p.read_text(encoding='utf-8')
s=s.replace('tree=make(initial);counter=0','tree=make(initial);counter=0;chunks=[]')
start=s.index("        for x,y,v,e,rev,before,ys in t['steps']:")
end=s.index("        if 'dead' in t:",start)
replacement='''        for offset in range(0,len(t['steps']),16):
            group=t['steps'][offset:offset+16];needed={};changed={};used=set()
            for x,y,v,e,rev,before,ys in group:
                if x not in needed:needed[x]=before[:]
                if y not in needed:needed[y]=ys[:]
                after=before[:];after.remove(v);changed[x]=after;used.add(e)
            cname='chunk'+str(len(chunks));local={i:'d'+str(i) for i in needed};body=[]
            for j,(x,y,v,e,rev,before,ys) in enumerate(group):
                rel=f'(fun u v => edge r{e} v u)' if rev else f'(edge r{e})'
                bad='b'+str(j);new='t'+str(j)
                body.append(f'  have {bad} : a {x} ≠ {v} := exclude {lst(ys)} {rel} (a {x}) (a {y}) {v} {local[y]} c{e} (by decide +kernel)')
                after=before[:];after.remove(v)
                body.append(f'  have {new} : a {x} ∈ {lst(after)} := remove (a {x}) {v} {lst(before)} {local[x]} {bad}')
                local[x]=new
            header='theorem '+cname+' (a : Nat → Nat)\\n'
            for i,ds in needed.items():header+=f'    (d{i} : a {i} ∈ {lst(ds)})\\n'
            for e in sorted(used):
                c=cs[e];header+=f'    (c{e} : edge r{e} (a {c["left"]}) (a {c["right"]})=true)\\n'
            header+='    : '+' ∧ '.join(f'a {i} ∈ {lst(ds)}' for i,ds in changed.items())+' := by\\n'
            terms=[local[i] for i in changed];proof=terms[-1]
            for term in terms[-2::-1]:proof='And.intro '+term+' ('+proof+')'
            body.append('  exact '+proof)
            chunks.append(header+'\\n'.join(body)+'\\n')
            call=cname+' a '+' '.join(bounds[i] for i in needed)+' '+' '.join('c'+str(e) for e in sorted(used))
            counter+=1;result='group'+str(counter)
            out.append(indent+'have '+result+' := '+call)
            labels=[]
            for i in changed:
                counter+=1;hb='h'+str(counter);bounds[i]=hb;labels.append(hb)
            if len(labels)==1:out.append(indent+'have '+labels[0]+' := '+result)
            else:out.append(indent+'rcases '+result+' with ⟨'+','.join(labels)+'⟩')
'''
s=s[:start]+replacement+s[end:]
old="    code+='theorem cover (a : Nat → Nat)\\n'"
s=s.replace(old,"    proof_body='\\n'.join(emit(tree,{i:'start'+str(i) for i in range(n)},'  '))\n    code+='\\n'.join(chunks)\n"+old)
s=s.replace("    code+='\\n'.join(emit(tree,{i:'start'+str(i) for i in range(n)},'  '))+'\\n#print axioms cover\\nend '+name+'\\n'","    code+=proof_body+'\\n#print axioms cover\\nend '+name+'\\n'")
s=s.replace("    if target.exists():assert target.read_bytes()==code.encode('utf-8')","    if (H/'data'/(name+'-audit.json')).exists():assert target.read_bytes()==code.encode('utf-8')")
s=s.replace("proof_steps=counter,source_sha256=","proof_steps=counter,elimination_chunks=len(chunks),source_sha256=")
(H/'scripts/emit_cover_chunked.py').write_bytes(s.encode('utf-8'))
print('Prepared chunked emitter')
