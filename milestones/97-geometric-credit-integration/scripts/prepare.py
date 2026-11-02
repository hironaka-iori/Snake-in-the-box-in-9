"""Preserve geometric proofs while connecting their literal credits to direction IDs."""
from pathlib import Path
import ast,hashlib,json,re
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
OLD=HERE.parent/'59-extended-share-window'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
audit=read(OLD/'data/lean-audit.json');assert audit['status']=='PASS'
historical={r['module']:r for r in audit['records']}
data=OLD/'data/geometry.json';rows=read(data)['patterns'];assert len(rows)==505
table_path=HERE.parent/'77-direction-state-coverage/lean/DirectionTables.lean'
table=table_path.read_text()
m=re.search(r'def extensions\s*:\s*List \(List Nat\)\s*:=\s*',table)
assert m,'Cannot parse direction list'
start=m.end();level=0;stop=None
for j in range(start,len(table)):
    if table[j]=='[':level+=1
    elif table[j]==']':
        level-=1
        if level==0:stop=j+1;break
assert stop is not None
directions=ast.literal_eval(table[start:stop]);assert directions==[r['directions'] for r in rows]
imports=re.compile(rb'^import [^\r\n]*(?:\r?\n|$)',re.M)
ports=[];shape_module={}
for p in sorted((OLD/'lean').glob('GeometryBatch*.lean')):
    before=p.read_bytes();assert sha(p)==historical[p.stem]['source_sha256']
    replacements={b'import ExtendedShareBridge':b'import Port95M59ExtendedShareBridge',b'import MaskShareBridge':b'import Port95M59MaskShareBridge'}
    after=before
    for a,b in replacements.items():after=after.replace(a,b)
    assert imports.sub(b'',before)==imports.sub(b'',after)
    name='Port97M59'+p.stem;target=HERE/'lean'/(name+'.lean')
    if target.exists():assert target.read_bytes()==after
    else:target.write_bytes(after)
    indices=list(map(int,re.findall(rb'^namespace G(\d+)\r?$',before,re.M)))
    for i in indices:
        assert i not in shape_module and rows[i]['share_lower']>0
        block=before.decode().split(f'namespace G{i:03d}\n')[1] if b'\r\n' not in before else before.decode().split(f'namespace G{i:03d}\r\n')[1]
        ds=ast.literal_eval(re.search(r'def ds : List Nat := (\[[^\n]*\])',block)[1])
        credit=int(re.search(r'theorem in_snake.*?\n\s*(\d+) ≤',block,re.S)[1])
        assert ds==rows[i]['directions'] and credit==rows[i]['share_lower']
        shape_module[i]=name
    ports.append(dict(module=name,original_source=p.relative_to(ROOT).as_posix(),original_sha256=sha(p),source=target.relative_to(ROOT).as_posix(),source_sha256=sha(target),indices=indices,non_import_bytes_identical=True))
assert set(shape_module)=={i for i,r in enumerate(rows) if r['share_lower']>0} and len(shape_module)==357
credits=[r['share_lower'] for r in rows]
source='import SuffixCredit95\n\nnamespace Snake9.GeometricCredit97\nopen Snake9.LocalWindow Snake9.CreditTransport95 Snake9.Direction77\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\ndef geometricCredits : List Nat := '+str(credits)+'''\n\ntheorem geometricCredits_length : geometricCredits.length = 505 := by decide

theorem local_nine_zero (ds : List Nat) : LocalNineShare ds 0 := by
  intro m p P r hr hP
  exact Nat.zero_le _

#print axioms geometricCredits_length
#print axioms local_nine_zero
end Snake9.GeometricCredit97
'''
(HERE/'lean/GeometricData97.lean').write_text(source,encoding='utf-8',newline='\n')
# Blocks follow literal index intervals; zero-credit directions need no geometry.
dispatch=[]
for start in range(0,505,20):
    stop=min(start+20,505);name=f'GeometricLookup97Batch{start//20:02d}'
    deps=sorted({shape_module[i] for i in range(start,stop) if i in shape_module})
    lines=['import GeometricData97',*['import '+d for d in deps],'','namespace Snake9.GeometricCredit97','open Snake9.LocalWindow Snake9.CreditTransport95 Snake9.Direction77','set_option maxRecDepth 100000','set_option maxHeartbeats 0','',f'theorem valid_{start//20:02d} (i : Nat) (hlo : {start} ≤ i) (hhi : i < {stop}) :', '    LocalNineShare (extensions.getD i []) (geometricCredits.getD i 0) := by','  interval_cases i']
    for i in range(start,stop):
        if credits[i]==0:lines+=['  · exact local_nine_zero _']
        else:lines+=['  · exact Snake9.LocalWindow.ExtendedShare59.G'+f'{i:03d}.in_snake']
    lines+=['',f'#print axioms valid_{start//20:02d}','end Snake9.GeometricCredit97']
    (HERE/'lean'/(name+'.lean')).write_text('\n'.join(lines)+'\n',encoding='utf-8',newline='\n')
    dispatch.append(dict(module=name,start=start,stop=stop,imports=deps))
plan=dict(status='GENERATED_NOT_CHECKED',inputs={data.relative_to(ROOT).as_posix():sha(data),table_path.relative_to(ROOT).as_posix():sha(table_path),(OLD/'data/lean-audit.json').relative_to(ROOT).as_posix():sha(OLD/'data/lean-audit.json')},ports=ports,shape_modules={str(k):v for k,v in shape_module.items()},dispatch=dispatch,shapes=505,positive=357,zero=148,generator_sha256=sha(Path(__file__)))
(HERE/'data/generation.json').write_text(json.dumps(plan,indent=2)+'\n')
print('GENERATED',len(ports),'ports;',len(dispatch),'lookup blocks; all505 directions match')
