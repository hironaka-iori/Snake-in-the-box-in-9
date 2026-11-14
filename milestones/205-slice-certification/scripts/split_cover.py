"""Split large generated proof modules without changing their statements."""
from pathlib import Path
import argparse,hashlib,json,re
H=Path(__file__).resolve().parents[1]
ap=argparse.ArgumentParser();ap.add_argument('--index',type=int);a=ap.parse_args();indices=range(254) if a.index is None else [a.index];order=[];records=[]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for i in indices:
    name='PartitionCover205_'+str(i);p=H/'lean'/(name+'.lean');s=p.read_text(encoding='utf-8');receipt=H/'data'/(name+'-audit.json')
    chunks=list(re.finditer(r'^theorem chunk\d+ ',s,re.M));split=len(s.encode('utf-8'))>40000 or len(chunks)>8
    if split:
        assert not receipt.exists()
        first=chunks[0].start();cover=s.index('theorem cover ');data=s[:first]+'end '+name+'\n';dname='PartitionData205_'+str(i)
        dp=H/'lean'/(dname+'.lean');dp.write_bytes(data.encode('utf-8'));order.append(dname);parts=[]
        chunksources=[s[m.start():chunks[j+1].start() if j+1<len(chunks) else cover] for j,m in enumerate(chunks)]
        for j in range(0,len(chunksources),4):
            pname='PartitionPiece205_'+str(i)+'_'+str(j//4);parts.append(pname)
            code='import '+dname+'\nnamespace '+name+'\nopen FiniteDomain205\nset_option maxRecDepth 100000\nset_option maxHeartbeats 2000000\n'+''.join(chunksources[j:j+4])
            for c in chunksources[j:j+4]:code+='#print axioms '+re.search(r'theorem (chunk\d+)',c).group(1)+'\n'
            code+='end '+name+'\n';(H/'lean'/(pname+'.lean')).write_bytes(code.encode('utf-8'));order.append(pname)
        aggregate='\n'.join('import '+n for n in [dname]+parts)+'\nnamespace '+name+'\nopen FiniteDomain205\nset_option maxRecDepth 100000\nset_option maxHeartbeats 2000000\n'+s[cover:]
        p.write_bytes(aggregate.encode('utf-8'))
    order.append(name);rpath=H/'data'/('cover-'+str(i)+'.json');record=json.loads(rpath.read_bytes());record['source_sha256']=sha(p);record['split_modules']=([dname]+parts) if split else [];rpath.write_text(json.dumps(record,indent=2)+'\n');records.append(record)
out=dict(module_order=order,source_sha256={n:sha(H/'lean'/(n+'.lean')) for n in order},partition_indices=list(indices),scope='Exact finite-CSP coverage. Split modules retain the same complete hypothesis and conclusion; geometric bridges remain separate.')
(H/'data'/('batch-plan'+('-'+str(a.index) if a.index is not None else '')+'.json')).write_text(json.dumps(out,indent=2)+'\n')
print('PREPARED',len(order),'modules for',len(records),'partition covers')
