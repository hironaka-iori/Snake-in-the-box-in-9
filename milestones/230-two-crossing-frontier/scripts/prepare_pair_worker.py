from pathlib import Path
import json
H=Path(__file__).resolve().parents[1];P=H.parents[1]/'milestones/229-two-layer-construction'
j=json.loads((H/'data/lower-pairs.json').read_bytes());assert not j['unsupported'] and len(j['contexts'])==11
s=(P/'scripts/pair_cp.py').read_text(encoding='utf-8').replace('data/boundary-lower-pairs.json','data/lower-pairs.json')
start=s.index("ap.add_argument('--ids',default=");end=s.index(';a=ap.parse_args()',start)
s=s[:start]+"ap.add_argument('--ids',default="+repr(','.join(map(str,j['representatives'])))+")"+s[end:]
old="sum((x^y)==256 for x,y in zip(full,full[1:]))==4";assert s.count(old)==1;s=s.replace(old,old[:-1]+'2')
s=s.replace('the five reduced Q8 path-pair tasks','the exact-two-crossing Q8 path-pair tasks')
p=H/'scripts/pair_cp.py';assert not p.exists();p.write_text(s,encoding='utf-8')
s=(P/'scripts/run_pairs.py').read_text(encoding='utf-8').replace('data/boundary-lower-pairs.json','data/lower-pairs.json')
(H/'scripts/run_pairs.py').write_text(s,encoding='utf-8')
print('PREPARED_PAIR_WORKER',len(j['representatives']))
