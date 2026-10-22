"""Query all previously uncharged windows of the newly found periodic pattern."""
import hashlib,json
from pathlib import Path
from direct import HERE,solve

def main():
    obstruction=json.loads((HERE/'data/cache-obstruction.json').read_text())
    rows=[]
    for i,record in enumerate(obstruction['records']):
        dirs,alpha=record['five_window_key']
        case=dict(name=f'obstruction_{i}',dirs=dirs,alpha=alpha,cap=107)
        row=solve(case,12)
        row['model_sha256_lf']=hashlib.sha256((HERE/'scripts/direct.py').read_bytes().replace(b'\r\n',b'\n')).hexdigest()
        rows.append(row)
        (HERE/'data/obstruction-probes.json').write_text(json.dumps(dict(rows=rows,complete=len(rows)==len(obstruction['records'])),indent=2)+'\n')
        print(i,row['status'],row['additional_cycle_cuts'],row.get('census',{}).get('total_share'),flush=True)
if __name__=='__main__':main()
