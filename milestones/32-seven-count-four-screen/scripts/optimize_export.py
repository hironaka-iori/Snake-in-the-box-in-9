"""Re-export completed certificates without executable copies of proof data."""
import argparse,json,subprocess,sys
from pathlib import Path
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--case',type=int,required=True);a=ap.parse_args();i=a.case
 name=f'four{i}';p=HERE/f'logs/{name}-export.txt';old=json.loads(p.read_text())
 meta=json.loads((HERE/f'data/{name}.json').read_text())
 off=next(v for v in (2400,3000,4000) if v>meta['active_variables'])
 bits=next(b for b in (13,14,15) if old['slots']<(1<<b))
 cmd=[sys.executable,'-X','utf8',str(ROOT/'milestones/10-window-aggregate/scripts/gen_lean_lrat.py'),'--work',str(HERE/'certificates'),'--data',str(HERE/'data'),'--out',str(HERE/'lean'),'--fast','--check','--noncomputable-data','--wbits',str(bits),'--off',str(off),name]
 r=subprocess.run(cmd,capture_output=True,text=True,encoding='utf-8',check=True)
 new=json.loads(r.stdout);assert all(new[k]==old[k] for k in ('hints','slots','segments','lemmas'))
 new['noncomputable_data']=True;p.write_text(json.dumps(new)+'\n')
 print(name,'noncomputable data exported',flush=True)
if __name__=='__main__':main()
