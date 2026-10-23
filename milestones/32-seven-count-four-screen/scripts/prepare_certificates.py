"""Adapt the verified ordinary-window certificate pipeline to all 34 cases."""
from pathlib import Path
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
for d in ['certificates','logs','lean']:(HERE/d).mkdir(exist_ok=True)
s=(ROOT/'milestones/30-coarse-count-correction/scripts/certify.py').read_text(encoding='utf-8')
s=s.replace("name=f'coarse{i}';mod=f'CoarseCount{i}'","name=f'four{i}';mod=f'FourRun{i}'")
s=s.replace("f'Window{i}.lean'","f'RunWindow{i}.lean'")
s=s.replace("print(name,len(compact),'clauses;',len(used),'variables;',report.strip(),flush=True)","print(name,len(compact),'clauses;',len(used),'variables;',json.loads(report)['hints'],'hints',flush=True)")
s=s.replace("    report=run([sys.executable,'-X','utf8'", "    import gen_lean_lrat as lratgen\n    slots=lratgen.plan(meta['core_ids'],lratgen.read_lrat(str(prefix.with_suffix('.lrat'))))[3]\n    bits=next(b for b in (13,14,15) if slots < (1 << b))\n    report=run([sys.executable,'-X','utf8'")
s=s.replace("'--fast','--check','--off',off,name", "'--fast','--check','--wbits',bits,'--off',off,name")
start=s.index('def main():')
s=s[:start]+'''def main():
    ap=argparse.ArgumentParser();ap.add_argument('--case',type=int);a=ap.parse_args()
    shapes=json.loads((HERE/'data/six/shapes.json').read_text())
    cases=[dict(dirs=ds,bounds=[(4,4)]*6) for ds in shapes]
    (HERE/'data/cases.json').write_text(json.dumps(cases,indent=2)+'\\n')
    for i,case in enumerate(cases):
        if a.case is not None and a.case!=i:continue
        if (HERE/f'lean/RunWindow{i}.lean').exists() and (HERE/f'logs/four{i}-export.txt').exists():
            print('Already generated',i,flush=True);continue
        build(i,case)
if __name__=='__main__':main()
'''
(HERE/'scripts/certify.py').write_text(s,encoding='utf-8')
