"""Recognize the share-free refutation core and prepare an ordinary Lean certificate."""
import gzip,json,subprocess,sys,types
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
sys.path[:0]=[str(ROOT/'work/share_packages'),str(ROOT/'work/solver_packages'),str(ROOT/'milestones/10-window-aggregate/scripts')]
import gen_lean_sat as gen
def cnf(p):return [list(map(int,l.split()))[:-1] for l in p.read_text().splitlines() if l.strip() and not l.startswith(('p','c'))]
def main():
    prefix=HERE/'certificates/obstruction0';meta=json.loads(prefix.with_suffix('.json').read_text())
    with gzip.open(prefix.with_suffix('.meanings.json.gz'),'rt') as f:info=json.load(f)
    full=cnf(prefix.with_suffix('.cnf'));core=cnf(prefix.with_suffix('.core.cnf'))
    lookup={tuple(sorted(c)):i for i,c in enumerate(full)};ids=[lookup[tuple(sorted(c))] for c in core]
    core=[full[i] for i in ids]  # restore the original literal order required by the tag checker
    tags=[info['tags'][i] for i in ids];assert all(t[0]=='old' for t in tags)
    used=sorted({abs(v) for cl in core for v in cl});old={int(k):v for k,v in info['meaning'].items()}
    assert set(used)<=old.keys();ordering=used+sorted(old.keys()-set(used));rename={v:i+1 for i,v in enumerate(ordering)}
    def lit(x):return (1 if x>0 else -1)*rename[abs(x)]
    compact=[[lit(v) for v in cl] for cl in core]
    out=HERE/'certificates/plain0.cnf'
    out.write_text(f'p cnf {len(used)} {len(core)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in compact))
    for folder in ['LocalWindowCnf','LocalWindowSat']:(HERE/'lean'/folder).mkdir(exist_ok=True)
    raw='[\n'+',\n'.join('['+','.join(str(gen.code(v)) for v in c)+']' for c in compact)+'\n]'
    text='import LocalWindowModel\nset_option maxRecDepth 100000\nnamespace Snake9.LocalWindow.ShareGap0\n'
    text+='def window : List Nat := '+str(meta['window'])+'\n'
    text+='def bounds : List (Nat × Nat) := ['+','.join(f'({a},{b})' for a,b in meta['bounds'])+']\n'
    text+='def raw : List (List Nat) := '+raw+'\ndef cnf : List (List Int) := raw.map (·.map decodeLit)\nend Snake9.LocalWindow.ShareGap0\n'
    (HERE/'lean/LocalWindowCnf/ShareGap0.lean').write_text(text,encoding='utf-8')
    enc=types.SimpleNamespace(nv=len(ordering),meaning={rename[k]:v for k,v in old.items()},
        ctrs=[([lit(x) for x in ls],k,kind) for ls,k,kind in info['ctrs']])
    gen.LEAN=str(HERE/'lean')
    gen.write_module('plain0','ShareGap0',dict(module='LocalWindowCnf.ShareGap0'),enc,[t[1] for t in tags])
    coremeta=dict(module='LocalWindowCnf.ShareGap0',core_ids=list(range(1,len(core)+1)),source_original_clause_ids=[i+1 for i in ids],active_variables=len(used),old_variable_count=len(old),original_to_new=rename,
        conclusion='The extracted refutation uses no empty-square-share clauses.')
    (HERE/'data/plain0.json').write_text(json.dumps(coremeta,indent=2)+'\n')
    exe='D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin/cadical.exe'
    result=subprocess.run([exe,'-q','--lrat','--no-binary',str(out),str(HERE/'certificates/plain0.lrat')],capture_output=True,text=True,timeout=120)
    (HERE/'logs/plain-cadical.txt').write_text(result.stdout+result.stderr)
    assert result.returncode==20 and 'UNSATISFIABLE' in result.stdout
    cmd=[sys.executable,'-X','utf8',str(ROOT/'milestones/10-window-aggregate/scripts/gen_lean_lrat.py'),'--work',str(HERE/'certificates'),'--data',str(HERE/'data'),'--out',str(HERE/'lean'),'--fast','--check','plain0']
    result=subprocess.run(cmd,capture_output=True,text=True)
    (HERE/'logs/lrat-export.txt').write_text(result.stdout+result.stderr)
    assert result.returncode==0,result.stdout+result.stderr
    print(len(core),'clauses;',len(used),'variables;',result.stdout)
if __name__=='__main__':main()
