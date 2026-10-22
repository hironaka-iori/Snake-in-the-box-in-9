"""Extract ordinary cores and generate kernel-replay sources for joint windows."""
import argparse,json,subprocess,sys,types
from pathlib import Path
from joint import ROOT,HERE,TaggedEncoding,window,candidates
import gen_lean_sat as gen
LEANBIN=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
def run(cmd,log,expected=0):
    p=subprocess.run(list(map(str,cmd)),capture_output=True,text=True,encoding='utf-8',timeout=300)
    (HERE/'logs'/log).write_text(p.stdout+p.stderr,encoding='utf-8')
    assert p.returncode==expected,(cmd,p.returncode,p.stdout[-1000:],p.stderr[-1000:])
    return p.stdout
def readcnf(p):return [list(map(int,l.split()))[:-1] for l in p.read_text().splitlines() if l.strip() and not l.startswith(('p','c'))]
def writecnf(p,n,clauses):p.write_text(f'p cnf {n} {len(clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in clauses))
def build(i,case):
    (HERE/'certificates').mkdir(exist_ok=True)
    for d in ['LocalWindowCnf','LocalWindowSat']:(HERE/'lean'/d).mkdir(exist_ok=True)
    name=f'joint{i}';mod=f'JointFour{i}';prefix=HERE/'certificates'/name
    enc=TaggedEncoding(window(case['dirs']),[(4,4)]*7,radius=4)
    full=prefix.with_suffix('.full.cnf');drat=prefix.with_suffix('.drat');core=prefix.with_suffix('.core.cnf')
    writecnf(full,enc.nv,enc.clauses)
    run([LEANBIN/'cadical.exe','-q','--no-binary',full,drat],name+'-cadical.txt',20)
    report=run([ROOT/'work/share-wheels/drat-trim.exe',full,drat,'-c',core],name+'-drat-check.txt')
    assert 's VERIFIED' in report
    rawcore=readcnf(core);lookup={tuple(sorted(c)):j for j,c in enumerate(enc.clauses)}
    ids=[lookup[tuple(sorted(c))] for c in rawcore];clauses=[enc.clauses[j] for j in ids]
    used=sorted({abs(v) for c in clauses for v in c});ordering=used+sorted(enc.meaning.keys()-set(used));rename={v:j+1 for j,v in enumerate(ordering)}
    lit=lambda v:(1 if v>0 else -1)*rename[abs(v)]
    compact=[[lit(v) for v in c] for c in clauses];writecnf(prefix.with_suffix('.cnf'),len(used),compact)
    raw='[\n'+',\n'.join('['+','.join(str(gen.code(v)) for v in c)+']' for c in compact)+'\n]'
    src=f'import LocalWindowModel\nset_option maxRecDepth 100000\nnamespace Snake9.LocalWindow.{mod}\n'
    src+=f'def window : List Nat := {enc.window}\ndef bounds : List (Nat × Nat) := ['+','.join('(4,4)' for _ in range(7))+']\n'
    src+='def raw : List (List Nat) := '+raw+f'\ndef cnf : List (List Int) := raw.map (·.map decodeLit)\nend Snake9.LocalWindow.{mod}\n'
    (HERE/'lean/LocalWindowCnf'/f'{mod}.lean').write_text(src,encoding='utf-8')
    small=types.SimpleNamespace(nv=len(ordering),meaning={rename[k]:v for k,v in enc.meaning.items()},ctrs=[([lit(x) for x in ls],k,kind) for ls,k,kind in enc.ctrs])
    gen.LEAN=str(HERE/'lean');gen.write_module(name,mod,dict(module='LocalWindowCnf.'+mod),small,[enc.tags[j] for j in ids])
    meta=dict(module='LocalWindowCnf.'+mod,core_ids=list(range(1,len(compact)+1)),source_original_clause_ids=[j+1 for j in ids],active_variables=len(used),original_to_new=rename,dirs=case['dirs'],bounds=[[4,4]]*7)
    (HERE/'data'/f'{name}.json').write_text(json.dumps(meta,indent=2)+'\n')
    run([LEANBIN/'cadical.exe','-q','--lrat','--no-binary',prefix.with_suffix('.cnf'),prefix.with_suffix('.lrat')],name+'-lrat-cadical.txt',20)
    off=next(v for v in [2400,3000,4000] if v>len(used))
    report=run([sys.executable,'-X','utf8',ROOT/'milestones/10-window-aggregate/scripts/gen_lean_lrat.py','--work',HERE/'certificates','--data',HERE/'data','--out',HERE/'lean','--fast','--check','--off',off,name],name+'-export.txt')
    wrapper=f'''import LocalWindowSat.{mod}
import LocalWindowUnsat.{mod}
import LocalWindowBridge
namespace Snake9.LocalWindow.{mod}
theorem refuted : Refuted window bounds := Tags.refuted_of_sat sat unsat
def directions : List Nat := {case['dirs']}
theorem excluded_in_snake {{m : Nat}} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + directions.length ≤ m)
    (hP : ∀ j, j < directions.length → P.fwd (dir p (r+j)) = directions.getD j 0)
    (hb : ∀ i, i < bounds.length →
      (bounds.getD i (0,21)).1 ≤ coreAlpha p (r+i+1) ∧
      coreAlpha p (r+i+1) ≤ (bounds.getD i (0,21)).2) : False :=
  refuted_bridge p P r (cs := directions) refuted ⟨rfl,rfl,by decide⟩ (by decide) hr hP hb
#print axioms refuted
#print axioms excluded_in_snake
end Snake9.LocalWindow.{mod}
'''
    (HERE/'lean'/f'Window{i}.lean').write_text(wrapper,encoding='utf-8')
    print(name,len(compact),'clauses;',len(used),'variables;',report.strip(),flush=True)
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--case',type=int);a=ap.parse_args();cases=candidates()
    for i in [3,0,2,1]:
        if a.case is None or a.case==i:build(i,cases[i])
if __name__=='__main__':main()
