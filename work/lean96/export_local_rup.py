"""Emit ordinary kernel-checked reflection proofs from untrusted LRAT cores."""
import json,sys,subprocess,os,time,hashlib
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
def emit(entry,folder=None):
    folder=folder or HERE/'bank'
    folder.mkdir(exist_ok=True)
    survey=json.loads((ROOT/'outputs/lean96/survey.json').read_text())['entries']
    core_entry=survey[str(entry)].get('reused_from',entry)
    core=json.loads((ROOT/f'outputs/lean96/cores/entry{core_entry:03d}.json').read_text())
    prefix=f'B96E{entry:03d}'
    header=f'namespace {prefix}\nopen Snake9.LocalRup\nset_option maxHeartbeats 0\nset_option maxRecDepth 1000000\n'
    end=f'end {prefix}\n'
    def ls(c):return '['+', '.join(f'({abs(v)}, {str(v>0).lower()})' for v in c)+']'
    def goal(c):return ' ∨ '.join(f'p {abs(v)} = {str(v>0).lower()}' for v in c) or 'False'
    def write(name,s):
        dest=folder/(name+'.lean')
        if not dest.exists() or dest.read_text(encoding='utf-8')!=s:dest.write_text(s,encoding='utf-8')
        return name
    modules=[];s='import TreeRup\n'+header
    count=len(core['clauses']);blocks=(count+31)//32
    for block in range(blocks):
        s+=f'structure Block{block} (p : Nat → Bool) : Prop where\n'
        for k in range(block*32,min((block+1)*32,count)):
            s+=f'  clause{k+1} : {goal(core["clauses"][k])}\n'
    s+='structure Constraints (p : Nat → Bool) : Prop where\n'+''.join(f'  block{b} : Block{b} p\n' for b in range(blocks))
    for k,c in enumerate(core['clauses'],1):
        s+=f'def c{k} : List Lit := {ls(c)}\n'
        s+=f'theorem step{k} (p : Nat → Bool) (h : Constraints p) : clause p c{k} = true := by\n'
        s+=f'  simpa only [c{k},clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block{(k-1)//32}.clause{k}\n'
    modules.append(write(prefix+'Inputs',s+end))
    chunk=64
    for part,start in enumerate(range(0,len(core['proof']),chunk)):
        s='import '+modules[-1]+'\n'+header
        for ident,c,hints in core['proof'][start:start+chunk]:
            s+=f'def c{ident} : List Lit := {ls(c)}\n'
            hs=f'sat_nil p'
            for h in reversed(hints):hs=f'sat_cons (step{h} p h) ({hs})'
            s+=f'theorem step{ident} (p : Nat → Bool) (h : Constraints p) : clause p c{ident} = true :=\n'
            helper='Snake9.TreeRup.prove_clause' if len(hints)>60 else 'Snake9.LocalRup.prove_clause'
            s+=f'  {helper} ['+', '.join(f'c{h}' for h in hints)+f'] c{ident} (by decide) p ({hs})\n'
        modules.append(write(prefix+f'Part{part:04d}',s+end))
    final=core['proof'][-1][0]
    s='import '+modules[-1]+'\n'+header
    s+=f'theorem constraints_unsat (p : Nat → Bool) (h : Constraints p) : False := by\n  have hh := step{final} p h\n  contradiction\n#print axioms constraints_unsat\n'
    modules.append(write(prefix,s+end))
    return modules

if __name__=='__main__':
    entry=int(sys.argv[1]);folder=HERE/'bank';modules=emit(entry,folder)
    print('Generated',entry,len(modules),'modules',flush=True)
    if '--check' in sys.argv:
        lean=ROOT.parent/'Snake in the Box/work/research_20261015/proof/dependencies/lean-4.19.0-windows/bin/lean.exe'
        env=os.environ.copy();env['LEAN_PATH']=str(folder)+';'+str(HERE)
        t=time.time()
        for name in modules:
            t0=time.time()
            p=subprocess.run([str(lean),'--root='+str(folder),'-o',str(folder/(name+'.olean')),str(folder/(name+'.lean'))],env=env,cwd=ROOT)
            print(name,p.returncode,round(time.time()-t0,2),'seconds',flush=True)
            if p.returncode:sys.exit(p.returncode)
        print('Checked all in',time.time()-t,'seconds',flush=True)
