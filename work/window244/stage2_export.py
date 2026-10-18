"""Parameterized Stage-2 exporter; emitted proofs must pass the kernel.

Derived from the frozen Stage-1 exporter, with separate output namespaces.
Every hint group exceeding 120 is compiled alone; no Stage-1 input is edited.
"""
import json,sys,subprocess,os,time,hashlib
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
def emit(shape,core_path,prefix,folder=None):
    folder=folder or HERE/'stage2_generated'
    folder.mkdir(exist_ok=True)
    core=json.loads(Path(core_path).read_text())
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
        if block and block % 4 == 0:
            modules.append(write(prefix+f'Types{block//4-1:03d}',s+end))
            s='import '+modules[-1]+'\n'+header
        s+=f'structure Block{block} (p : Nat → Bool) : Prop where\n'
        for k in range(block*32,min((block+1)*32,count)):
            s+=f'  clause{k+1} : {goal(core["clauses"][k])}\n'
    modules.append(write(prefix+f'Types{(blocks-1)//4:03d}',s+end))
    s='import '+modules[-1]+'\n'+header
    s+='structure Constraints (p : Nat → Bool) : Prop where\n'+''.join(f'  block{b} : Block{b} p\n' for b in range(blocks))
    modules.append(write(prefix+'Constraints',s+end))
    s='import '+modules[-1]+'\n'+header
    for k,c in enumerate(core['clauses'],1):
        if k>1 and (k-1)%64==0:
            modules.append(write(prefix+f'Inputs{(k-1)//64-1:03d}',s+end))
            s='import '+modules[-1]+'\n'+header
        s+=f'def c{k} : List Lit := {ls(c)}\n'
        s+=f'theorem step{k} (p : Nat → Bool) (h : Constraints p) : clause p c{k} = true := by\n'
        s+=f'  simpa only [c{k},clause,value,List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false] using h.block{(k-1)//32}.clause{k}\n'
    modules.append(write(prefix+f'Inputs{(count-1)//64:03d}',s+end))
    chunk=8
    for part,start in enumerate(range(0,len(core['proof']),chunk)):
        s='import '+modules[-1]+'\n'+header
        split = True
        weight=0;subpart=0
        for offset,(ident,c,hints) in enumerate(core['proof'][start:start+chunk]):
            if split and weight and weight+len(hints)>120:
                modules.append(write(prefix+f'Part{part:04d}Batch{subpart}',s+end))
                s='import '+modules[-1]+'\n'+header
                subpart+=1;weight=0
            s+=f'def c{ident} : List Lit := {ls(c)}\n'
            hs=f'sat_nil p'
            for h in reversed(hints):hs=f'sat_cons (step{h} p h) ({hs})'
            s+=f'theorem step{ident} (p : Nat → Bool) (h : Constraints p) : clause p c{ident} = true :=\n'
            helper='Snake9.TreeRup.prove_clause' if len(hints)>60 else 'Snake9.LocalRup.prove_clause'
            s+=f'  {helper} ['+', '.join(f'c{h}' for h in hints)+f'] c{ident} (by decide) p ({hs})\n'
            weight+=len(hints)
            if False:  # No stage-one-specific exceptional module numbering.
                modules.append(write(prefix+f'Part{part:04d}Step{offset}',s+end))
                s='import '+modules[-1]+'\n'+header
                weight=0
        modules.append(write(prefix+f'Part{part:04d}',s+end))
    final=core['proof'][-1][0]
    s='import '+modules[-1]+'\n'+header
    s+=f'theorem constraints_unsat (p : Nat → Bool) (h : Constraints p) : False := by\n  have hh := step{final} p h\n  contradiction\n#print axioms constraints_unsat\n'
    modules.append(write(prefix,s+end))
    return modules

