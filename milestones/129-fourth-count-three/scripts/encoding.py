"""Reconstruct the tagged expanded input without mutating any saved evidence."""
from pathlib import Path
import json,sys
H=Path(__file__).resolve().parents[1];R=H.parents[1]
def build():
 sys.dont_write_bytecode=True
 sys.path[:0]=[str(R/'milestones/10-window-aggregate/scripts'),str(R/'work/solver_packages')]
 from gen_lean_sat import TaggedEncoding
 read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
 case=read(R/'milestones/125-critical-six-count/data/probes/0120324-total22-positive.json')
 cs=read(R/'milestones/127-direct-cardinality/data/direct-clauses.json')['corner_lists']
 e=TaggedEncoding(case['window'],case['bounds'],radius=9)
 e.atmost(sorted(-e.var[v] for c in cs for v in c),22,('unproved_sum',))
 for cut in case['cycle_cuts']:e.add([-e.var[v] for v in cut],('cut',))
 e.atmost([e.var[v] for v in cs[1]+cs[3]],34,('proved_pair_lower',))
 e.atmost([e.var[v] for v in cs[0]],18,('lo',0))
 e.atmost([e.var[v] for v in cs[1]],16,('lo',1))
 e.atmost([-e.var[v] for v in cs[3]],3,('hi',3))
 e.atmost(sorted(-e.var[v] for i in [2,4,5] for v in cs[i]),11,('proved_other_three',))
 exact=(f'p cnf {e.nv} {len(e.clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in e.clauses)).encode()
 assert e.nv==10175 and len(e.clauses)==112225 and len(e.ctrs)==13
 assert exact==(H/'work/expanded.cnf').read_bytes()
 return e
