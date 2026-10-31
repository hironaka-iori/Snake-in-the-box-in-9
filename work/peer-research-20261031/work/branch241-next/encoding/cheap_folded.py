"""Path-aware constant folding of exact 21*alpha+2*e2+e3 objective.
Sound only with the emitted selected/forbidden unit clauses. No universal window bound.
"""
import json,sys
from pathlib import Path
from collections import Counter
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from charge_fast import Geometry,Charges
from adaptive_pb import CNF

class FixedPathObjective:
 def __init__(self,G,path,occupancy_bonus=False,cnf_factory=CNF):
  self.occupancy_bonus=occupancy_bonus
  self.G=G;self.path=list(path);self.centres=self.path[1:-1];self.cnf=cnf_factory()
  if not self.centres:raise ValueError('need an internal centre')
  if len(set(path))!=len(path):raise ValueError('repeated path vertex')
  for i,a in enumerate(path):
   for j in range(i+1,len(path)):
    if ((a^path[j]).bit_count()==1)!=(j==i+1):raise ValueError('path is not induced')
  self.ball={v for v in range(G.N) if any((v^x).bit_count()<=4 for x in self.centres)}
  self.var={v:self.cnf.fresh() for v in sorted(self.ball)}
  self.selected=set(path);self.forbidden=set()
  for i,x in enumerate(path[1:-1],1):
   allowed={path[i-1],path[i+1]};self.forbidden.update((x^(1<<d)) for d in range(G.n) if x^(1<<d) not in allowed)
  assert not self.selected&self.forbidden
  for v in self.selected:self.cnf.clauses.append([self.var[v]])
  for v in self.forbidden:self.cnf.clauses.append([-self.var[v]])
  self.empty={};self.by_centre={};self.occurrences=0
  def empty(vs):
   vs=set(vs)
   if not vs<=self.ball:raise ValueError('radius truncation')
   if vs&self.selected:return -self.cnf.one
   key=tuple(sorted(vs-self.forbidden))
   if not key:return self.cnf.one
   if len(key)==1:return -self.var[key[0]]
   if key not in self.empty:self.empty[key]=self.cnf.AND(*[-self.var[v] for v in key])
   return self.empty[key]
  for x in self.centres:
   terms=[]
   for _,_,_,vs in G.squares:
    if x in vs:terms.append((empty(v for v in vs if v!=x),21))
    elif any((v^x).bit_count()==1 for v in vs):terms.append((empty(vs),2))
   for (_,_,_,vs),boundary in zip(G.cubes,G.cube_boundary):
    if boundary>>x&1:terms.append((empty(vs),1))
   self.by_centre[x]=terms;self.occurrences+=len(terms)
  if occupancy_bonus:
   self.mixed_events={}
   def event(present,absent):
    P=set(present);A=set(absent)
    if P&self.forbidden or A&self.selected:return -self.cnf.one
    if not (P|A)<=self.ball:raise ValueError('radius truncation')
    lits=tuple(sorted([self.var[v] for v in P-self.selected]+[-self.var[v] for v in A-self.forbidden]))
    if not lits:return self.cnf.one
    if len(lits)==1:return lits[0]
    if lits not in self.mixed_events:self.mixed_events[lits]=self.cnf.AND(*lits)
    return self.mixed_events[lits]
   for x in self.centres:
    for _,_,_,vs in G.cubes:
     if x not in vs:continue
     self.by_centre[x].append((empty(v for v in vs if v!=x),12))
     for y in vs:
      d=(x^y).bit_count()
      if d in (1,2):self.by_centre[x].append((event([y],[v for v in vs if v not in (x,y)]),2 if d==1 else 1))
  weights=Counter()
  for ts in self.by_centre.values():
   for lit,w in ts:weights[lit]+=w
  self.offset=weights.pop(self.cnf.one,0);weights.pop(-self.cnf.one,None)
  self.terms=sorted(weights.items())
 def evaluate(self,S):
  S=set(S)
  assert self.selected<=S and not self.forbidden&S
  a=self.cnf.witness({var:v in S for v,var in self.var.items()})
  assert self.cnf.satisfied(a)
  def val(l):return a[abs(l)]==(l>0)
  total=self.offset+sum(w for l,w in self.terms if val(l))
  per={x:sum(w for l,w in ts if val(l)) for x,ts in self.by_centre.items()}
  assert total==sum(per.values())
  return per
 def export(self):
  return {'status':'Objective + fixed-path units ONLY, not complete geometric Encoding or a certified bound','scale':21,'occupancy_bonus':self.occupancy_bonus,'offset':self.offset,'path':self.path,'centres':self.centres,'vertex_variables':self.var,'selected':sorted(self.selected),'forbidden':sorted(self.forbidden),'variables':self.cnf.nv,'clauses':self.cnf.clauses,'terms':self.terms}

def main():
 here=Path(__file__).resolve().parent;repo=here.parents[1]/'branch241-audit/repo';bank=json.loads((repo/'work/bank9.json').read_text());G=Geometry(9);rows=[]
 for k in (1,3,7,9):
  path=bank[67]['vertex_sequence'];C=Charges(G,path);E=FixedPathObjective(G,path[:k+2]);got=E.evaluate(path);target=C.cheap()['r6']['values'];assert got=={x:target[x] for x in E.centres}
  row={'centres':k,'variables':E.cnf.nv,'clauses':len(E.cnf.clauses),'unique_nontrivial_empty_gates':len(E.empty),'weighted_terms':len(E.terms),'constant_offset':E.offset,'total_score':sum(got.values()),'selected_units':len(E.selected),'forbidden_units':len(E.forbidden)};rows.append(row)
  if k==9:(here/'cheap_folded_bank67.json').write_text(json.dumps(E.export()))
 (here/'folded_controls.json').write_text(json.dumps({'bank67_controls':rows,'exact_agreement':True},indent=2));print(json.dumps(rows,indent=2))
if __name__=='__main__':main()
