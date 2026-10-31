"""Use the actual GitHub Encoding class without importing its optional solver.
AST selection only removes unrelated solver/build-driver definitions, not geometric clauses.
"""
import ast,gzip,hashlib,itertools,json
from pathlib import Path
from cheap_folded import FixedPathObjective
from pb_binary import BinaryCNF
from charge_fast import Geometry
from build_pb_controls import propagate
HERE=Path(__file__).resolve().parent;REPO=HERE.parents[1]/'branch241-audit/repo'
def load_encoding(repo=REPO):
 p=repo/'milestones/10-window-aggregate/scripts/wincert.py';s=p.read_text(encoding='utf-8');tree=ast.parse(s)
 nodes=[n for n in tree.body if isinstance(n,ast.ClassDef) and n.name=='Encoding'];assert len(nodes)==1
 ns={'combinations':itertools.combinations};exec(compile(ast.Module(body=nodes,type_ignores=[]),str(p),'exec'),ns)
 return ns['Encoding'],hashlib.sha256(p.read_bytes()).hexdigest()
def build(path,cap,bonus=True,repo=REPO,radius=4):
 if radius not in range(4,10):raise ValueError("geometry radius must be 4..9")
 E=FixedPathObjective(Geometry(9),path,occupancy_bonus=bonus,cnf_factory=BinaryCNF);Encoding,sha=load_encoding(repo)
 class RecordEncoding(Encoding):
  def atmost(self,lits,k,kind):
   before=self.nv;super().atmost(lits,k,kind)
   if self.nv>before:self.counters.append((list(lits),k,before+1))
  def __init__(self,*args,**kwargs):self.counters=[];super().__init__(*args,**kwargs)
 geo=RecordEncoding(path,[None]*(len(path)-2),radius)
 assert set(E.var)<=set(geo.var)
 for v in sorted(set(geo.var)-set(E.var)):E.var[v]=E.cnf.fresh()
 E.ball=set(geo.var)
 remap={geo.var[v]:E.var[v] for v in geo.var}
 for old in range(len(geo.var)+1,geo.nv+1):remap[old]=E.cnf.fresh()
 def lit(l):return remap[abs(l)]*(1 if l>0 else -1)
 E.cnf.clauses.extend([[lit(l) for l in c] for c in geo.clauses]);geometric_count=len(geo.clauses)
 target=E.cnf.leq_binary(E.terms,cap-E.offset);E.cnf.clauses.append([target])
 return E,geo,remap,{'source_wincert_sha256':sha,'cap_scaled21':cap,'bonus':bonus,'geometry_radius':radius,'geometry_clauses':geometric_count,'total_variables':E.cnf.nv,'total_clauses':len(E.cnf.clauses),'path':path,'objective':'21alpha+2e2+e3'+('+V' if bonus else ''),'scope':'Git Encoding necessary conditions plus objective cap; SAT can still contain extra cycles until lazy cuts. No Lean proof.'}
def bank_witness(E,geo,remap,S):
 S=set(S);old={geo.var[v]:v in S for v in geo.var}
 for c,k in zip(geo.clauses,geo.kinds):
  if k=='end_selected':
   e=-c[0];v=next(x for x,y in geo.var.items() if y==c[1]);old[e]=v in S and sum(v^(1<<d) in S for d in range(9))==1
 def val(l):return old[abs(l)]==(l>0)
 for lits,k,start in geo.counters:
  count=0
  for i,l in enumerate(lits):
   count+=val(l)
   for j in range(k):old[start+i*k+j]=count>=j+1
 assert len(old)==geo.nv
 return E.cnf.witness({remap[v]:b for v,b in old.items()})
def write(E,p,comment):
 with gzip.open(p,'wt',encoding='ascii') as f:
  f.write('c '+comment+'\n');f.write(f'p cnf {E.cnf.nv} {len(E.cnf.clauses)}\n')
  for c in E.cnf.clauses:f.write(' '.join(map(str,c))+' 0\n')
def main():
 bank=json.loads((REPO/'work/bank9.json').read_text());S=bank[67]['vertex_sequence'];path=S[:11]
 # Positive control: known bank score, including actual Git geometric clauses.
 E,geo,m,meta=build(path,2675);a=bank_witness(E,geo,m,S);assert E.cnf.satisfied(a)
 meta['known_bank67_positive_control']='all geometric/objective/PB clauses satisfied'
 # A genuine free-window search candidate, not a proven threshold.
 Q,g,m,qmeta=build(path,850);qmeta['unit_propagation']=propagate(Q.cnf.clauses)
 write(Q,HERE/'github_window9_bonus_cap850.cnf.gz','FREE WINDOW QUERY; necessary snake conditions; not a certified result')
 (HERE/'github_query_metadata.json').write_text(json.dumps({'positive_control':meta,'candidate_query':qmeta},indent=2));print(json.dumps({'positive_control':meta,'candidate_query':qmeta},indent=2))
if __name__=='__main__':main()
