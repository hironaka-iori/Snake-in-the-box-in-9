"""Build real three-centre queries with binary and GT PB; never invoke SAT."""
from pathlib import Path
from collections import Counter
import sys,json,time,gc,gzip
R=Path(__file__).resolve().parent;B=R.parent/'branch241-next';sys.path[:0]=[str(B),str(B/'encoding')]
from github_query import build,bank_witness,REPO
from pb_binary import BinaryCNF
from charge_fast import Geometry,Charges
from gt_pb import GeneralizedTotalizer

def rgs(ds):
 seen={};return tuple(seen.setdefault(d,len(seen)) for d in ds)
def control(shape,bank):
 for row in bank:
  p=row['vertex_sequence']
  for start in range(len(p)-4):
   ds=[(p[j]^p[j+1]).bit_length()-1 for j in range(start,start+4)]
   if rgs(ds)!=shape:continue
   order=list(dict.fromkeys(ds));mapping={d:i for i,d in enumerate(order)}
   mapping.update(zip([d for d in range(9) if d not in mapping],[i for i in range(9) if i not in mapping.values()]))
   transform=lambda x:sum(1<<mapping[d] for d in range(9) if (x^p[start])>>d&1)
   return list(map(transform,p)),list(map(transform,p[start:start+5]))
 raise ValueError('no genuine bank control of this direction shape')

def main():
 saved=BinaryCNF.leq_binary;rows=[];bank=json.loads((REPO/'work/bank9.json').read_text());geo=Geometry(9)
 for shape,path in [((0,1,2,0),[0,1,3,7,6]),((0,1,2,3),[0,1,3,7,15])]:
  result={'shape':''.join(map(str,shape)),'cap_scaled21':254,'SAT_search_run':False}
  def binary(self,terms,cap):
   oldnv=self.nv;oldcs=len(self.clauses);target=saved(self,terms,cap)
   self.review_stats={'new_variables':self.nv-oldnv,'new_clauses':len(self.clauses)-oldcs};return target
  BinaryCNF.leq_binary=binary;start=time.perf_counter();E,_,_,meta=build(path,254)
  result['binary']={**E.cnf.review_stats,'query_variables':E.cnf.nv,'query_clauses_before_static8':len(E.cnf.clauses),'build_seconds':time.perf_counter()-start};del E;gc.collect()
  def gt(self,terms,cap):
   self.review_gt=GeneralizedTotalizer(self,terms,cap);return self.review_gt.target
  BinaryCNF.leq_binary=gt;start=time.perf_counter();E,g,m,meta=build(path,254);G=E.cnf.review_gt
  result['GT']={**G.statistics(),'query_variables':E.cnf.nv,'query_clauses_before_static8':len(E.cnf.clauses),'build_seconds':time.perf_counter()-start}
  S,window=control(shape,bank);assert window==path
  assignment=G.extend(bank_witness(E,g,m,S));assert len(assignment)==E.cnf.nv
  assert all(any(assignment[abs(l)]==(l>0) for l in c) for c in E.cnf.clauses[:-1])
  cheap=Charges(geo,S).cheap()['r6plus'];score=sum(cheap['values'][x] for x in E.centres)
  assert (assignment[abs(G.target)]==(G.target>0))==(score<=254)
  result['GT_bank_control']={'all_base_geometry_forward_PB_clauses_satisfied':True,'canonical_extension_complete':True,'exact_score':score,'cap_predicate_exact':True}
  with gzip.open(R/f"loop_k3_cap254_r4_d{result['shape']}_all8/checkpoint.json.gz",'rt',encoding='utf-8') as f:state=json.load(f)
  static8=state['meta']['static8_count'];result['folded_static8_clauses']=static8
  for name in ('binary','GT'):result[name]['query_clauses_with_static8']=result[name]['query_clauses_before_static8']+static8
  rows.append(result);del E,G,assignment;gc.collect()
 BinaryCNF.leq_binary=saved
 output={'status':'Cost and canonical model controls only; no GT solver run or new bound','results':rows}
 (R/'gt_cost_comparison.json').write_text(json.dumps(output,indent=2));print(json.dumps(output,indent=2))
if __name__=='__main__':main()
