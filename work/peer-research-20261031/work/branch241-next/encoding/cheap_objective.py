"""Shared-gate integer objective 21*alpha+2*e2+e3 (r6 support line).
No SAT dependency or solver claim; returns weighted literals for a PB/cardinality cap.
Centre variables are fixed selected. Empty-face gates are exact equivalences.
"""
import json,sys
from pathlib import Path
from collections import Counter
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from charge_fast import Geometry,Charges
from adaptive_pb import CNF

class CheapObjective:
    def __init__(self,geometry,centres,radius=4):
        self.G=geometry;self.centres=list(centres);self.cnf=CNF()
        self.ball={v for v in range(geometry.N) if any((v^x).bit_count()<=radius for x in centres)}
        self.var={v:self.cnf.fresh() for v in sorted(self.ball)}
        self.empty={};self.alpha_gates={};self.by_centre={}
        for x in centres:
            self.cnf.clauses.append([self.var[x]])
            local=[]
            for _,_,_,vs in geometry.squares:
                if x in vs:
                    other=tuple(sorted(v for v in vs if v!=x))
                    if other not in self.alpha_gates:self.alpha_gates[other]=self.gate_empty(other)
                    local.append((self.alpha_gates[other],21,'alpha'))
                elif any((v^x).bit_count()==1 for v in vs):
                    local.append((self.gate_empty(vs),2,'e2'))
            for (_,_,_,vs),boundary in zip(geometry.cubes,geometry.cube_boundary):
                if boundary>>x&1:local.append((self.gate_empty(vs),1,'e3'))
            self.by_centre[x]=local
        weights=Counter()
        for local in self.by_centre.values():
            for lit,w,kind in local:weights[lit]+=w
        self.terms=sorted(weights.items())
    def gate_empty(self,vs):
        key=tuple(sorted(vs))
        if not set(key)<=self.ball:raise ValueError('objective truncated by ball; use radius4')
        if key not in self.empty:self.empty[key]=self.cnf.AND(*[-self.var[v] for v in key])
        return self.empty[key]
    def evaluate(self,selected):
        S=set(selected);a=self.cnf.witness({var:v in S for v,var in self.var.items()})
        assert self.cnf.satisfied(a)
        out={}
        for x,terms in self.by_centre.items():
            out[x]=sum(w for lit,w,_ in terms if a[abs(lit)]==(lit>0))
        return out
    def export(self):
        return dict(scale=21,definition='21*alpha+2*e2+e3',centres=self.centres,
                    vertex_variables=self.var,terms=self.terms,variables=self.cnf.nv,
                    clauses=self.cnf.clauses,
                    status='objective encoding only; no window bound or Lean certificate')

def main():
    here=Path(__file__).resolve().parent
    repo=here.parents[1]/'branch241-audit/repo'
    bank=json.loads((repo/'work/bank9.json').read_text())
    path=bank[67]['vertex_sequence'];G=Geometry(9);C=Charges(G,path)
    target=C.cheap()['r6'];assert target['scale']==21
    controls=[]
    for k in (1,3,7,9):
        centres=path[1:1+k];E=CheapObjective(G,centres)
        got=E.evaluate(path);want={x:target['values'][x] for x in centres}
        assert got==want,(got,want)
        assert all(got[x]*G.A<=C.a[x]*21 for x in centres)
        row=dict(bank_index=67,centres=k,centre_vertices=centres,values=list(got.values()),
                 total=sum(got.values()),variables=E.cnf.nv,clauses=len(E.cnf.clauses),
                 unique_empty_gates=len(E.empty),weighted_terms=len(E.terms),ball_vertices=len(E.ball))
        controls.append(row)
        if k==9:(here/'cheap_objective_bank67.json').write_text(json.dumps(E.export()))
    result=dict(status='passed',controls=controls,
                validation='canonical gate assignment satisfies all clauses and agrees with charge_fast.cheap r6',
                formal_status='no SAT run; no UNSAT lower bound; new Lean soundness lemmas still required')
    (here/'cheap_objective_controls.json').write_text(json.dumps(result,indent=2))
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
