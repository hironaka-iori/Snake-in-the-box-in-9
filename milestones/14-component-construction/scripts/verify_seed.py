"""Independent pairwise audit and generation of the concrete Lean certificate."""
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[3]
HERE=Path(__file__).resolve().parents[1]


def adjacent(a,b):return (a^b).bit_count()==1
def sha(p):return hashlib.sha256(p.read_bytes().replace(b'\r\n',b'\n')).hexdigest()


def main():
    data=json.loads((HERE/'data/product-seed.json').read_text())
    selected=data['seed_vertices']
    assert len(selected)==len(set(selected))==197 and all(0<=v<512 for v in selected)
    # Enumerate pairs directly, independently of the solver's coordinate-neighbor implementation.
    adj={v:[w for w in selected if adjacent(v,w)] for v in selected}
    assert all(len(adj[v]) in (1,2) for v in selected)
    ends=sorted(v for v in selected if len(adj[v])==1)
    assert len(ends)==2 and ends[0]==0 and adj[0]==[1]
    edges=sum(map(len,adj.values()))//2
    assert edges==196
    todo=set(selected);parts=[]
    while todo:
        seen=set();stack=[min(todo)]
        while stack:
            v=stack.pop()
            if v in seen:continue
            seen.add(v);stack.extend(adj[v])
        todo-=seen;parts.append(sorted(seen))
    assert parts==data['seed_components']
    cycles=[c for c in parts if not set(c)&set(ends)]
    pathpart=next(c for c in parts if ends[0] in c)
    assert len(cycles)==7 and all(len(c)==26 for c in cycles) and len(pathpart)==15
    path=[0]
    while len(path)<len(pathpart):
        following=[w for w in adj[path[-1]] if w not in path]
        assert len(following)==1
        path.append(following[0])
    for i,v in enumerate(path):
        for j,w in enumerate(path):assert adjacent(v,w)==(abs(i-j)==1)
    def lst(xs):return '['+','.join(map(str,xs))+']'
    source='''import CycleCuts
namespace Snake9.ComponentConstruction.Seed
open Classical CycleExclusion
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
'''
    source+=f'def vertices : List Vertex := {lst(selected)}\n'
    source+=f'def endpoints : List Vertex := {lst(ends)}\n'
    source+='def cycles : List (List Vertex) := ['+','.join(lst(c)for c in cycles)+']\n'
    source+=f'def pathVertices : List Vertex := {lst(path)}\n'
    source+='''
def degreeCheck : Bool := vertices.all (fun v =>
  (vertices.filter (fun w => decide (Adj v w))).length ==
    (if endpoints.contains v then 1 else 2))
theorem vertex_count : vertices.length = 197 := by decide
theorem vertices_distinct : vertices.Nodup := by decide
theorem endpoint_count : endpoints.length = 2 := by decide
theorem endpoints_selected : endpoints.all vertices.contains = true := by decide
theorem degrees_checked : degreeCheck = true := by decide
theorem cycles_checked : cycles.all cycleCheck = true := by decide
theorem partition_checked :
    (pathVertices ++ cycles.flatten).toFinset = vertices.toFinset ∧
    (pathVertices ++ cycles.flatten).Nodup := by decide
theorem cuts_valid {m : Nat} (p : Snake m) : ∀ c ∈ cycles,
    (c.toFinset.filter (fun v => InPath p v)).card ≤ c.toFinset.card-1 := by
  intro c hc
  exact checked_cycle_cut p c (List.all_eq_true.mp cycles_checked c hc)
#print axioms vertex_count
#print axioms vertices_distinct
#print axioms degrees_checked
#print axioms partition_checked
#print axioms cuts_valid
end Snake9.ComponentConstruction.Seed
'''
    (HERE/'lean/SeedCertificate.lean').write_text(source,encoding='utf-8',newline='\n')
    report={'status':'PASSED','vertices':197,'edges':edges,'component_sizes':list(map(len,parts)),
        'endpoints':ends,'path_vertices':path,'pair_count':197*196//2,
        'scope':'Independent seed audit; disconnected graph, not a 196-edge snake.',
        'sha256_lf':{}}
    for p in [HERE/'data/product-seed.json',HERE/'lean/SeedCertificate.lean',Path(__file__)]:
        report['sha256_lf'][p.relative_to(ROOT).as_posix()]=sha(p)
    (HERE/'data/seed-audit.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('sha256_lf','path_vertices')}))


if __name__=='__main__':main()
