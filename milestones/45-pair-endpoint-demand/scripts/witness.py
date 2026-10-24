"""Check a complete snake attaining the endpoint-free pair bound."""
from pathlib import Path
import hashlib,json,os,subprocess,time
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
r=json.loads((HERE/'data/full-first-radius-2-cap-8.json').read_text())
vs=r['vertex_sequence'];n=len(vs)-1;start=vs.index(0);a=start+2;b=start+6
assert vs[start:start+9]==[0,1,3,7,15,31,30,22,20]
assert len(set(vs))==len(vs)
assert all(((vs[i]^vs[j]).bit_count()==1)==(j==i+1) for i in range(n+1) for j in range(i+1,n+1))
distances=[(vs[a]^vs[k]).bit_count() for k in [0,n]]
assert min(distances)>=3
source=f'''import EndpointDistance
namespace Snake9.EndpointSharp
open Snake9.LocalWindow
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def values : Array Nat := #[{', '.join(map(str,vs))}]
def vertex (i : Fin {n+1}) : Vertex :=
  ⟨values[i.val]! % 512, Nat.mod_lt _ (by decide)⟩
theorem distinct : ∀ i j : Fin {n+1}, vertex i = vertex j → i = j := by decide +kernel
theorem induced : ∀ i j : Fin {n+1}, i.val < j.val →
    (Adj (vertex i) (vertex j) ↔ i.val+1=j.val) := by decide +kernel
def witness : Snake {n} := ⟨vertex, distinct, induced⟩
theorem window_directions : ∀ j : Fin 8,
    dir witness ({start}+j.val) = ([0,1,2,3,4,0,3,1] : List Nat).getD j.val 0 := by
  simp only [dir, Tags.dirOfStep_eq]
  decide +kernel
theorem pair_counts : coreAlpha witness {a} = 5 ∧ coreAlpha witness {b} = 3 := by decide +kernel
theorem endpoint_distances :
    EndpointPair451.hamming (vx witness {a}) (vx witness 0) = {distances[0]} ∧
    EndpointPair451.hamming (vx witness {a}) (vx witness {n}) = {distances[1]} := by decide +kernel
#print axioms distinct
#print axioms induced
#print axioms window_directions
#print axioms pair_counts
#print axioms endpoint_distances
end Snake9.EndpointSharp
'''
p=HERE/'lean/WitnessEndpointSharp.lean';p.write_text(source,encoding='utf-8')
BIN=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
build=Path((HERE/'build/latest.txt').read_text().strip());paths=[build]
for prior,tag in [('44-critical-window-generalization','latest'),('41-joint-intervening-sum','latest'),('31-joint-counter-soundness','latest'),('32-seven-count-four-screen','proofs-latest'),('28-direct-share-certificates','latest')]:
    paths.append(Path((ROOT/f'milestones/{prior}/build/{tag}.txt').read_text().strip()))
paths.extend(ROOT/p for p in ['milestones/20-middle-path-release/build','milestones/14-component-construction/build','milestones/07-window-223/lean/generated/geometry/support-ci2y7deg','work/spectral/.verification/strengthened-n8g3mwjy/core/.lake/build/lib/lean','work/spectral/.verification/strengthened-n8g3mwjy'])
env=os.environ.copy();env['PATH']=str(BIN)+';'+env['PATH'];env['LEAN_PATH']=';'.join(map(str,paths))
t=time.monotonic()
with (HERE/'logs/WitnessEndpointSharp.log').open('w',encoding='utf-8') as f:
    result=subprocess.run([str(BIN/'lake.exe'),'env','lean','-R',str(HERE/'lean'),'-o',str(build/'WitnessEndpointSharp.olean'),str(p)],cwd=BIN.parent.parent/'mathlib',env=env,stdout=f,stderr=subprocess.STDOUT)
record=dict(module='WitnessEndpointSharp',exit_code=result.returncode,seconds=round(time.monotonic()-t,3),source_sha256=hashlib.sha256(p.read_bytes()).hexdigest())
(HERE/'logs/witness-build-record.json').write_text(json.dumps(record,indent=2)+'\n')
assert result.returncode==0,(HERE/'logs/WitnessEndpointSharp.log').read_text()
out=dict(edges=n,start=start,pair_counts=[5,3],endpoint_distances=distances,vertex_sequence=vs,source_sha256=hashlib.sha256((HERE/'data/full-first-radius-2-cap-8.json').read_bytes()).hexdigest())
(HERE/'data/witness-endpoint-sharp.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(record));print('Witness',n,'edges; start',start,'distances',distances)
