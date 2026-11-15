"""Specialize the two-region solver to the independently prepared 44-edge inputs."""
from pathlib import Path
H=Path(__file__).resolve().parents[1]
s=(H/'scripts/joint_regions.py').read_text(encoding='utf-8')
s=s.replace("H/'data/regions.json'","H/'data/regions44.json'")
s=s.replace('Two33-edge replacements','Two44-edge replacements')
s=s.replace('Mutual cross-contact pruning is conditional on the native round193 short-move closure.','No mutualcontact restriction or short-move closure premise.')
s=s.replace("model=cp_model.CpModel();variables=[];crosses=[];conflict_count=0","model=cp_model.CpModel();variables=[];crosses=[];all_cross_edges=[];conflict_count=0")
s=s.replace('model.add(sum(x.values())==34)',"model.add(sum(x.values())==part['target_vertices'])")
s=s.replace("model.add(sum(x[z] for z in values if z.bit_count()%2==0)==17)","model.add(sum(x[z] for z in values if z.bit_count()%2==0)==part['required_even'])")
s=s.replace("        model.add(sum(x[z] for z in part['contact_candidates'])>=1)\n",'')
s=s.replace("model.add(sum(edges)==part['crossings']);crosses.append(len(edges))","all_cross_edges.extend(edges);crosses.append(len(edges))")
s=s.replace('    for u in variables[0]:',"    model.add(sum(all_cross_edges)==row['replacement_crossings'])\n    for u in variables[0]:")
p=H/'scripts/joint_regions44.py';assert not p.exists();p.write_text(s,encoding='utf-8')
s=(H/'scripts/run_regions.py').read_text(encoding='utf-8').replace('scripts/joint_regions.py','scripts/joint_regions44.py').replace("H/'data/regions.json'","H/'data/regions44.json'")
(H/'scripts/run_regions44.py').write_text(s,encoding='utf-8')
print('PREPARED_EXPANDED_SOLVER')
