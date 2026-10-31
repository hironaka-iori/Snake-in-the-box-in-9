import json,random
from pathlib import Path
from cheap_folded import FixedPathObjective
from charge_fast import Geometry,Charges
H=Path(__file__).resolve().parent;repo=H.parents[1]/'branch241-audit/repo';bank=json.loads((repo/'work/bank9.json').read_text());G=Geometry(9);E=FixedPathObjective(G,bank[67]['vertex_sequence'][:11],occupancy_bonus=True);rng=random.Random(235234);checked=attempts=0
while checked<64:
 attempts+=1;S=E.selected|{v for v in E.ball-E.selected-E.forbidden if rng.random()<.06};mask=G.mask(S)
 if any(mask&m==m for m,*_ in G.squares):continue
 actual=Charges(G,S).cheap()['r6plus']['values'];got=E.evaluate(S);assert got=={x:actual[x] for x in E.centres};checked+=1
r={'random_seed':235234,'no_square_random_assignments':checked,'attempts':attempts,'all_9_centre_bonus_scores_exact':True,'scope':'objective semantics only; random sets need not be snakes or satisfy full geometric constraints'};(H/'random_bonus_controls.json').write_text(json.dumps(r,indent=2));print(json.dumps(r,indent=2))
