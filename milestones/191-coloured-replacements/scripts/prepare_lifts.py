from pathlib import Path
R=Path('E:/Snake-in-a-box');H=R/'milestones/191-coloured-replacements';P=R/'milestones/188-dimensional-constructions'
s=(P/'scripts/two_cross_search.py').read_text()
s=s.replace("H=R/'milestones/188-dimensional-constructions'","H=R/'milestones/191-coloured-replacements'")
s=s[:s.index("if __name__=='__main__':")]
s=s.replace('solver=cp_model.CpSolver();','modelpath=H/\'data\'/(tag+\'.pbtxt\');assert not modelpath.exists();model.export_to_file(str(modelpath))\n    solver=cp_model.CpSolver();')
s=s.replace('random_seed=188','random_seed=191')
s=s.replace("'best_outside_bound':solver.best_objective_bound,","'best_outside_bound':solver.best_objective_bound,'model_sha256':hashlib.sha256(modelpath.read_bytes()).hexdigest(),")
s+='''if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--dimension',type=int,choices=[6,7,8],required=True);ap.add_argument('--target',type=int,default=0);ap.add_argument('--seconds',type=float,default=90);a=ap.parse_args()
    seeds=json.loads((R/'milestones/188-dimensional-constructions/data/lower-dimensional-seeds.json').read_text())
    middle=seeds[str(a.dimension)]['vertices']
    solve(a.dimension,middle,None,a.target,a.seconds,f'optimal-middle-{a.dimension}-target{a.target}')
'''
(H/'scripts/optimal_middle_lifts.py').write_text(s,encoding='utf-8',newline='\n')
(H/'scripts/prepare_lifts.py').write_bytes(Path(__file__).read_bytes())
