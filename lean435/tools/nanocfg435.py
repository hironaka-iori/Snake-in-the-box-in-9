#!/usr/bin/env python3
"""nanoda_bin config for an export file: every axiom of the export is listed in permitted_axioms (the
explicit assumptions of the check); also writes <export>.axioms.txt. Usage: nanocfg435.py EXPORT"""
import json,sys,subprocess
exp=sys.argv[1]; N={0:''}; ax=[]
for l in open(exp):
    r=json.loads(l)
    if 'in' in r:
        v=r.get('str') or r.get('num'); p=N[v['pre']]; s=str(v.get('str',v.get('i'))); N[r['in']]=(p+'.'+s) if p else s
    elif 'axiom' in r: ax.append(N[r['axiom']['name']])
json.dump({"export_file_path":exp,"use_stdin":False,"permitted_axioms":sorted(set(ax)),
  "unpermitted_axiom_hard_error":True,"nat_extension":True,"string_extension":True,"print_success_message":True},open(exp+'.nanoda.json','w'),indent=1)
open(exp+'.axioms.txt','w').write('\n'.join(sorted(set(ax)))+'\n')
print(len(set(ax)),'axioms permitted')
