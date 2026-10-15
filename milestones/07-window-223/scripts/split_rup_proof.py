"""Split and sequentially check an exported RUP proof with bounded parser memory.

Generated files are untrusted. Success requires Lean to compile every module
and the final theorem audit to use only the standard logical foundations.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

parser = argparse.ArgumentParser()
parser.add_argument('--source', type=Path, required=True)
parser.add_argument('--core', type=Path, required=True)
parser.add_argument('--output-dir', type=Path, required=True)
parser.add_argument('--chunk-size', type=int, default=40)
parser.add_argument('--check', action='store_true')
args = parser.parse_args()
assert args.chunk_size > 0
source = args.source.read_text(encoding='utf-8')
namespace = re.search(r'^namespace (\w+)$', source, re.M)[1]
input_count = len(json.loads(args.core.read_text(encoding='utf-8'))['clauses'])
starts = list(re.finditer(r'^private theorem step(\d+)\b', source, re.M))
first = next(i for i,m in enumerate(starts) if int(m[1]) > input_count)
final_start = source.index('theorem constraints_unsat ')
base = source[:starts[first].start()].replace('private theorem ', 'theorem ')
base_name = namespace+'Inputs'
modules = [(base_name, base+'end '+namespace+'\n')]
steps = []
for index in range(first, len(starts)):
    end = starts[index+1].start() if index+1<len(starts) else final_start
    steps.append(source[starts[index].start():end].replace('private theorem ', 'theorem '))
previous = base_name
for start in range(0,len(steps),args.chunk_size):
    name = namespace+f'Part{start//args.chunk_size:04d}'
    code = f'import {previous}\nnamespace {namespace}\nset_option maxHeartbeats 0\nset_option maxRecDepth 1000000\n'
    code += ''.join(steps[start:start+args.chunk_size])+'end '+namespace+'\n'
    modules.append((name,code))
    previous = name
modules.append((namespace, f'import {previous}\nnamespace {namespace}\n'+source[final_start:]))
output = args.output_dir.resolve()
output.mkdir(parents=True,exist_ok=True)
for name,code in modules:
    (output/(name+'.lean')).write_text(code,encoding='utf-8',newline='\n')
manifest = {'status':'generated','source_sha256':hashlib.sha256(args.source.read_bytes()).hexdigest(),
            'core_sha256':hashlib.sha256(args.core.read_bytes()).hexdigest(),
            'chunk_size':args.chunk_size,'modules':len(modules),'checked':[],
            'scope':'Explicit Boolean clauses only; no geometric interpretation is asserted.'}
manifest_path = output/'manifest.json'
def save():manifest_path.write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8')
save()
print(f'{namespace}: {len(modules)} modules, {len(steps)} derived clauses',flush=True)
if args.check:
    lean = shutil.which('lean')
    assert lean, 'Lean 4.19.0 must be on PATH'
    version = subprocess.check_output([lean,'--version'],text=True).strip()
    assert 'version 4.19.0' in version,version
    manifest.update(status='running',lean_version=version,started_utc=datetime.now(timezone.utc).isoformat())
    env=os.environ.copy();env['LEAN_PATH']=str(output)
    for number,(name,code) in enumerate(modules,1):
        print(f'Checking {number}/{len(modules)}: {name}',flush=True)
        result=subprocess.run([lean,'--root='+str(output),'-o',str(output/(name+'.olean')),str(output/(name+'.lean'))],cwd=output,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,encoding='utf-8',errors='replace')
        (output/(name+'.log')).write_text(result.stdout,encoding='utf-8')
        manifest['checked'].append({'module':name,'sha256':hashlib.sha256(code.encode()).hexdigest(),'exit_code':result.returncode})
        save()
        if result.returncode or 'sorryAx' in result.stdout or "declaration uses 'sorry'" in result.stdout:
            manifest['status']='failed';save();raise SystemExit(result.stdout or f'{name} failed')
    audits=re.findall(r"depends on axioms: \[([^\]]*)\]",result.stdout)
    assert len(audits)==1 and {a.strip() for a in audits[0].split(',')} <= {'propext','Classical.choice','Quot.sound'},result.stdout
    manifest.update(status='success',axioms=audits[0].split(', '),completed_utc=datetime.now(timezone.utc).isoformat())
    save();print(result.stdout,flush=True)
