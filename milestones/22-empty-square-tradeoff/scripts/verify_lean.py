"""Fresh kernel build of new small theorems from the exact upstream definition prefix.

The unused 191-witness calculation is deliberately not imported. The dependency
named Snake9.lean is a byte-for-byte prefix through structure Snake, followed by
end Snake9. This changes neither Vertex, Adj, nor Snake. No upstream proof cache
is used. This is not a rebuild of upstream 191/238.
"""
import argparse, hashlib, json, os, pathlib, re, subprocess, time
P=pathlib.Path(__file__).resolve().parents[1]; R=P.parents[1]
ap=argparse.ArgumentParser(); ap.add_argument('--lean',required=True); ap.add_argument('--run',required=True)
a=ap.parse_args(); build=P/'.build'/a.run; build.mkdir(parents=True,exist_ok=False)
logs=P/'logs'/a.run; logs.mkdir(parents=True,exist_ok=False)
source=(R/'work/final_lean/Snake9.lean').read_bytes()
marker=b'def takePrefix'
prefix=source[:source.index(marker)]+b'end Snake9\n'
(build/'Snake9.lean').write_bytes(prefix)
(build/'TradeoffChecks.lean').write_bytes((P/'lean/TradeoffChecks.lean').read_bytes())
env=os.environ.copy(); env['LEAN_PATH']=str(build)
sha=lambda b:hashlib.sha256(b).hexdigest()
manifest={'git':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),
          'compiler':subprocess.check_output([a.lean,'--version'],text=True).strip(),
          'upstream_source_sha256':sha(source),'definition_prefix_sha256':sha(prefix),
          'new_source_sha256':sha((build/'TradeoffChecks.lean').read_bytes()),
          'driver_sha256':sha(pathlib.Path(__file__).read_bytes()),
          'dependency_scope':'Exact upstream prefix ending after Snake; no 191/238 rebuild or object reuse',
          'steps':[]}
for module in ['Snake9','TradeoffChecks']:
    t=time.monotonic()
    proc=subprocess.run([a.lean,'-o',module+'.olean',module+'.lean'],cwd=build,env=env,
                        stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=120)
    (logs/(module+'.log')).write_bytes(proc.stdout)
    manifest['steps'].append({'module':module,'exit_code':proc.returncode,'seconds':time.monotonic()-t,
                              'source_sha256':sha((build/(module+'.lean')).read_bytes()),
                              'log_sha256':sha(proc.stdout)})
    if proc.returncode:
        manifest['status']='FAILED'; (logs/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
        print(proc.stdout.decode(errors='replace')); raise SystemExit(proc.returncode)
    if module=='TradeoffChecks':
        text=proc.stdout.decode()
        audits=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",text)
        assert len(audits)==6,(len(audits),text)
        allowed={'propext','Classical.choice','Quot.sound'}
        for name,axioms in audits:
            assert set(x.strip() for x in axioms.split(',') if x.strip())<=allowed
        manifest['axioms']={name:axioms for name,axioms in audits}
manifest['status']='PASS'
(logs/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(manifest,indent=2))
