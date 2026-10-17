"""Development bridge check against a source-matched foundation cache.

This is deliberately not the final fresh-source rebuild. The latter must be
performed by verify_strengthened.py after the complete exclusion is proved.
"""
import argparse,hashlib,json,os,pathlib,re,subprocess,time
ROOT=pathlib.Path(__file__).resolve().parents[2]
OUT=ROOT/'outputs/window244';CACHE=OUT/'cache';LOG=OUT/'logs'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--foundation-cache',type=pathlib.Path,required=True)
    parser.add_argument('--mathlib-dir',type=pathlib.Path,required=True)
    parser.add_argument('--lake',type=pathlib.Path,required=True)
    args=parser.parse_args()
    for p in [OUT,CACHE,LOG]:p.mkdir(exist_ok=True)
    foundation=args.foundation_cache.resolve();mathlib=args.mathlib_dir.resolve()
    assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=mathlib,text=True).strip()=='c44e0c8ee63ca166450922a373c7409c5d26b00b'
    source_dirs=[ROOT/'work/window244',ROOT/'work/final_lean',ROOT/'work/spectral',ROOT/'work/spectral/stronger',ROOT/'work/lean112']
    order=['BallClauseLogic','WindowGeometry','WindowCounters','WindowAlpha','DfsCertificate','DfsPrefix','WindowReversal','WindowClauses','WindowPermutation','CoordinateExtension','WindowNormalization']
    previous=json.loads((OUT/'bridge-build.json').read_text()) if (OUT/'bridge-build.json').exists() else {}
    record=dict(status='RUNNING',scope='DEVELOPMENT_CACHE_MATCHED; not final fresh rebuild',foundation={},modules={})
    def source(name):return next(d/(name+'.lean') for d in source_dirs if (d/(name+'.lean')).exists())
    seen=set()
    def verify_imports(name):
        if name in seen:return
        seen.add(name);src=source(name)
        if name=='LocalRup':
            check=json.loads((OUT/'certificate-build.json').read_text())['modules'][name]
            assert check['exit_code']==0 and check['identity']['source_sha256']==sha(src)
            assert check['olean_sha256']==sha(CACHE/(name+'.olean'))
            record['foundation'][name]=dict(source_sha256=sha(src),object_sha256=sha(CACHE/(name+'.olean')))
        elif name not in order:
            cached=next(p for p in [foundation/(name+'.lean'),foundation/'core'/(name+'.lean')] if p.exists())
            obj=next(p for p in [foundation/(name+'.olean'),foundation/'core/.lake/build/lib/lean'/(name+'.olean')] if p.exists())
            # Python universal-newline reading permits CRLF/LF only, not proof edits.
            assert cached.read_text(encoding='utf-8')==src.read_text(encoding='utf-8'),f'Foundation source differs beyond line endings: {name}'
            record['foundation'][name]=dict(source_sha256=sha(src),cached_source_sha256=sha(cached),line_endings_only=sha(src)!=sha(cached),object_sha256=sha(obj))
        for line in src.read_text(encoding='utf-8').splitlines():
            if line.startswith('import '):
                for dep in line.split()[1:]:
                    if not dep.startswith(('Mathlib','Std','Lean','Init')):verify_imports(dep)
    for name in order:verify_imports(name)
    env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join(map(str,[CACHE,foundation,foundation/'core/.lake/build/lib/lean']))
    manifest=OUT/'bridge-build.json'
    def save():manifest.write_text(json.dumps(record,indent=2)+'\n')
    save()
    for name in order:
        src=source(name);obj=CACHE/(name+'.olean');log=LOG/(name+'.log');start=time.monotonic()
        deps={}
        for line in src.read_text(encoding='utf-8').splitlines():
            if line.startswith('import '):
                for dep in line.split()[1:]:
                    if dep.startswith(('Mathlib','Std','Lean','Init')):continue
                    path=next(p for p in [CACHE/(dep+'.olean'),foundation/(dep+'.olean'),foundation/'core/.lake/build/lib/lean'/(dep+'.olean')] if p.exists())
                    deps[dep]=sha(path)
        prior=previous.get('modules',{}).get(name,{})
        if prior.get('exit_code')==0 and prior.get('source_sha256')==sha(src) and prior.get('imports')==deps and obj.exists() and log.exists() and prior.get('olean_sha256')==sha(obj) and prior.get('log_sha256')==sha(log):
            record['modules'][name]=prior;save();continue
        result=subprocess.run([str(args.lake.resolve()),'-d',str(mathlib),'env','lean','--root='+str(src.parent),'-o',str(obj),str(src)],cwd=ROOT,env=env,capture_output=True,text=True,encoding='utf-8')
        output=result.stdout+result.stderr;log.write_text(output,encoding='utf-8')
        audits={n: [x.strip() for x in raw.split(',') if x.strip()] for n,raw in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",output)}
        item=dict(source_sha256=sha(src),imports=deps,exit_code=result.returncode,seconds=time.monotonic()-start,log_sha256=sha(log),axioms=audits)
        if not result.returncode:item['olean_sha256']=sha(obj)
        record['modules'][name]=item;save();print(name,result.returncode,flush=True)
        if result.returncode or not audits or any(set(a)-{'propext','Classical.choice','Quot.sound'} for a in audits.values()):
            record['status']='FAILED';save();raise SystemExit(output)
    record['status']='PASSED_DEVELOPMENT_ONLY';save()

if __name__=='__main__':main()
