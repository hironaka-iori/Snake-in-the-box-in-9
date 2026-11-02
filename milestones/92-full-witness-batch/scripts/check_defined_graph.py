"""Check the conditional defined-graph bridge in one reserved compiler slot."""
from pathlib import Path
import hashlib,json,os,re,subprocess,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
P87=HERE.parent/'87-retained-array-membership'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p:json.loads(p.read_text())
dependencies=[(HERE,'ContextAssignment'),(P87,'ArrayAssembly')]
def pins():
    out={}
    for base,name in dependencies:
        rp=base/'data'/(name+'-audit.json');r=read(rp)
        assert r['exit_code']==0 and r['status'].startswith('PASS_')
        for folder,ext,key in [('lean','.lean','source_sha256'),('build','.olean','olean_sha256'),('logs','.log','log_sha256')]:
            assert sha(base/folder/(name+ext))==r[key],(name,key)
        out[rp.relative_to(ROOT).as_posix()]=sha(rp)
    rp=P87/'data/enumeration-audit.json';r=read(rp)
    assert r['exit_code']==0 and r['status']=='PASS_RETAINED_ENUMERATION'
    assert sha(P87/'lean/RetainedEnumeration.lean')==r['source_sha256']
    assert sha(P87/'build/RetainedEnumeration.olean')==r['object_sha256']
    assert sha(P87/'logs/RetainedEnumeration.log')==r['log_sha256']
    out[rp.relative_to(ROOT).as_posix()]=sha(rp)
    return out
deps=pins();paths=read(HERE/'data/ContextAssignment-audit.json')['paths']
assert str(P87/'build') in paths
BIN=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
env=os.environ.copy();env['PATH']=str(BIN)+';'+env['PATH'];env['LEAN_PATH']=';'.join(paths)
name='DefinedProofGraph';src=HERE/'lean'/(name+'.lean');obj=HERE/'build'/(name+'.olean')
log=HERE/'logs'/(name+'.log');fresh=obj.with_name(name+'.check-'+str(time.time_ns())+'.olean')
assert not log.exists() and not fresh.exists(),'Preserve prior attempts before retry'
before=sha(src);start=time.monotonic();timeout=False
with log.open('w',encoding='utf-8') as out:
    proc=subprocess.Popen([str(BIN/'lake.exe'),'env','lean','-s','65536','-R',str(HERE/'lean'),'-o',str(fresh),str(src)],
                          cwd=BIN.parent.parent/'mathlib',env=env,stdout=out,stderr=subprocess.STDOUT)
    try:code=proc.wait(timeout=300)
    except subprocess.TimeoutExpired:
        timeout=True
        subprocess.run(['taskkill','/PID',str(proc.pid),'/T','/F'],stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL,check=False)
        code=proc.wait(timeout=30)
r=dict(module=name,exit_code=code,seconds=time.monotonic()-start,timeout=timeout,source_sha256=before,
       log_sha256=sha(log),dependencies=deps,paths=paths,checker_sha256=sha(Path(__file__)))
(HERE/'logs'/(name+'-record.json')).write_text(json.dumps(r,indent=2)+'\n')
assert not timeout and code==0,log.read_text()[-16000:]
assert sha(src)==before and pins()==deps
output=log.read_text();assert 'error:' not in output and 'sorryAx' not in output
assert not re.search(r'\b(sorry|admit|native_decide)\b',src.read_text())
matches=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",output,re.S)
matches += [(n,'') for n in re.findall(r"'([^']+)' does not depend on any axioms",output)]
assert len(matches)==3==src.read_text().count('#print axioms')
audits=[]
for theorem,values in matches:
    axioms=re.findall(r'[A-Za-z][\w.]*',values);assert set(axioms)<={'propext','Classical.choice','Quot.sound'}
    audits.append(dict(theorem=theorem,axioms=axioms))
os.replace(fresh,obj)
r.update(status='PASS_CONDITIONAL_DEFINED_GRAPH',olean_sha256=sha(obj),theorem_audits=audits,
         scope='Defined graph coverage, endpoint identities and actual walk under explicit family, assignment and reference premises. No external-array identity or weight/potential transfer is asserted.')
(HERE/'data'/(name+'-audit.json')).write_text(json.dumps(r,indent=2)+'\n')
print(name,r['status'],round(r['seconds'],3),'seconds;3 audits')
