"""Bounded native DRAT-trim audit of three large, already generated proofs.

Setup: python -m pip install --target work/keep96/.native-packages ziglang==0.13.0
Upstream sources are unmodified, pinned at 2e3b2dc0ecf938addbd779d42877b6ed69d9a985.
Windows uses getc instead of getc_unlocked through a compiler definition.
"""
import shutil
import subprocess
import time
from common import *
from worker import memory_limit


def main():
    build=HERE/'.native-build';build.mkdir(exist_ok=True)
    out=OUT/'native-audit';out.mkdir(exist_ok=True)
    compiler=HERE/'.native-packages/ziglang/zig.exe'
    source=HERE/'vendor/drat-trim/drat-trim.c'
    executable=build/'drat-trim.exe'
    command=[str(compiler),'cc',str(source),'-O2','-std=c99','-Dgetc_unlocked=getc','-o',str(executable)]
    with (out/'build.log').open('w') as log:
        subprocess.run(command,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=300)
    metadata=dict(upstream='https://github.com/marijnheule/drat-trim',
        commit='2e3b2dc0ecf938addbd779d42877b6ed69d9a985',source_sha256=sha(source),
        compiler_version=subprocess.check_output([str(compiler),'version'],text=True).strip(),
        compiler_sha256=sha(compiler),binary_sha256=sha(executable),command=command,
        wall_limit_seconds=1800,memory_mib=2048)
    save(out/'build.json',metadata)
    # Child processes inherit the Windows Job Object process-memory limit.
    metadata['memory_policy']=memory_limit(2048)
    controls=[]
    for name,cnf,proof,expected in [
        ('valid','p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n','1 0\n0\n',True),
        ('invalid','p cnf 2 1\n1 2 0\n','0\n',False),
        ('truncated','p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n','',False)]:
        c=out/(name+'.cnf');p=out/(name+'.drup')
        c.write_text(cnf);p.write_text(proof)
        result=subprocess.run([str(executable),str(c),str(p)],capture_output=True,text=True,timeout=30)
        (out/(name+'.log')).write_text(result.stdout+result.stderr)
        passed=result.returncode==0 and 's VERIFIED' in result.stdout
        if passed!=expected:raise ValueError('native checker control failed: '+name)
        controls.append(dict(name=name,returncode=result.returncode,verified=passed,expected=expected))
    save(out/'controls.json',controls)
    rows={r['entry']:r for r in json.loads((OUT/'results.json').read_text())['entries']}
    records=[]
    for entry in (258,133,256):
        row=rows[entry]
        for path,key in [(row['formula'],'cnf_gzip_sha256'),(row['certificate'],'certificate_sha256')]:
            if sha(ROOT/path)!=row[key]:raise ValueError('input hash changed')
        cnf=build/f'entry{entry}.cnf';proof=build/f'entry{entry}.drup'
        for source_path,destination in [(ROOT/row['formula'],cnf),(ROOT/row['certificate'],proof)]:
            with gzip.open(source_path,'rb') as src,destination.open('wb') as dst:shutil.copyfileobj(src,dst)
        logpath=out/f'entry{entry}.log'
        cmd=[str(executable),str(cnf),str(proof),'-t','1800']
        print(f'{entry}: native check starting',flush=True);start=time.perf_counter()
        with logpath.open('w') as log:
            try:
                process=subprocess.run(cmd,stdout=log,stderr=subprocess.STDOUT,timeout=1800)
                returncode=process.returncode
            except subprocess.TimeoutExpired:returncode=None
        content=logpath.read_text()
        status='PASSED_NATIVE_DRAT_CHECK' if returncode==0 and 's VERIFIED' in content else ('UNKNOWN_TIMEOUT' if returncode is None else 'CHECK_FAILED_OR_MEMORY_LIMIT')
        record=dict(entry=entry,status=status,returncode=returncode,seconds=time.perf_counter()-start,
            formula_sha256=row['cnf_gzip_sha256'],certificate_sha256=row['certificate_sha256'],
            uncompressed_cnf_sha256=sha(cnf),uncompressed_proof_sha256=sha(proof),
            log=logpath.relative_to(ROOT).as_posix(),log_sha256=sha(logpath),command=cmd)
        records.append(record)
        save(out/'results.json',dict(build=metadata,entries=records,scope='Native DRAT-trim certificate verification, not Lean'))
        print(json.dumps(record),flush=True)


if __name__=='__main__':main()
