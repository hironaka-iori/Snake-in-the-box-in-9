"""Emit a portable formula and resolution proof and replay the extracted proof."""
import gzip,shutil,subprocess
from pathlib import Path
from pysat.solvers import pysolvers
from proof_ascii import write_ascii
from rerun_deep_certificate import digest


def checked_export(solver,clauses,prefix,checker):
    cnf=prefix.with_suffix(".cnf");drat=prefix.with_suffix(".drat");core=prefix.with_suffix(".core")
    with cnf.open("w",newline="\n") as f:
        f.write(f"p cnf {max(abs(v) for c in clauses for v in c)} {len(clauses)}\n")
        for c in clauses:f.write(" ".join(map(str,c))+" 0\n")
    backend=solver.solver;pysolvers.flushpr(backend.prfp);backend.prfile.seek(0)
    with drat.open("wb") as f:write_ascii(backend.prfile,f)
    for cmd in ([str(cnf),str(drat),"-l",str(core)],[str(cnf),str(core)]):
        replay=subprocess.run([str(checker),*cmd],capture_output=True)
        assert replay.returncode==0 and b"s VERIFIED" in replay.stdout.splitlines()
    out={"checker":replay.stdout.decode(errors="replace").splitlines()[-10:]}
    for f in (cnf,core):
        out[f.suffix[1:]+"_sha256"]=digest(f)
        with f.open("rb") as src,Path(str(f)+".gz").open("wb") as dest:
            with gzip.GzipFile(fileobj=dest,filename="",mode="wb",mtime=0,compresslevel=5) as gz:
                shutil.copyfileobj(src,gz)
    return out
