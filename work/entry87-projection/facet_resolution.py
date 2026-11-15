"""Reconstruct a fixed-face formula and match it to its independently checked proof."""
import gzip
import hashlib
import json
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

from dense_eight import components, facet_formula


def verify_resolution(file, vertices, size, maximum_components, checker=None):
    record = json.loads(file.read_bytes())
    assert record["status"] == "UNSAT" and record["fixed"] == vertices
    assert record["size"] == size and record["component_limit"] >= maximum_components
    assert "s VERIFIED" in record["checker"]
    clauses, _, select, _ = facet_formula(vertices, size, record["component_limit"],
                                          record.get("deficit_encoding", False))
    for cycle in record["cycles"]:
        sites = set(cycle)
        assert len(sites) == len(cycle) and (sites & set(range(128))) <= set(vertices)
        part, = components(sites, 8)
        assert part[0] == len(sites)
        upper = [v ^ 128 for v in cycle if v >= 128]
        assert upper
        clauses.append([-select[v] for v in upper])
    lines = [f"p cnf {max(abs(v) for clause in clauses for v in clause)} {len(clauses)}"]
    lines.extend(" ".join(map(str, clause))+" 0" for clause in clauses)
    rebuilt = ("\n".join(lines)+"\n").encode()
    assert hashlib.sha256(rebuilt).hexdigest() == record["cnf_sha256"]
    prefix = file.with_suffix("").name+"-proof"
    raw = gzip.decompress(Path(prefix+".core.gz").read_bytes())
    assert hashlib.sha256(raw).hexdigest() == record["core_sha256"]
    if checker:
        with TemporaryDirectory() as tmp:
            cnf, core = Path(tmp)/"cube.cnf", Path(tmp)/"proof.drat"
            cnf.write_bytes(rebuilt)
            core.write_bytes(raw)
            result = subprocess.run([str(checker),str(cnf),str(core)],capture_output=True,check=True)
            assert b"s VERIFIED" in result.stdout.splitlines()
    return record
