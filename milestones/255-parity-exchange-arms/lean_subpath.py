"""Compile the consecutive-window extension theorem and its length consequence."""
import json
import os
from pathlib import Path
import re
import shutil
import sys
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "242-seed-trade-construction"))
from guarded import compile_receipt, memory_limit, wait_for_gate


def main():
    archive = HERE.parent / "249-long-parent-joins" / "Hinge249-compile.json"
    evidence = json.loads(archive.read_bytes())
    compiler = Path(evidence["compiler"])
    base = HERE.parent / "188-dimensional-constructions" / "lean" / "LayerJoining.lean"
    digest = compile_receipt.digest
    if digest(compiler) != evidence["compiler_sha256"] or digest(base) != evidence["modules"][0]["source_sha256"]:
        raise ValueError("Joining source or compiler differs from the archived build")
    declarations = {
        base: ["join", "compatibility_necessary", "lengths_for_196", "lengths_for_197", "single_crossing_upper"],
        HERE / "Subpath255.lean": ["window", "one_edge_extension", "unextendible_occurrence"],
    }
    limit = memory_limit(256)
    results = []
    with TemporaryDirectory(prefix="snake-subpath255-") as temporary:
        folder = Path(temporary)
        os.environ["LEAN_PATH"] = temporary
        for src, names in declarations.items():
            shutil.copyfile(src, folder / src.name)
            obj = src.with_suffix(".olean").name
            args = ["-j", "1", "-s", "8192", "-o", obj, src.name]
            log = folder / (src.stem + ".log")
            execution = wait_for_gate([str(compiler), *args], folder, log, 60)
            output = log.read_text(encoding="utf-8")
            reports = re.findall(r"'([\w.]+)' (?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])", output)
            if ([name for name, _ in reports] != [src.stem + "." + name for name in names] or
                    any(s in output for s in ("error:", "sorryAx", "warning:")) or
                    any(set(re.findall(r"[\w.]+", axes)) - {"propext", "Quot.sound", "Classical.choice"}
                        for _, axes in reports)):
                raise ValueError(output)
            results.append(dict(module=src.stem, source_sha256=digest(src), object_sha256=digest(folder / obj),
                                arguments=args, execution=execution, compiler_output=output))
    result = dict(status="pass", compiler=str(compiler), compiler_sha256=digest(compiler),
                  thread_limit=1, private_memory_limit=limit, deadline_seconds_per_module=60, modules=results)
    (HERE / "Subpath255-compile.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
    print("Compiled LayerJoining and Subpath255")


if __name__ == "__main__":
    main()
