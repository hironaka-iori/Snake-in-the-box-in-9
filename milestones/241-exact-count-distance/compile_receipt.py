"""Run one compiler at a time under the saved Windows resource limits."""
from datetime import datetime, timezone
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
import ctypes
import json
import os
import re
import shutil
import subprocess
import sys
import time


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PREVIOUS = HERE.parent / "240-five-count-recovery"
sys.path.insert(0, str(PREVIOUS / "scripts"))
from native_resources import PROCESS_MEMORY_COUNTERS_EX, psapi, snapshot
sys.path.insert(0, str(ROOT / "work" / "keep96"))
from worker import memory_limit


def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()


def run(command, cwd, log, deadline):
    gate = snapshot()
    if gate["errors"] or gate["processes"] or gate["free_bytes"] < 1024**3:
        raise RuntimeError(("Startup resource gate", gate))
    start = time.monotonic()
    peak = 0
    reserve = gate["free_bytes"]
    with log.open("wb") as out:
        process = subprocess.Popen(command, cwd=cwd, stdout=out, stderr=subprocess.STDOUT)
        try:
            while True:
                state = snapshot()
                reserve = min(reserve, state["free_bytes"])
                counters = PROCESS_MEMORY_COUNTERS_EX()
                counters.cb = ctypes.sizeof(counters)
                if not psapi.GetProcessMemoryInfo(int(process._handle), ctypes.byref(counters), counters.cb):
                    raise OSError(ctypes.get_last_error())
                peak = max(peak, counters.PeakPagefileUsage)
                if (state["errors"] or any(p["ProcessId"] != process.pid for p in state["processes"])
                        or reserve < 768 * 1024**2 or peak > 256 * 1024**2):
                    raise RuntimeError(("Runtime resource gate", state, peak))
                if process.poll() is not None:
                    break
                if time.monotonic() - start > deadline:
                    raise TimeoutError(deadline)
                time.sleep(0.10)
        finally:
            if process.poll() is None:
                process.kill()
                process.wait()
    if process.returncode:
        raise RuntimeError(log.read_text(encoding="utf-8", errors="replace")[-2400:])
    return dict(seconds=time.monotonic() - start, exit_code=process.returncode,
                startup_free_bytes=gate["free_bytes"], minimum_sampled_free_bytes=reserve,
                peak_private_bytes=peak, log_sha256=digest(log))


def compile_one(name):
    hard_limit = memory_limit(256)  # Child processes inherit the Windows job.
    with TemporaryDirectory(prefix="snake241-") as build:
        folder = Path(build)
        log = folder / "compiler-output.txt"
        passes = []
        if name == "EightCountWitness241":
            source = HERE / "lean" / (name + ".lean")
            previous = json.loads((PREVIOUS / "data" / "EightCubeObstruction240-execution.json").read_bytes())
            compiler = Path(previous["lean_bin"]) / "lean.exe"
            obj = folder / (name + ".olean")
            command = [str(compiler), "-j", "1", "-s", "8192", "-o", str(obj), source.name]
            passes.append(run(command, source.parent, log, 60))
            output = log.read_text(encoding="utf-8")
            if "sorryAx" in output or "error:" in output or "warning:" in output:
                raise ValueError(output)
            reports = re.findall(r"'([^']+)' (?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])", output)
            if len(reports) != source.read_text(encoding="utf-8").count("#print axioms"):
                raise ValueError(output)
            for _, names in reports:
                if not set(re.findall(r"[\w.]+", names)) <= {"propext", "Quot.sound", "Classical.choice"}:
                    raise ValueError(output)
            details = dict(compiler_output=output, object_sha256=digest(obj))
        elif name in {"snake9_research", "snake9_frontier_explanation"}:
            source = Path("D:/Codex/2026-10-13/new-chat/outputs") / (name + ".tex")
            compiler = Path(shutil.which("pdflatex"))
            if digest(source) != digest(ROOT / "paper" / source.name):
                raise ValueError("Authoritative document and repository mirror differ")
            command = [str(compiler), "-no-shell-escape", "-interaction=nonstopmode", "-halt-on-error",
                       "-output-directory=" + str(folder), str(source)]
            for _ in range(4):
                passes.append(run(command, source.parent, log, 180))
                output = (folder / (name + ".log")).read_text(encoding="utf-8", errors="replace")
                if not re.search(r"Rerun to get|rerunfilecheck Warning:|There were undefined references|There were undefined citations", output):
                    break
            else:
                raise ValueError("References did not settle in four passes")
            pdf = folder / (name + ".pdf")
            pages = re.search(r"\((\d+) pages?,\s*[\d,]+ bytes\)", output)
            if not pages:
                raise ValueError(output[-1500:])
            shutil.copyfile(pdf, source.with_suffix(".pdf"))
            details = dict(pages=int(pages[1]), pdf_sha256=digest(pdf),
                           final_typesetter_log_sha256=digest(folder / (name + ".log")),
                           references_settled=True)
        else:
            raise ValueError(name)
        return dict(status="pass", name=name, source_sha256=digest(source), compiler=str(compiler),
                    compiler_sha256=digest(compiler), arguments=command[1:], passes=passes,
                    private_memory_limit=hard_limit, thread_limit=1 if name.endswith("241") else None,
                    finished_utc=datetime.now(timezone.utc).isoformat(), **details)


if __name__ == "__main__":
    name = sys.argv[1]
    receipt = compile_one(name)
    (HERE / (name + "-compile.json")).write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(name, receipt["status"], receipt.get("pages", receipt.get("compiler_output")))
