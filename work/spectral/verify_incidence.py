"""Rebuild the core and check the square-incidence bound with pinned mathlib."""
import argparse, os, shutil, subprocess, tempfile
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument("--mathlib-dir", required=True, type=Path)
parser.add_argument("--module", choices=["SquareIncidence","LowSingletonArms"],default="SquareIncidence")
parser.add_argument("--fresh-core", action="store_true", help="Rebuild a source-only core copy")
args = parser.parse_args()
mathlib = args.mathlib_dir.resolve()
expected = "c44e0c8ee63ca166450922a373c7409c5d26b00b"
actual = subprocess.check_output(["git", "rev-parse", "HEAD"],cwd=mathlib,text=True).strip()
if actual != expected:
    raise SystemExit(f"Expected mathlib {expected}; found {actual}")
project = Path(__file__).resolve().parent
build_parent = project / ".verification"
build_parent.mkdir(exist_ok=True)
build = Path(tempfile.mkdtemp(prefix="square-",dir=build_parent)).resolve()
assert build.is_relative_to(build_parent.resolve())
core = project.parent / "final_lean"
if args.fresh_core:
    source = core
    core = build / "core"
    core.mkdir()
    for file in [*source.glob("*.lean"),source/"lakefile.toml",source/"lean-toolchain",source/"lake-manifest.json"]:
        shutil.copy2(file,core/file.name)
subprocess.run(["lake","build"],cwd=core,check=True)
shutil.copy2(project/(args.module+".lean"),build/(args.module+".lean"))
env = os.environ.copy()
env["LEAN_PATH"] = str(core/".lake/build/lib/lean") + os.pathsep + str(build) + os.pathsep + env.get("LEAN_PATH", "")
version = subprocess.check_output(["lake", "env", "lean", "--version"],cwd=mathlib,env=env,text=True)
if "version 4.19.0" not in version:
    raise SystemExit("Expected Lean 4.19.0: " + version)
subprocess.run(["lake","env","lean",f"--root={build}","-o",str(build/(args.module+".olean")),
                str(build/(args.module+".lean"))],cwd=mathlib,env=env,check=True)
print("Square-incidence proof checked: every Q9 snake has at most 254 edges." if args.module=="SquareIncidence"
      else "Low-singleton arm restriction checked under its explicit geometric premises.")
