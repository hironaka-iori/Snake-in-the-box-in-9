"""Check the spectral proof using an existing pinned mathlib checkout and Lean 4.19.0."""
import argparse, os, shutil, subprocess, tempfile
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument("--mathlib-dir", required=True, type=Path)
args = parser.parse_args()
mathlib = args.mathlib_dir.resolve()
expected = "c44e0c8ee63ca166450922a373c7409c5d26b00b"
actual = subprocess.check_output(["git", "rev-parse", "HEAD"],cwd=mathlib,text=True).strip()
if actual != expected:
    raise SystemExit(f"Expected mathlib {expected}; found {actual}")
project = Path(__file__).resolve().parent
build_parent = project / ".verification"
build_parent.mkdir(exist_ok=True)
build = Path(tempfile.mkdtemp(prefix="run-",dir=build_parent)).resolve()
assert build.is_relative_to(build_parent.resolve())
(build / "Archive").mkdir()
shutil.copy2(mathlib/"Archive/Sensitivity.lean",build/"Archive/Sensitivity.lean")
shutil.copy2(project.parent/"final_lean/Snake9.lean",build/"Snake9.lean")
shutil.copy2(project/"SpectralUpperBound.lean",build/"SpectralUpperBound.lean")
env = os.environ.copy()
env["LEAN_PATH"] = str(build) + os.pathsep + env.get("LEAN_PATH", "")
version = subprocess.check_output(["lake", "env", "lean", "--version"],cwd=mathlib,env=env,text=True)
if "version 4.19.0" not in version:
    raise SystemExit("Expected Lean 4.19.0: " + version)
for name in ["Archive/Sensitivity", "Snake9", "SpectralUpperBound"]:
    subprocess.run(["lake","env","lean",f"--root={build}","-o",str(build/(name+".olean")),
                    str(build/(name+".lean"))],cwd=mathlib,env=env,check=True)
print("Spectral proof checked against pinned mathlib. Build files: " + str(build))
