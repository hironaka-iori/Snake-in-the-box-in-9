"""Resource-limited subprocess launcher. Timeout is exit 124, never success."""
import subprocess,sys
from limits import memory_limit
memory_limit(int(sys.argv[1]))
try:
    p=subprocess.run(sys.argv[3:],timeout=float(sys.argv[2]))
    raise SystemExit(p.returncode)
except subprocess.TimeoutExpired:raise SystemExit(124)
