"""Export the saved full-window proof only; no solver or Lean invocation."""
import sys
sys.dont_write_bytecode=True
from export_short import run
if __name__=='__main__': run('base')
