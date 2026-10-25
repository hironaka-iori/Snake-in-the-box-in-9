"""Test sharpness of the four-step sum on a complete induced path."""
from pathlib import Path
import importlib.util
from survey import p,HERE,ROOT
spec=importlib.util.spec_from_file_location('fullsearch',ROOT/'milestones/44-critical-window-generalization/scripts/full_cube.py')
# The imported module expects a local module named probe; provide its established interface.
import sys,types
sys.modules['probe']=types.SimpleNamespace(p=p,HERE=HERE)
f=importlib.util.module_from_spec(spec);spec.loader.exec_module(f)
f.search('full-return-five',[0,1,2,0],[1,3],5,seconds=30)
