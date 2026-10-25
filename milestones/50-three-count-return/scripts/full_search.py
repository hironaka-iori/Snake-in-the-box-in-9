"""Seek a complete induced path attaining the triple sum thirteen."""
from pathlib import Path
import importlib.util,sys,types
from probe import p,HERE,ROOT
sys.modules['probe']=types.SimpleNamespace(p=p,HERE=HERE)
spec=importlib.util.spec_from_file_location('fullsearch',ROOT/'milestones/44-critical-window-generalization/scripts/full_cube.py')
f=importlib.util.module_from_spec(spec);spec.loader.exec_module(f)
f.search('full-triple-thirteen',[0,1,2,3,4,0],[1,4,5],13,seconds=45)
