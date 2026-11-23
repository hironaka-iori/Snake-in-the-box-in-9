from pathlib import Path
import sys
d=Path(__file__).resolve().parent;families=(d/'families.in').read_text().splitlines();y={}
for file in sys.argv[1:]:
 for line in (d/file).read_text().splitlines():
  i,st,ng,n=map(int,line.split());assert not (st==0 and y.get(i)==0);y[i]=st
for i,line in enumerate(families):
 if y.get(i,1)!=0:print(line)
