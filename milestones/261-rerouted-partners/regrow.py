"""Reroute compatible partners at the previously unresolved 96-edge parents."""
from pathlib import Path
from tempfile import TemporaryDirectory
import json
import subprocess
import sys

HERE=Path(__file__).resolve().parent
MS=HERE.parent
sys.path.insert(0,str(MS/"260-donor-intersections"))
from census import load,save,digest,bank
sys.path.insert(0,str(MS/"255-parity-exchange-arms"))
import construct255 as growth

if __name__=="__main__":
    targets=load(MS/"260-donor-intersections/minimum.json")["rows"]
    source=MS/"257-three-exchange-parents/constructed-51.json"
    old=load(source)["cases"]
    destination=HERE/"growth.json"
    data=load(destination) if destination.exists() else dict(cases={},inputs={
        f.name:digest(f) for f in [source,Path(__file__),growth.SOURCE,Path(growth.__file__),MS/"260-donor-intersections/minimum.json"]})
    with TemporaryDirectory() as d:
        exe=Path(d)/"grow.exe"
        subprocess.run([str(growth.COMPILER),"/nologo","/optimize+","/out:"+str(exe),str(growth.SOURCE)],
                        check=True,capture_output=True)
        # Work first on parents whose closest 95-edge donors collided least.
        for index,(key,row) in enumerate(sorted(targets.items(),key=lambda item:(item[1]["minimum"],item[0]))):
            if key in data["cases"]: continue
            parent=row["parent"]
            start=old[key]["partner"]
            record=growth.grow(exe,parent,start,261000+index)
            path=record["partner"]
            record.update(growth.check_join(parent,path))
            record.update(rooted_parent=parent,previous_join=old[key]["joined_edges"])
            data["cases"][key]=record
            save(destination,data)
            print(key[:8],key[-1],record["previous_join"],record["joined_edges"],flush=True)
            if record["joined_edges"]>=192: break
