import subprocess,json
bank="q9_odd_reference_vertices.txt"
s=list(map(int,open("q9_face_all_halves.txt").readline().split()))
outside=[v for v in range(512) if v not in s and (v^s[0]).bit_count()%2==0]
def summary(binary,source):
    res=subprocess.run([binary,bank,"100000"],input=source,text=True,capture_output=True,check=True)
    lines=res.stdout.splitlines();assert all(l.startswith(("AT ","DONE ")) for l in lines)
    return list(map(int,lines[-1].split()[1:]))
lines=[" ".join(map(str,s[:i]+[v]+s[i+1:])) for i in range(len(s)) for v in outside]
direct=summary("/tmp/q9oddcheck21","\n".join(lines)+"\n")
fast=summary("/tmp/q9oddex21"," ".join(map(str,s))+"\n")
assert len(lines)==15360 and direct[0]==fast[1]==len(lines) and direct[1:]==fast[3:] and direct[3]==0
print(json.dumps(dict(checked=len(lines),all_orders=direct[1],paths=direct[2],cutoffs=direct[3],new_classes=direct[4])))
