"""Obtain additional candidate Q7 parents as seven-coordinate 49-edge intervals of saved snakes."""
from collections import defaultdict
from hashlib import sha256
import gzip,json,sys
from parents import HERE,R270,read,write,wordof,ordered
MS=HERE.parent
sys.path.insert(0,str(MS/"265-joint-arm-regrowth"))
from exchange import input_paths

def recover():
    result=defaultdict(list)
    def collect(w,label):
        for i in range(len(w)-48):
            seg=w[i:i+49]
            if len(set(seg))==7:
                key=min(ordered(seg),ordered(seg[::-1])).hex()
                result[key].append([label,i])
    for label,p in input_paths():
        collect(wordof(p),label)
    archive=gzip.decompress((MS/"267-fixed-arm-extensions/donor-paths.json.gz").read_bytes())
    for i,(w,_) in enumerate(json.loads(archive)):
        collect(bytes.fromhex(w),"R267-"+str(i))
    for w in read(R270/"q8-primer-arms.json"):
        collect(bytes.fromhex(w),"R270-"+w)
    write(HERE/"project-intervals.json",dict(parents=sorted(result),occurrences=result))
    print("Archive Q7 shapes",len(result), "occurrences",sum(map(len,result.values())))

if __name__=="__main__":recover()
