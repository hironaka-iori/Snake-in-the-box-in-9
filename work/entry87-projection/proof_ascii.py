"""Stream CaDiCaL's packed additions and deletions as plain DRAT."""
def write_ascii(src,dst):
    mode=None
    number=0
    shift=0
    clause=[]
    for block in iter(lambda:src.read(1<<20),b""):
        for byte in block:
            if mode is None:
                if byte not in (97,100):raise ValueError("unexpected proof marker")
                mode=byte
            elif byte==0:
                if shift:raise ValueError("unfinished variable-length number")
                if mode==100:dst.write(b"d ")
                if clause:dst.write(b" ".join(clause)+b" ")
                dst.write(b"0\n")
                clause.clear();mode=None
            else:
                number|=(byte&127)<<shift
                if byte&128:
                    shift+=7
                else:
                    value=-(number>>1) if number&1 else number>>1
                    clause.append(str(value).encode("ascii"))
                    shift=0;number=0
    if mode is not None:raise ValueError("unfinished clause")
