"""Emit complete CSV rows from the first partially downloaded ZIP member."""
import struct, sys, zlib
with open(sys.argv[1], 'rb') as f:
    header=f.read(30)
    assert header[:4]==b'PK\x03\x04' and struct.unpack_from('<H',header,8)[0]==8
    n,m=struct.unpack_from('<HH',header,26)
    assert f.read(n)==b'record_snakes.csv'
    f.read(m)
    decoder=zlib.decompressobj(-15)
    buf=b''
    while chunk:=f.read(65536):
        buf+=decoder.decompress(chunk)
        k=buf.rfind(b'\n')+1
        sys.stdout.buffer.write(buf[:k])
        buf=buf[k:]
        if decoder.eof:break
