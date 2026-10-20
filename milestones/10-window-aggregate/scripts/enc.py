"""Encoders matching WindowAutomatonLit.lean (ofB64, ofGaps)."""
import numpy as np
B64 = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/'
_B64A = np.frombuffer(B64.encode(), np.uint8)


def b64_of_bytes(b):
    """ofB64 text of the little-endian bytes `b` (padded with zero bytes to a multiple of 6)."""
    a = np.frombuffer(bytes(b), np.uint8)
    pad = (-len(a)) % 6
    if pad:
        a = np.concatenate([a, np.zeros(pad, np.uint8)])
    w = a.reshape(-1, 6).astype(np.uint64)
    v = np.zeros(len(w), np.uint64)
    for j in range(6):
        v |= w[:, j] << np.uint64(8 * j)
    out = np.empty((len(w), 8), np.uint8)
    for j in range(8):
        out[:, j] = _B64A[((v >> np.uint64(6 * j)) & np.uint64(63)).astype(np.int64)]
    return out.tobytes().decode()


def b64_of_int(x, nbytes=None):
    nbytes = nbytes if nbytes is not None else (x.bit_length() + 7) // 8
    return b64_of_bytes(x.to_bytes(nbytes, 'little'))


def int_of_b64(s):
    a = np.frombuffer(s.encode(), np.uint8)
    lut = np.zeros(256, np.uint64); lut[_B64A] = np.arange(64, dtype=np.uint64)
    v = lut[a].reshape(-1, 8)
    w = np.zeros(len(v), np.uint64)
    for j in range(8):
        w |= v[:, j] << np.uint64(6 * j)
    by = np.zeros((len(w), 6), np.uint8)
    for j in range(6):
        by[:, j] = ((w >> np.uint64(8 * j)) & np.uint64(255)).astype(np.uint8)
    return int.from_bytes(by.tobytes(), 'little')


def gaps_of_positions(pos):
    """ofGaps text of sorted bit positions."""
    out = []
    last = None
    for p in pos:
        g = int(p) if last is None else int(p) - last - 1
        assert g >= 0
        last = int(p)
        while True:
            c = g & 31; g >>= 5
            if g:
                out.append(B64[c | 32])
            else:
                out.append(B64[c]); break
    return ''.join(out)


def int_of_gaps(s):
    x = 0; cur = 0; sh = 0; last = None
    for ch in s:
        v = B64.index(ch)
        cur |= (v & 31) << sh
        if v < 32:
            p = cur if last is None else last + cur + 1
            x |= 1 << p; last = p; cur = 0; sh = 0
        else:
            sh += 5
    return x


def gaps_of_int(x):
    """positions of the set bits of a Python int (via bytes)."""
    if x == 0:
        return ''
    b = np.frombuffer(x.to_bytes((x.bit_length() + 7) // 8, 'little'), np.uint8)
    bits = np.unpackbits(b, bitorder='little')
    return gaps_of_positions(np.flatnonzero(bits))


if __name__ == '__main__':
    import random
    for _ in range(20):
        x = random.getrandbits(random.randrange(1, 5000))
        assert int_of_b64(b64_of_int(x)) == x
        assert int_of_gaps(gaps_of_int(x)) == x
    print('ok')
