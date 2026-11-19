using System;
using System.Collections.Generic;
using System.IO;
using System.Runtime.CompilerServices;

// A mask omits the mandatory common root. Bits use the usual Q8 vertex numbers.
struct Mask {
    public ulong A, B, C, D;
    public void Add(int x) {
        ulong bit = 1UL << (x & 63);
        switch (x >> 6) {
            case 0: A |= bit; break;
            case 1: B |= bit; break;
            case 2: C |= bit; break;
            default: D |= bit; break;
        }
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static ulong CountsByByte(ulong word) {
        word -= (word >> 1) & 0x5555555555555555UL;
        word = (word & 0x3333333333333333UL) + ((word >> 2) & 0x3333333333333333UL);
        return (word + (word >> 4)) & 0x0F0F0F0F0F0F0F0FUL;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public int Intersection(ref Mask other) {
        ulong count = CountsByByte(A & other.A) + CountsByByte(B & other.B)
                    + CountsByByte(C & other.C) + CountsByByte(D & other.D);
        // Each byte is at most 32; the full intersection has at most 98 vertices.
        return (int)(unchecked(count * 0x0101010101010101UL) >> 56);
    }
}

class Place {
    const int Permutations = 40320;
    static readonly List<int[]> images = new List<int[]>();
    static readonly byte[] maps = new byte[Permutations * 256];

    static void Generate(int[] image, int depth, int used) {
        if (depth == 8) {
            int start = images.Count * 256;
            images.Add((int[])image.Clone());
            for (int j = 0; j < 8; ++j)
                for (int x = 0; x < (1 << j); ++x)
                    maps[start + (1 << j) + x] = (byte)(maps[start + x] | (1 << image[j]));
            return;
        }
        for (int i = 0; i < 8; ++i)
            if ((used & (1 << i)) == 0) {
                image[depth] = i;
                Generate(image, depth + 1, used | (1 << i));
            }
    }

    static int[] ReadInts(StreamReader input) {
        return Array.ConvertAll(input.ReadLine().Split(' '), int.Parse);
    }

    static void RootedImages(int[] path, int end, Mask[] output) {
        int root = path[end == 0 ? 0 : path.Length - 1];
        for (int i = 0; i < Permutations; ++i) {
            Mask mask = new Mask();
            int offset = i * 256;
            foreach (int v in path)
                if (v != root) mask.Add(maps[offset + (v ^ root)]);
            output[end * Permutations + i] = mask;
        }
    }

    static void Main(string[] args) {
        Generate(new int[8], 0, 0);
        if (images.Count != Permutations) throw new Exception("Incomplete coordinate group");
        using (var input = new StreamReader(args[0]))
        using (var output = new StreamWriter(args[1])) {
            int total = int.Parse(input.ReadLine());
            int[][] paths = new int[total][];
            Mask[,] fixedMasks = new Mask[total, 2];
            for (int id = 0; id < total; ++id) {
                int[] path = ReadInts(input);
                paths[id] = path;
                for (int e = 0; e < 2; ++e) {
                    int root = path[e == 0 ? 0 : path.Length - 1];
                    Mask m = new Mask();
                    foreach (int v in path) if (v != root) m.Add(v ^ root);
                    fixedMasks[id, e] = m;
                }
            }
            int jobs = int.Parse(input.ReadLine());
            int last = -1;
            Mask[] all = new Mask[2 * Permutations];
            for (int j = 0; j < jobs; ++j) {
                int[] pair = ReadInts(input);
                int a = pair[0], b = pair[1];
                if (a != last) {
                    RootedImages(paths[a], 0, all);
                    RootedImages(paths[a], 1, all);
                    last = a;
                }
                int best = 256, hits = 0, bestLong = 0, bestShort = 0, bestPerm = 0;
                for (int shortEnd = 0; shortEnd < 2; ++shortEnd) {
                    Mask fixedMask = fixedMasks[b, shortEnd];
                    for (int p = 0; p < all.Length; ++p) {
                        int n = fixedMask.Intersection(ref all[p]);
                        if (n < best) {
                            best = n;
                            hits = 1;
                            bestLong = p / Permutations;
                            bestShort = shortEnd;
                            bestPerm = p % Permutations;
                        } else if (n == best) {
                            ++hits;
                        }
                    }
                }
                output.WriteLine("{0} {1} {2} {3} {4} {5} {6}",
                    a, b, best, hits, bestLong, bestShort, string.Join("", images[bestPerm]));
            }
            Console.WriteLine("{0} labelled shape pairs, {1} placements per pair", jobs, 4 * Permutations);
        }
    }
}
