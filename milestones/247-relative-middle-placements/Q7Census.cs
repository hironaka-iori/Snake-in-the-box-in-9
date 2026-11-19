using System;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Runtime.CompilerServices;

// Bits 0..63 and 64..127 retain their original Q7 labels.
struct Sites {
    public ulong Lo, Hi;
    public Sites(ulong lo, ulong hi) { Lo=lo; Hi=hi; }
    public bool Has(int v) { return (((v<64 ? Lo : Hi) >> (v & 63)) & 1UL) != 0; }
    public void Add(int v) {
        if (v<64) Lo |= 1UL << v; else Hi |= 1UL << (v-64);
    }
    public void Remove(int v) {
        if (v<64) Lo &= ~(1UL << v); else Hi &= ~(1UL << (v-64));
    }
}

class Q7Census {
    static readonly Sites[] N = new Sites[128];
    static readonly bool[] Even = new bool[128];
    static readonly int[] Path = new int[48];
    static Sites allowed, evenSites;
    static int[] packOrder;
    static StreamWriter paths;
    static long nodes, limit, count47, count48, parityCuts, reachCuts, starCuts;
    static int seconds;
    static string status = "complete";
    static Stopwatch clock;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static int Pop(ulong z) {
        z -= (z >> 1) & 0x5555555555555555UL;
        z = (z & 0x3333333333333333UL) + ((z >> 2) & 0x3333333333333333UL);
        z = (z + (z >> 4)) & 0x0f0f0f0f0f0f0f0fUL;
        return (int)(unchecked(z * 0x0101010101010101UL) >> 56);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static ulong WithinHalf(ulong x) {
        return ((x & 0x5555555555555555UL)<<1) | ((x>>1)&0x5555555555555555UL)
             | ((x & 0x3333333333333333UL)<<2) | ((x>>2)&0x3333333333333333UL)
             | ((x & 0x0f0f0f0f0f0f0f0fUL)<<4) | ((x>>4)&0x0f0f0f0f0f0f0f0fUL)
             | ((x & 0x00ff00ff00ff00ffUL)<<8) | ((x>>8)&0x00ff00ff00ff00ffUL)
             | ((x & 0x0000ffff0000ffffUL)<<16) | ((x>>16)&0x0000ffff0000ffffUL)
             | (x<<32) | (x>>32);
    }

    static Sites Reach(int tip, Sites free) {
        ulong lo=free.Lo & N[tip].Lo, hi=free.Hi & N[tip].Hi;
        while (true) {
            ulong a=lo | (free.Lo & (WithinHalf(lo) | hi));
            ulong b=hi | (free.Hi & (WithinHalf(hi) | lo));
            if (a==lo && b==hi) return new Sites(lo,hi);
            lo=a; hi=b;
        }
    }

    static bool Enough(Sites free, int depth) {
        int even=Pop(free.Lo & evenSites.Lo)+Pop(free.Hi & evenSites.Hi);
        int odd=Pop(free.Lo & ~evenSites.Lo)+Pop(free.Hi & ~evenSites.Hi);
        return even >= 24-(depth+2)/2 && odd >= 24-(depth+1)/2;
    }

    static bool TooManyStars(Sites free, int tip, int depth) {
        // A path can retain at most three of a centre and three neighbours.
        int slack=Pop(free.Lo)+Pop(free.Hi)-(47-depth);
        free.Add(tip);
        if (slack>=8 || 4*(slack+1)>Pop(free.Lo)+Pop(free.Hi)) return false;
        foreach (int v in packOrder) {
            if (!free.Has(v)) continue;
            ulong a=free.Lo & N[v].Lo, b=free.Hi & N[v].Hi;
            if (Pop(a)+Pop(b)<3) continue;
            for (int i=0;i<3;++i) {
                if (a!=0) {
                    ulong bit=a & unchecked(0UL-a);
                    free.Lo ^= bit; a ^= bit;
                } else {
                    ulong bit=b & unchecked(0UL-b);
                    free.Hi ^= bit; b ^= bit;
                }
            }
            free.Remove(v);
            if (--slack<0) return true;
        }
        return false;
    }

    static void Emit() {
        paths.WriteLine(string.Join(" ",Path));
        ++count47;
        Sites selected = new Sites();
        foreach (int v in Path) selected.Add(v);
        for (int side=0;side<2;++side) {
            int end=Path[47*side], other=Path[47*(1-side)];
            for (int j=0;j<7;++j) {
                int w=end^(1<<j);
                if (w>=other || !allowed.Has(w) || selected.Has(w)) continue;
                if (Pop(N[w].Lo & selected.Lo)+Pop(N[w].Hi & selected.Hi)!=1) continue;
                // Both trims of a 48-edge path are enumerated. Emit just the
                // extension that appends its smaller endpoint.
                paths.Write(w);
                for (int i=0;i<48;++i) {
                    paths.Write(' ');
                    paths.Write(Path[side==0 ? i : 47-i]);
                }
                paths.WriteLine();
                ++count48;
            }
        }
    }

    static void Visit(int tip, int depth, Sites free) {
        if (nodes>=limit) { status="node_limit"; return; }
        if ((nodes & 16383)==0 && clock.Elapsed.TotalSeconds>=seconds) { status="time_limit"; return; }
        ++nodes;
        Path[depth]=tip;
        if (depth==47) { Emit(); return; }
        if (!Enough(free,depth)) { ++parityCuts; return; }
        if (depth%3==0) {
            free=Reach(tip,free);
            if (!Enough(free,depth)) { ++reachCuts; return; }
            if (TooManyStars(free,tip,depth)) { ++starCuts; return; }
        }
        Sites next = new Sites(free.Lo & ~N[tip].Lo,free.Hi & ~N[tip].Hi);
        for (int j=0;j<7;++j) {
            int v=tip^(1<<j);
            if (free.Has(v)) {
                Visit(v,depth+1,next);
                if (status!="complete") return;
            }
        }
    }

    static void Main(string[] args) {
        int[] excluded=File.ReadAllText(args[0]).Trim().Split(' ').Select(int.Parse).ToArray();
        allowed=new Sites(ulong.MaxValue,ulong.MaxValue);
        foreach(int v in excluded) allowed.Remove(v);
        for(int v=0;v<128;++v) {
            for(int j=0;j<7;++j) N[v].Add(v^(1<<j));
            Even[v]=(Pop((ulong)v)%2==0);
            if (Even[v]) evenSites.Add(v);
        }
        packOrder=Enumerable.Range(0,128).Where(v=>allowed.Has(v))
            .OrderByDescending(v=>Pop(N[v].Lo & allowed.Lo)+Pop(N[v].Hi & allowed.Hi)).ToArray();
        int[] roots=Enumerable.Range(0,128).Where(v=>allowed.Has(v) && Even[v]).ToArray();
        int first=int.Parse(args[3]), stop=int.Parse(args[4]);
        limit=long.Parse(args[5]); seconds=int.Parse(args[6]);
        if (roots.Length!=40 || first<0 || stop>40 || first>=stop || limit<1 || seconds<1)
            throw new Exception("Invalid complement or run limits");
        clock=Stopwatch.StartNew();
        using(paths=new StreamWriter(args[1]))
        using(StreamWriter summary=new StreamWriter(args[2])) {
            for(int i=first;i<stop;++i) {
                Sites free=allowed;
                free.Remove(roots[i]);
                long before=nodes;
                Visit(roots[i],0,free);
                summary.WriteLine("root "+roots[i]+" "+status+" "+(nodes-before));
                summary.Flush();
                if (status!="complete") break;
            }
            summary.WriteLine("total "+status+" "+nodes+" "+count47+" "+count48+" "+
                              parityCuts+" "+reachCuts+" "+starCuts);
        }
    }
}
