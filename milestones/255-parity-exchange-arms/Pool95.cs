using System;
using System.Collections.Generic;
using System.Linq;

class Pool95 {
    const int Size = 48;
    const ulong Full = (1UL << Size)-1;
    readonly int[] side;
    readonly int removed, added;
    readonly ulong[] graph = new ulong[Size];
    readonly List<int>[,] labels = new List<int>[Size, Size];
    readonly List<int>[] singleton = new List<int>[Size];
    readonly int[] order = new int[Size];
    readonly int[] path = new int[2*Size];
    long nodes, orders, paths;

    Pool95(int[] vertices, int r, int a) {
        side = vertices;
        removed = r; added = a;
        int[] index = Enumerable.Repeat(-1, 256).ToArray();
        for (int i=0; i<Size; i++) index[vertices[i]]=i;
        for (int v=0; v<256; v++) {
            int count=0, first=-1, second=-1;
            for (int j=0; j<8; j++) {
                int pos=index[v ^ (1<<j)];
                if (pos<0) continue;
                if (count==0) first=pos;
                if (count==1) second=pos;
                if (++count==3) break;
            }
            if (count==1) {
                if (singleton[first]==null) singleton[first]=new List<int>();
                singleton[first].Add(v);
            } else if (count==2) {
                graph[first] |= 1UL<<second;
                graph[second] |= 1UL<<first;
                if (labels[first,second]==null)
                    labels[first,second]=labels[second,first]=new List<int>();
                labels[first,second].Add(v);
            }
        }
    }

    static int Position(ulong low) {
        int p=0;
        if ((low & 0xffffffffUL)==0) { low >>= 32; p+=32; }
        if ((low & 65535UL)==0) { low >>= 16; p+=16; }
        if ((low & 255UL)==0) { low >>= 8; p+=8; }
        if ((low & 15UL)==0) { low >>= 4; p+=4; }
        if ((low & 3UL)==0) { low >>= 2; p+=2; }
        if ((low & 1UL)==0) p++;
        return p;
    }

    void Materialize(int i) {
        if (i==Size) {
            // Output starts on the fixed parity side, so its even indices recover S.
            paths++;
            Console.WriteLine("P {0} {1} {2}",removed,added,string.Join(",",path.Reverse()));
            return;
        }
        foreach (int link in labels[order[i-1],order[i]]) {
            path[2*i]=link;
            path[2*i+1]=side[order[i]];
            Materialize(i+1);
        }
    }

    void Visit(int used, ulong unused) {
        nodes++;
        if (unused==0) {
            orders++;
            foreach (int tip in singleton[order[0]]) {
                path[0]=tip;
                path[1]=side[order[0]];
                Materialize(1);
            }
            return;
        }
        int last=order[used-1];
        ulong moves=graph[last] & unused;
        if (moves==0) return;
        ulong residual=unused | (1UL<<last);
        ulong forced=0;
        for (ulong todo=unused; todo!=0; todo &= todo-1) {
            ulong low=todo & (~todo+1);
            ulong n=graph[Position(low)] & residual;
            if (n==0) return;
            if ((n & (n-1))==0) {
                if (forced!=0) return;
                forced=low;
            }
        }
        if ((unused & (unused-1))!=0) moves &= ~forced;
        while (moves!=0) {
            ulong low=moves & (~moves+1);
            moves ^= low;
            order[used]=Position(low);
            Visit(used+1,unused ^ low);
        }
    }

    void Enumerate() {
        for (int i=0; i<Size; i++) if (singleton[i]!=null) {
            order[0]=i;
            Visit(1,Full ^ (1UL<<i));
        }
        Console.WriteLine("S {0} {1} {2} {3} {4}",removed,added,orders,paths,nodes);
    }

    static int Parity(int v) {
        int p=0;
        while (v!=0) { v &= v-1; p ^= 1; }
        return p;
    }

    static void Main() {
        int[] seed=Console.ReadLine().Split(',').Select(int.Parse).OrderBy(v=>v).ToArray();
        if (seed.Length!=Size || seed.Distinct().Count()!=Size ||
            seed.Any(v=>v<0 || v>=256 || Parity(v)!=Parity(seed[0])))
            throw new ArgumentException("Invalid starting parity side");
        new Pool95(seed,-1,-1).Enumerate();
        for (int i=0; i<Size; i++) for (int a=0; a<256; a++)
            if (Parity(a)==Parity(seed[0]) && Array.BinarySearch(seed,a)<0) {
                int[] s=(int[])seed.Clone();
                s[i]=a;
                Array.Sort(s);
                new Pool95(s,seed[i],a).Enumerate();
            }
    }
}
