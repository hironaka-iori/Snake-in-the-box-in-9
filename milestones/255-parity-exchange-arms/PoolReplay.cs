using System;
using System.Collections.Generic;
using System.Linq;

// Specify the unattached and attached ends. A spanning path is equivalent to
// a spanning cycle after adding a forced two-edge detour between those ends.
// Removing that detour gives degrees one at both ends and two elsewhere.
class PoolReplay {
    const int N=48;
    sealed class Edge {
        public int U,V;
        public readonly List<int> Labels=new List<int>();
        public int Other(int n) { return n==U ? V : U; }
    }
    readonly int[] side;
    readonly int number;
    readonly List<Edge> edges=new List<Edge>();
    readonly List<int>[] incident=new List<int>[N];
    readonly List<int>[] tip=new List<int>[N];
    readonly int[] path=new int[2*N];
    readonly int[] links=new int[N-1];
    long orders, paths;
    int first, last;

    PoolReplay(int id, int[] verts) {
        number=id; side=verts;
        var neighbours=new List<int>[256];
        for (int u=0; u<N; u++) {
            incident[u]=new List<int>();
            tip[u]=new List<int>();
            for (int j=0; j<8; j++) {
                int y=side[u] ^ (1<<j);
                if (neighbours[y]==null) neighbours[y]=new List<int>();
                neighbours[y].Add(u);
            }
        }
        var pair=new Dictionary<int,int>();
        for (int y=0; y<256; y++) {
            if (neighbours[y]==null) continue;
            var ns=neighbours[y];
            if (ns.Count==1) { tip[ns[0]].Add(y); continue; }
            if (ns.Count!=2) continue;
            int u=ns[0], v=ns[1], code=N*u+v, e;
            if (!pair.TryGetValue(code,out e)) {
                e=edges.Count;
                pair.Add(code,e);
                edges.Add(new Edge { U=u, V=v });
                incident[u].Add(e); incident[v].Add(e);
            }
            edges[e].Labels.Add(y);
        }
    }

    void Label(int i) {
        if (i==N-1) {
            foreach (int y in tip[last]) {
                path[2*N-1]=y;
                Console.WriteLine("P {0} {1}",number,string.Join(",",path));
                paths++;
            }
            return;
        }
        foreach (int y in edges[links[i]].Labels) {
            path[2*i+1]=y;
            Label(i+1);
        }
    }

    void Select(sbyte[] state) {
        bool changed;
        int decision;
        do {
            changed=false; decision=-1;
            int min=int.MaxValue;
            for (int u=0; u<N; u++) {
                int required=(u==first || u==last) ? 1 : 2;
                int accepted=0, free=0, recent=-1;
                foreach (int e in incident[u]) {
                    if (state[e]==1) accepted++;
                    if (state[e]==0) { free++; recent=e; }
                }
                if (accepted>required || accepted+free<required) return;
                if (free==0) continue;
                if (accepted==required || accepted+free==required) {
                    sbyte value=(sbyte)(accepted==required ? -1 : 1);
                    foreach (int e in incident[u]) if (state[e]==0) state[e]=value;
                    changed=true;
                } else if (free<min) {
                    min=free;
                    decision=recent;
                }
            }
        } while (changed);
        if (decision>=0) {
            var include=(sbyte[])state.Clone();
            include[decision]=1;
            Select(include);
            state[decision]=-1;
            Select(state);
            return;
        }
        int v=first, previous=-1, count=1;
        path[0]=side[v];
        while (v!=last) {
            int e=-1;
            foreach (int a in incident[v]) if (a!=previous && state[a]==1) { e=a; break; }
            if (e<0 || count>=N) throw new InvalidOperationException("Broken degree sequence");
            links[count-1]=e;
            v=edges[e].Other(v);
            path[2*count]=side[v];
            count++;
            previous=e;
        }
        if (count!=N) return;
        orders++;
        Label(0);
    }

    void Run() {
        var leaves=Enumerable.Range(0,N).Where(v=>incident[v].Count==1).ToArray();
        if (leaves.Length<=2 && incident.All(es=>es.Count>0)) {
            for (last=0; last<N; last++) {
                if (tip[last].Count==0) continue;
                for (first=0; first<N; first++) {
                    if (first==last || leaves.Any(v=>v!=first && v!=last)) continue;
                    Select(new sbyte[edges.Count]);
                }
            }
        }
        Console.WriteLine("S {0} {1} {2}",number,orders,paths);
    }

    static void Main() {
        string line;
        int id=0;
        while ((line=Console.ReadLine())!=null) {
            int[] side=line.Split(',').Select(int.Parse).ToArray();
            if (side.Length!=N || side.Distinct().Count()!=N || side.Any(v=>v<0 || v>=256))
                throw new ArgumentException("Invalid side");
            new PoolReplay(id++,side).Run();
        }
    }
}
