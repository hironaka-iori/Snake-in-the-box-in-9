using System;
using System.Collections.Generic;
using System.Linq;

// For each retained edge count k, this group contains the stopped prefix and
// paths whose next edge differs from the archived edge (all choices at its tip).
class Prefix254
{
    readonly bool[] parent = new bool[256], used = new bool[256];
    readonly int[] contacts = new int[256], path = new int[256];
    readonly int[][] neighbor = new int[256][];
    readonly int[][][] order;
    readonly int[] seed;
    int nodes, budget, bestCount;
    int[] best;
    bool truncated;

    Prefix254(int[] blocked, int[] original)
    {
        seed=original;
        foreach(int v in blocked) parent[v]=true;
        for(int v=0;v<256;v++) neighbor[v]=Enumerable.Range(0,8).Select(i=>v^(1<<i)).ToArray();
        int[] position=Enumerable.Repeat(-1000,256).ToArray();
        for(int j=0;j<seed.Length;j++) position[seed[j]]=j;
        order=new int[256][][];
        for(int n=0;n<256;n++) {
            order[n]=new int[256][];
            for(int v=0;v<256;v++) {
                var shuffled=neighbor[v].OrderBy(x=>((x*31+1)*(v*17+n*11+1))&255);
                order[n][v]=shuffled.OrderBy(x=>Math.Abs(position[x]-n)).ToArray();
            }
        }
    }

    void Mark(int v,bool on)
    {
        used[v]=on; int delta=on?1:-1;
        foreach(int w in neighbor[v]) contacts[w]+=delta;
    }

    void Visit(int count)
    {
        if(nodes==budget) { truncated=true; return; }
        nodes++;
        if(count>bestCount) {bestCount=count; best=path.Take(count).ToArray();}
        int tip=path[count-1];
        foreach(int w in order[count][tip]) {
            if(parent[w] || used[w] || contacts[w]!=1) continue;
            path[count]=w; Mark(w,true); Visit(count+1); Mark(w,false);
            if(truncated) break;
        }
    }

    // An independent counter tracks the available vertices after each departure.
    // The current tip's neighbors remain possible for one step only.
    struct Mask
    {
        public ulong a,b,c,d;
        public bool Has(int v) {
            ulong word=v<64?a:(v<128?b:(v<192?c:d));
            return (word & (1UL<<(v&63)))!=0;
        }
        public void Remove(int v) {
            ulong m=~(1UL<<(v&63));
            if(v<64) a&=m; else if(v<128) b&=m; else if(v<192) c&=m; else d&=m;
        }
        public Mask Intersect(Mask t) {return new Mask{a=a&t.a,b=b&t.b,c=c&t.c,d=d&t.d};}
        public static Mask Full() {return new Mask{a=ulong.MaxValue,b=ulong.MaxValue,c=ulong.MaxValue,d=ulong.MaxValue};}
    }
    readonly Mask[] after=new Mask[256];
    long replayNodes;
    int replayEdges;

    void Replay(int v, int edges,Mask free)
    {
        replayNodes++; if(edges>replayEdges) replayEdges=edges;
        var next=free.Intersect(after[v]);
        foreach(int w in neighbor[v]) if(free.Has(w)) Replay(w,edges+1,next);
    }

    void Search()
    {
        var open=Mask.Full();
        for(int v=0;v<256;v++) {
            if(parent[v]) open.Remove(v);
            var m=Mask.Full(); m.Remove(v);
            foreach(int w in neighbor[v]) m.Remove(w);
            after[v]=m;
        }
        bool allClosed=true;
        int archived=seed.Length-1;
        for(int k=archived;k>=8;k--) {
            Array.Copy(seed,path,k+1);
            for(int j=0;j<=k;j++) Mark(seed[j],true);
            bool complete=true;
            long work=1;
            best=seed.Take(k+1).ToArray();bestCount=k+1;
            int tip=seed[k], excluded=k<archived?seed[k+1]:-1;
            foreach(int w in neighbor[tip]) {
                if(w==excluded || parent[w] || used[w] || contacts[w]!=1) continue;
                budget=allClosed && k>=24 ? 4500000 : (k>=24?750000:240000);
                nodes=0; truncated=false; Mark(w,true); path[k+1]=w;
                Visit(k+2); Mark(w,false);
                work+=nodes; if(truncated) complete=false;
            }
            for(int j=0;j<=k;j++) Mark(seed[j],false);
            if(complete) {
                var free=open;
                for(int j=0;j<k;j++) free=free.Intersect(after[seed[j]]);
                var child=free.Intersect(after[tip]);
                replayNodes=1; replayEdges=k;
                foreach(int w in neighbor[tip]) if(w!=excluded && free.Has(w)) Replay(w,k+1,child);
                if(replayNodes!=work || replayEdges!=bestCount-1)
                    throw new InvalidOperationException("Independent first-difference enumeration disagrees");
            } else allClosed=false;
            Console.WriteLine(k+" "+(complete?1:0)+" "+work+" "+string.Join(",",best));
        }
    }
    static int[] Read() {return Console.ReadLine().Split(',').Select(int.Parse).ToArray();}
    static void Main() {new Prefix254(Read(),Read()).Search();}
}
