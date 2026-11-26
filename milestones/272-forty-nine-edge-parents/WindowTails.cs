using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;

// Split the added edges uniquely into a left tail and a right tail for the fixed interval.
class WindowTails {
    static readonly int[][] adj=Enumerable.Range(0,128).Select(v=>Enumerable.Range(0,7).Select(d=>v^(1<<d)).ToArray()).ToArray();
    static readonly bool[] used=new bool[128];
    static readonly byte[] near=new byte[128];
    static readonly int[] chain=new int[150];
    static int left0,right0,limit;
    static long visits,emitted;
    static void Mark(int v,bool add) {
        used[v]=add;
        foreach(int n in adj[v]) { if(add)near[n]++;else near[n]--; }
    }
    static void Right(int l,int r,int remaining) {
        visits++;
        if(remaining==0) {
            Console.WriteLine("P "+String.Join(",",new ArraySegment<int>(chain,l,r-l+1)));
            emitted++;return;
        }
        foreach(int v in adj[chain[r]]) if(!used[v] && near[v]==1) {
            chain[r+1]=v;Mark(v,true);Right(l,r+1,remaining-1);Mark(v,false);
        }
    }
    static void Left(int l,int remaining) {
        Right(l,right0,remaining);
        if(remaining==0)return;
        foreach(int v in adj[chain[l]]) if(!used[v] && near[v]==1) {
            chain[l-1]=v;Mark(v,true);Left(l-1,remaining-1);Mark(v,false);
        }
    }
    static void Main() {
        string line;
        while((line=Console.ReadLine())!=null) {
            int[] vertices=line.Split(',').Select(int.Parse).ToArray();
            limit=50-vertices.Length;left0=50;right0=left0+vertices.Length-1;
            vertices.CopyTo(chain,left0);foreach(int p in vertices)Mark(p,true);
            visits=0;emitted=0;Left(left0,limit);
            Console.WriteLine("T "+visits+" "+emitted);
            foreach(int p in vertices)Mark(p,false);
        }
    }
}
