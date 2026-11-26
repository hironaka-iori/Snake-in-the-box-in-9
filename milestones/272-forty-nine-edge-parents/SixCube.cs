using System;
using System.IO;
using System.Collections.Generic;
using System.Linq;

// The larger half of a single-crossing Q7 snake with at least 48 edges has at least 24 edges.
class SixCube {
    static readonly ulong[] near=new ulong[64];
    static readonly int[] path=new int[64], touch=new int[64];
    static readonly bool[] used=new bool[64], barred=new bool[64];
    static readonly List<int[]> large=new List<int[]>();
    static int[] parent;
    static bool roots, audit;
    static StreamWriter pairs;
    static long visits;
    static int largest;
    static void Enter(int d) {
        visits++;
        if(roots) {
            largest=Math.Max(largest,d);
            if(d>=24)large.Add(path.Take(d+1).ToArray());
        } else if(d+parent.Length>=48 && d<parent.Length) {
            pairs.WriteLine(String.Join(",",parent)+";"+String.Join(",",path.Take(d+1)));
        }
    }
    static void MaskWalk(int d,int usedAxes,ulong free) {
        Enter(d);
        if(!roots && d+1>=parent.Length)return;
        int tip=path[d];
        int last=roots?Math.Min(usedAxes,5):5;
        for(int j=0;j<=last;j++) {
            int v=tip^(1<<j);
            if((free&(1UL<<v))==0)continue;
            path[d+1]=v;
            MaskWalk(d+1,Math.Max(usedAxes,j+1),free&~near[tip]);
        }
    }
    static void Mark(int v,bool add) {
        used[v]=add;
        for(int j=0;j<6;j++)touch[v^(1<<j)]+=add?1:-1;
    }
    static void ContactWalk(int d,int usedAxes) {
        Enter(d);
        if(!roots && d+1>=parent.Length)return;
        int tip=path[d];
        for(int j=5;j>=0;j--) {
            if(roots && j>usedAxes)continue;
            int v=tip^(1<<j);
            if(used[v] || barred[v] || touch[v]!=1)continue;
            path[d+1]=v;Mark(v,true);
            ContactWalk(d+1,Math.Max(usedAxes,j+1));
            Mark(v,false);
        }
    }
    static void Run(ulong free) {
        if(audit) {Mark(0,true);ContactWalk(0,0);Mark(0,false);}
        else MaskWalk(0,0,free);
    }
    static void Main(string[] args) {
        audit=args[0]=="contacts";
        for(int v=0;v<64;v++)
            for(int j=0;j<6;j++)near[v]|=1UL<<(v^(1<<j));
        roots=true;Run(ulong.MaxValue^1UL);
        long initial=visits;visits=0;
        using(var list=new StreamWriter(args[1]))
            foreach(int[] q in large)list.WriteLine(String.Join(",",q));
        roots=false;
        using(pairs=new StreamWriter(args[2])) {
            foreach(int[] q in large) {
                parent=q;ulong free=ulong.MaxValue^1UL;
                for(int i=1;i<q.Length;i++) {barred[q[i]]=true;free&=~(1UL<<q[i]);}
                Run(free);
                foreach(int v in q)barred[v]=false;
            }
        }
        Console.WriteLine(initial+" "+large.Count+" "+largest+" "+visits);
    }
}
