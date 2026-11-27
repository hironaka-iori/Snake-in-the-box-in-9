using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;

// Enumerate the two lower tails in a fixed order. Each ordered pair has a unique visit.
class Ends {
    static int[] a=new int[512], b=new int[512], m, occupied=new int[512], contacts=new int[512];
    static bool[] unavailable=new bool[512];
    static int na, nb, fixedA, fixedB, best, capture, saved;
    static string bestPath;
    static long budget, visits;
    static bool exhausted, fullCube;
    static int dimension;
    static long[] histogram=new long[512];
    static StreamWriter results;
    static string id;
    static int[] Parse(string s) { return Array.ConvertAll(s.Split(','),int.Parse); }
    static void Set(int v, int d) {
        occupied[v]+=d;
        for(int i=0;i<dimension;i++) contacts[v^(1<<i)]+=d;
    }
    static string Join() {
        var outp=new List<int>(na+nb+m.Length);
        for(int j=na-1;j>=0;j--) outp.Add(a[j]);
        foreach(int v in m) outp.Add(fullCube?v:256+v);
        for(int j=0;j<nb;j++) outp.Add(b[j]);
        return string.Join(",",outp);
    }
    static bool Visit() {
        if(visits>=budget) { exhausted=false; return false; }
        visits++; return true;
    }
    static void Right() {
        if(!Visit()) return;
        int len=na+nb+m.Length-1;
        histogram[len]++;
        if(len>best) { best=len; bestPath=Join(); }
        if(len>=capture && saved<2500) { results.WriteLine("P\t"+id+"\t"+Join()); saved++; }
        int tip=b[nb-1];
        for(int i=0;i<dimension && exhausted;i++) {
            int v=tip^(1<<i);
            if(unavailable[v] || occupied[v]!=0 || contacts[v]!=1) continue;
            b[nb++]=v; Set(v,1); Right(); Set(v,-1); nb--;
        }
    }
    static void Left() {
        if(!Visit()) return;
        Right();
        int tip=a[na-1];
        for(int i=0;i<dimension && exhausted;i++) {
            int v=tip^(1<<i);
            if(unavailable[v] || occupied[v]!=0 || contacts[v]!=1) continue;
            a[na++]=v; Set(v,1); Left(); Set(v,-1); na--;
        }
    }
    static void Main(string[] args) {
        budget=long.Parse(args[2]); capture=int.Parse(args[3]);fullCube=args.Length>4 && args[4]=="full";dimension=fullCube?9:8;
        using(results=new StreamWriter(args[1])) {
            foreach(string s in File.ReadLines(args[0])) {
                var t=s.Split('\t'); id=t[0];
                int[] left=Parse(t[1]), right=Parse(t[3]); m=Parse(t[2]);
                Array.Clear(occupied,0,512); Array.Clear(contacts,0,512); Array.Clear(unavailable,0,512);
                foreach(int v in m) {unavailable[v]=true; if(fullCube) Set(v,1);}
                left.CopyTo(a,0); right.CopyTo(b,0); fixedA=na=left.Length; fixedB=nb=right.Length;
                foreach(int v in left.Concat(right)) Set(v,1);
                best=-1; bestPath=""; visits=0; saved=0; exhausted=true; Array.Clear(histogram,0,512);
                Left();
                if(na!=fixedA || nb!=fixedB) throw new Exception("Unbalanced search");
                results.WriteLine(string.Join("\t", new string[]{ "S",id,exhausted ? "1":"0",visits.ToString(),
                    best.ToString(),bestPath,saved.ToString(),string.Join(",",histogram.Take(best+1).Skip(fixedA+fixedB+m.Length-1))}));
                results.Flush();
            }
        }
    }
}

