// Enumerate ordered paths by freely extending first the left, then the right end.
using System;
using System.IO;
using System.Linq;
using System.Collections.Generic;

class Grow {
    readonly bool[] used = new bool[256];
    readonly int[] contacts = new int[256];
    readonly int[] path = new int[200];
    readonly HashSet<string> seen = new HashSet<string>();
    long nodes;
    int segment;
    int first;
    readonly TextWriter output;
    Grow(TextWriter writer) { output = writer; }

    void Set(int v, bool present) {
        used[v] = present;
        int increment = present ? 1 : -1;
        for (int j=0; j<8; j++) contacts[v ^ (1<<j)] += increment;
    }

    void Record(int lo, int hi) {
        string word = String.Join(",",path.Skip(lo).Take(hi-lo+1));
        if (seen.Add(word))
            output.WriteLine("P " + segment + " " + (first-lo) + " " + word);
    }

    void Right(int lo, int hi) {
        nodes++;
        if (hi-lo >= 96) Record(lo,hi);
        if (hi-lo == 98) return;
        for (int j=0; j<8; j++) {
            int v = path[hi] ^ (1<<j);
            if (used[v] || contacts[v]!=1) continue;
            path[hi+1]=v; Set(v,true);
            Right(lo,hi+1); Set(v,false);
        }
    }

    void Left(int lo, int hi) {
        Right(lo,hi);
        if (hi-lo == 98) return;
        for (int j=0; j<8; j++) {
            int v=path[lo] ^ (1<<j);
            if (used[v] || contacts[v]!=1) continue;
            path[lo-1]=v; Set(v,true);
            Left(lo-1,hi); Set(v,false);
        }
    }

    void Segment(string line) {
        int[] core=Array.ConvertAll(line.Split(','),Int32.Parse);
        first=98-(core.Length-1);
        Array.Copy(core,0,path,first,core.Length);
        foreach(int v in core) Set(v,true);
        nodes=0;
        Left(first,first+core.Length-1);
        foreach(int v in core) Set(v,false);
        output.WriteLine("C " + segment + " " + nodes);
        segment++;
    }

    public static void Main(string[] args) {
        using (var writer=new StreamWriter(args[1])) {
            var run=new Grow(writer);
            foreach(string line in File.ReadLines(args[0])) run.Segment(line);
        }
    }
}
