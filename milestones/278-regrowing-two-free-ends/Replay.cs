using System;
using System.IO;
using System.Linq;

// Availability masks implement an independent search from the opposite free end first.
// Extending a tail retires every neighbour of its former tip. Disjoint tails also
// retire the closed neighbourhood of each newly selected vertex in the other mask.
struct Set256 {
    public ulong w0,w1,w2,w3,w4,w5,w6,w7;
    public static Set256 All() { return new Set256{w0=ulong.MaxValue,w1=ulong.MaxValue,w2=ulong.MaxValue,w3=ulong.MaxValue,w4=ulong.MaxValue,w5=ulong.MaxValue,w6=ulong.MaxValue,w7=ulong.MaxValue}; }
    public void Clear(int v) {
        ulong k=~(1UL<<(v%64));
        switch(v/64) {case 0:w0&=k;break;case 1:w1&=k;break;case 2:w2&=k;break;case 3:w3&=k;break;case 4:w4&=k;break;case 5:w5&=k;break;case 6:w6&=k;break;default:w7&=k;break;}
    }
    public bool Has(int v) {
        ulong z;
        switch(v/64) {case 0:z=w0;break;case 1:z=w1;break;case 2:z=w2;break;case 3:z=w3;break;
            case 4:z=w4;break;case 5:z=w5;break;case 6:z=w6;break;default:z=w7;break;}
        return (z & (1UL<<(v%64)))!=0;
    }
    public void Apply(Set256 keep) {w0&=keep.w0;w1&=keep.w1;w2&=keep.w2;w3&=keep.w3;w4&=keep.w4;w5&=keep.w5;w6&=keep.w6;w7&=keep.w7;}
}
class Replay {
    static Set256[] outside=new Set256[512];
    static long[] counts=new long[512];
    static long budget,visits;
    static bool complete, fullCube;
    static int dimension;
    static void GrowFirst(int tip,Set256 available,int length) {
        if(++visits>budget) {complete=false;return;}
        counts[length]++;
        Set256 next=available;next.Apply(outside[tip]);
        for(int j=dimension-1;j>=0 && complete;j--) {
            int v=tip^(1<<j);
            if(available.Has(v)) GrowFirst(v,next,length+1);
        }
    }
    static void GrowSecond(int end,Set256 second,int start,Set256 first,int length) {
        if(++visits>budget) {complete=false;return;}
        GrowFirst(start,first,length);
        Set256 next=second;next.Apply(outside[end]);
        for(int j=dimension-1;j>=0 && complete;j--) {
            int v=end^(1<<j);
            if(!second.Has(v)) continue;
            Set256 remaining=first;remaining.Apply(outside[v]);
            GrowSecond(v,next,start,remaining,length+1);
        }
    }
    static Set256 Initial(int[] middle,int[] own,int[] other) {
        var allowed=Set256.All();
        foreach(int v in middle) {if(fullCube) allowed.Apply(outside[v]);else allowed.Clear(v);}
        foreach(int v in other) allowed.Apply(outside[v]);
        for(int k=0;k+1<own.Length;k++) allowed.Apply(outside[own[k]]);
        allowed.Clear(own.Last());
        return allowed;
    }
    static int[] Parse(string seq) {return Array.ConvertAll(seq.Split(','),int.Parse);}
    static void Main(string[] args) {
        budget=long.Parse(args[2]);fullCube=args.Length>3 && args[3]=="full";dimension=fullCube?9:8;
        for(int v=0;v<(1<<dimension);v++) {
            var s=Set256.All();s.Clear(v);
            for(int j=0;j<dimension;j++) s.Clear(v^(1<<j));
            outside[v]=s;
        }
        using(var writer=new StreamWriter(args[1])) foreach(string row in File.ReadLines(args[0])) {
            var t=row.Split('\t');var a=Parse(t[1]);var m=Parse(t[2]);var b=Parse(t[3]);
            int length=a.Length+m.Length+b.Length-1;
            visits=0;complete=true;Array.Clear(counts,0,512);
            GrowSecond(b.Last(),Initial(m,b,a),a.Last(),Initial(m,a,b),length);
            int high=Array.FindLastIndex(counts,c=>c!=0);
            writer.WriteLine(t[0]+"\t"+(complete?"1":"0")+"\t"+visits+"\t"+string.Join(",",counts.Skip(length).Take(high-length+1)));
        }
    }
}

