using System;
using System.Collections.Generic;
using System.Linq;

class Anchors {
    readonly int Target;
    readonly bool[] blocked=new bool[256];
    readonly bool rooted;
    readonly bool[] used=new bool[256];
    readonly int[] touches=new int[256];
    readonly int[,] neighbors=new int[256,8];
    readonly int[] weights=new int[256];
    readonly int[] middle=new int[256], tail=new int[256];
    readonly SortedSet<string> results=new SortedSet<string>(StringComparer.Ordinal);
    int[] p;
    int e,i,j,available,mode;
    long setups,visits,embeddings;

    Anchors(int order,int target,bool fixedCrossing) {
        mode=order;Target=target;rooted=fixedCrossing;
        for(int x=0;x<256;x++){
            for(int b=0;b<8;b++) neighbors[x,b]=x^(1<<b);
            if(x!=0)weights[x]=1+weights[x&(x-1)];
        }
    }
    void Mark(int v,bool take) {
        used[v]=take;
        for(int b=0;b<8;b++)touches[neighbors[v,b]]+=take?1:-1;
    }
    void Emit(int m,int t) {
        var a=new List<int>(Target);
        for(int k=t-1;k>=0;k--)a.Add(tail[k]);
        for(int k=e;k<=i;k++)a.Add(p[k]);
        for(int k=0;k<m;k++)a.Add(middle[mode==0?k:m-1-k]);
        for(int k=j;k<p.Length;k++)a.Add(p[k]);
        if(a.Count!=Target)throw new Exception("Wrong length");
        if(a[0]>a[a.Count-1])a.Reverse();
        results.Add(String.Join(",",a));embeddings++;
    }
    void GrowTail(int v,int n,int stop,int m) {
        if(rooted && results.Count>0)return;
        visits++;
        if(n==stop) {
            if(mode==0 || j==i+1) Emit(m,n);
            else Bridge(p[j],p[i],0,available-stop,stop);
            return;
        }
        for(int b=0;b<8;b++) {
            int w=neighbors[v,b];
            if(blocked[w] || used[w] || touches[w]!=1)continue;
            tail[n]=w;Mark(w,true);
            GrowTail(w,n+1,stop,m);
            Mark(w,false);
        }
    }
    void Bridge(int v,int dest,int n,int limit,int t) {
        if(rooted && results.Count>0)return;
        visits++;
        if(n>=limit || weights[v^dest]>limit-n+1)return;
        for(int b=0;b<8;b++){
            int w=neighbors[v,b];
            if(blocked[w] || used[w])continue;
            int d=weights[w^dest];
            if(d>limit-n)continue;
            if(d==1 && touches[w]==2) {
                if(mode==1 && n+1!=limit)continue;
                middle[n]=w;Mark(w,true);
                if(mode==0)GrowTail(p[e],0,available-n-1,n+1);else Emit(n+1,t);
                Mark(w,false);
            } else if(d>1 && touches[w]==1) {
                middle[n]=w;Mark(w,true);
                Bridge(w,dest,n+1,limit,t);
                Mark(w,false);
            }
        }
    }
    void Case() {
        setups++;
        int core=(i-e+1)+(p.Length-j);
        available=Target-core;
        if(available<0)return;
        for(int k=e;k<=i;k++)Mark(p[k],true);
        for(int k=j;k<p.Length;k++)Mark(p[k],true);
        if(j==i+1)GrowTail(p[e],0,available,0);
        else if(mode==0)Bridge(p[i],p[j],0,available,0);
        else {
            int least=weights[p[i]^p[j]]-1;
            for(int t=0;t<=available-least;t++)GrowTail(p[e],0,t,0);
        }
        for(int k=e;k<=i;k++)Mark(p[k],false);
        for(int k=j;k<p.Length;k++)Mark(p[k],false);
    }
    void Run(string key,int[] path,int gap,int trim,int[] forbidden) {
        results.Clear();setups=0;visits=0;embeddings=0;
        Array.Clear(blocked,0,blocked.Length);
        foreach(int v in forbidden)if(v!=0)blocked[v]=true;
        var reverse=path.Reverse().ToArray();
        foreach(int[] oriented in (rooted?new[]{reverse}:new[]{path,reverse})){
            p=oriented;
            for(e=0;e<=trim && e+1<p.Length && (!rooted || results.Count==0);e++){
                // A zero-width interior window is the same contiguous core at every split.
                i=e;j=e+1;Case();
                for(i=e;i+2<p.Length && (!rooted || results.Count==0);i++)for(j=i+2;j<p.Length && j-i-1<=gap && (!rooted || results.Count==0);j++)Case();
            }
        }
        foreach(string q in results)Console.WriteLine("P\t"+key+"\t"+q);
        Console.WriteLine("S\t"+key+"\t"+setups+"\t"+visits+"\t"+embeddings+"\t"+results.Count);
        Console.Out.Flush();
    }
    static void Main(string[] args) {
        int gap=int.Parse(args[0]),trim=int.Parse(args[1]),order=int.Parse(args[2]);
        bool rooted=args.Length>3; int target=rooted?int.Parse(args[3]):99;
        var scan=new Anchors(order,target,rooted);
        string line;
        while((line=Console.ReadLine())!=null) {
            string[] pair=line.Split('\t');
            scan.Run(pair[0],pair[1].Split(',').Select(Int32.Parse).ToArray(),gap,trim,
                rooted?pair[2].Split(',').Select(Int32.Parse).ToArray():new int[0]);
        }
    }
}
