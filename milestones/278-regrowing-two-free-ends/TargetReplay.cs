using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;

// Reverse the order of the two searches and calculate a separate upper bound.
// Available internal vertices have no contact with the retained path. Each tail after
// its first vertex has to remain in one connected component of these available sites.
class TargetReplay {
    static int[] incident=new int[512],visit=new int[512],component=new int[512],queue=new int[512],ones=new int[513],zeros=new int[513];
    static int[] accessL=new int[513],accessR=new int[513],weight=new int[512];
    static bool[] present=new bool[512]; static int tick,groups,goal;
    static long count,limit,cut;static bool open,hit;static string path;
    static List<int> interval=new List<int>();
    static void Set(int v,bool used) {
        present[v]=used;
        for(int k=0;k<9;k++)incident[v^(1<<k)]+=used?1:-1;
    }
    static bool Legal(int v) { return !present[v] && incident[v]==1; }
    static int Paint(int u) {
        if(visit[u]==tick)return component[u];
        int g=++groups, end=1;queue[0]=u;visit[u]=tick;zeros[g]=ones[g]=0;
        for(int p=0;p<end;p++) {
            int v=queue[p];component[v]=g;
            if(weight[v]==0)zeros[g]++;else ones[g]++;
            for(int k=0;k<9;k++){
                int w=v^(1<<k);
                if(present[w] || incident[w]!=0 || visit[w]==tick)continue;
                visit[w]=tick;queue[end++]=w;
            }
        }
        return g;
    }
    static bool Domains(int tip,int[] tags) {
        bool can=false;
        for(int k=8;k>=0;k--){
            int w=tip^(1<<k);if(!Legal(w))continue;
            can=true;
            for(int d=0;d<9;d++){
                int u=w^(1<<d);
                if(!present[u] && incident[u]==0) tags[Paint(u)]=tick;
            }
        }
        return can;
    }
    static bool Feasible(bool allowLeft) {
        int n=interval.Count,d=goal+1-n,l=interval[0],r=interval[n-1];
        if(d==0)return true;
        tick++;groups=0;
        bool ls=allowLeft && Domains(l,accessL),rs=Domains(r,accessR);
        // Vary the possible lengths of the two tails explicitly. For each length pair
        // compare the required parity counts with every permitted component assignment.
        for(int a=ls?d:0;a>=0;a--) {
            int b=d-a;
            if(b>0 && !rs) continue;
            int l0=(a+weight[l])/2,l1=a-l0,r0=(b+weight[r])/2,r1=b-r0;
            if(a>0) {if(weight[l]==1)l0--;else l1--;}
            if(b>0) {if(weight[r]==1)r0--;else r1--;}
            for(int i=0;i<=groups;i++) {
                if(i>0 && (a<2 || accessL[i]!=tick))continue;
                if(l0>zeros[i] || l1>ones[i])continue;
                for(int j=0;j<=groups;j++){
                    if(j>0 && (b<2 || accessR[j]!=tick))continue;
                    if(r0>zeros[j] || r1>ones[j])continue;
                    if(i!=j || (l0+r0<=zeros[i] && l1+r1<=ones[i]))return true;
                }
            }
        }
        return false;
    }
    static void Walk(bool left) {
        if(open || hit)return;
        if(++count>limit){open=true;return;}
        if(interval.Count==goal+1){hit=true;path=string.Join(",",interval);return;}
        if(!Feasible(left)){cut++;return;}
        // This worker reverses the entire donor interval on input. It explores the
        // first side's next extension before it chooses to close that side.
        int root=left?interval[0]:interval[interval.Count-1];
        for(int d=8;d>=0 && !open && !hit;d--){
            int u=root^(1<<d);if(!Legal(u))continue;
            if(left)interval.Insert(0,u);else interval.Add(u);
            Set(u,true);Walk(left);Set(u,false);
            interval.RemoveAt(left?0:interval.Count-1);
        }
        if(left) Walk(false);
    }
    static void Main(string[] args) {
        goal=int.Parse(args[2]);limit=long.Parse(args[3]);
        for(int x=1;x<512;x++)weight[x]=1-weight[x&(x-1)];
        using(var output=new StreamWriter(args[1]))foreach(string row in File.ReadLines(args[0])) {
            string[] t=row.Split('\t');
            interval=Array.ConvertAll(t[1].Split(','),int.Parse).Reverse().ToList();
            Array.Clear(incident,0,512);Array.Clear(present,0,512);
            foreach(int v in interval)Set(v,true);
            count=cut=0;open=hit=false;path="";
            Walk(true);
            output.WriteLine(string.Join("\t",new string[]{t[0],hit?"witness":(open?"open":"excluded"),count.ToString(),cut.ToString(),path}));
            output.Flush();
            if(hit)break;
        }
    }
}

