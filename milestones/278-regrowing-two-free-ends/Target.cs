using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;

// Decide whether a 192-edge path can contain a prescribed interval of the original Q9 path.
class Target {
    static int[,] adj=new int[512,9];
    static int[] degree=new int[512],parity=new int[512],queue=new int[512],first=new int[512],second=new int[512];
    static bool[] occupied=new bool[512];
    static int na, nb, goal, coreLength;
    static long nodes, budget, prunes;static bool complete,found;
    static int[] core;
    static string witness="";
    static void Put(int v,int delta) {
        occupied[v]=delta>0;
        for(int j=0;j<9;j++)degree[adj[v,j]]+=delta;
    }
    static int[] labels=new int[512], mark=new int[512], inA=new int[513],inB=new int[513], ca=new int[513],cb=new int[513], leaves=new int[513];
    static int serial, parts;
    static bool Options(int tip,int[] reaches) {
        bool canMove=false;
        for(int d=0;d<9;d++) {
            int first=adj[tip,d]; if(occupied[first] || degree[first]!=1)continue;
            canMove=true;
            for(int j=0;j<9;j++) {
                int start=adj[first,j];
                if(occupied[start] || degree[start]!=0)continue;
                if(mark[start]!=serial) {
                    int k=++parts, head=0,tail=1;queue[0]=start;mark[start]=serial;labels[start]=k;
                    ca[k]=cb[k]=leaves[k]=0;
                    while(head<tail) {
                        int u=queue[head++],cnt=0;
                        if(parity[u]==0)ca[k]++;else cb[k]++;
                        for(int i=0;i<9;i++) {
                            int w=adj[u,i];if(occupied[w] || degree[w]!=0)continue;
                            cnt++;
                            if(mark[w]==serial)continue;
                            mark[w]=serial;labels[w]=k;queue[tail++]=w;
                        }
                        if(cnt<=1)leaves[k]++;
                    }
                }
                reaches[labels[start]]=serial;
            }
        }
        return canMove;
    }
    static int Bound(int tip,int component,bool canMove) {
        if(!canMove)return 0;
        int evens=ca[component]+parity[tip], odds=cb[component]+1-parity[tip];
        int opposite=parity[tip]==0?odds:evens;
        int same=parity[tip]==0?evens:odds;
        return Math.Min(Math.Min(2*opposite,2*same+1),1+ca[component]+cb[component]-Math.Max(0,leaves[component]-2));
    }
    static bool Can(int a,int b,int need,bool both) {
        serial++;parts=0;
        bool moveB=Options(b,inB), moveA=both && Options(a,inA);
        // Component zero allows a stopped tip or just one added vertex.
        for(int k=0;k<=parts;k++){
            if(k!=0 && inB[k]!=serial)continue;
            int ub=Bound(b,k,moveB);
            if(ub>=need)return true;
            if(!both)continue;
            for(int h=0;h<=parts;h++) {
                if(h!=0 && inA[h]!=serial)continue;
                int ua=Bound(a,h,moveA);
                if(ua+ub<need)continue;
                if(k!=h || k==0)return true;
                int total=ca[k]+cb[k]-Math.Max(0,leaves[k]-4)+2;
                if(total<need)continue;
                for(int l=Math.Max(0,need-ub);l<=Math.Min(need,ua);l++) {
                    int r=need-l;
                    int even=(l+parity[a])/2+(r+parity[b])/2;
                    int outsideEven=(l>0?parity[a]:0)+(r>0?parity[b]:0);
                    int outsideOdd=(l>0?1-parity[a]:0)+(r>0?1-parity[b]:0);
                    if(even<=ca[k]+outsideEven && need-even<=cb[k]+outsideOdd)return true;
                }
            }
        }
        return false;
    }

    static void Search(bool both) {
        if(found || !complete)return;
        if(++nodes>budget) {complete=false;return;}
        int need=goal-(coreLength-1+na+nb);
        if(need==0) {
            found=true;
            var r=first.Take(na).Reverse().Concat(core).Concat(second.Take(nb));witness=string.Join(",",r);return;
        }
        int a=na==0?core[0]:first[na-1], b=nb==0?core[coreLength-1]:second[nb-1];
        // These caps depend only on occupied sites and are valid regardless of future growth order.
        if(!Can(a,b,need,both)) { prunes++;return; }
        if(both) Search(false);
        int v=both?a:b;
        for(int j=0;j<9 && !found && complete;j++) {
            int w=adj[v,j];if(occupied[w] || degree[w]!=1)continue;
            if(both)first[na++]=w;else second[nb++]=w;
            Put(w,1); Search(both);Put(w,-1);
            if(both)na--;else nb--;
        }
    }
    static void Main(string[] args) {
        goal=int.Parse(args[2]);budget=long.Parse(args[3]);
        for(int v=0;v<512;v++) {
            for(int j=0;j<9;j++)adj[v,j]=v^(1<<j);
            if(v>0)parity[v]=1-parity[v&(v-1)];
        }
        using(var writer=new StreamWriter(args[1])) foreach(string row in File.ReadLines(args[0])) {
            var parts=row.Split('\t');core=Array.ConvertAll(parts[1].Split(','),int.Parse);
            coreLength=core.Length;na=nb=0;found=false;complete=true;nodes=prunes=0;witness="";
            Array.Clear(occupied,0,512);Array.Clear(degree,0,512);
            foreach(int v in core)Put(v,1);
            Search(true);
            writer.WriteLine(string.Join("\t",new[]{parts[0],found?"witness":(complete?"excluded":"open"),nodes.ToString(),prunes.ToString(),witness}));
            writer.Flush();
            if(found)break;
        }
    }
}

