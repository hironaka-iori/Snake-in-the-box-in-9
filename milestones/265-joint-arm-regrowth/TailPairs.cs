using System;
using System.Collections.Generic;
using System.Linq;

// Enumerate tails independently against the two retained prefixes, then match
// their vertex sets. The sole common projected site allowed is the crossing.
class TailPairs {
    static readonly int[][] N=Enumerable.Range(0,256).Select(v=>Enumerable.Range(0,8).Select(j=>v^(1<<j)).ToArray()).ToArray();
    static readonly int[] Parity=Enumerable.Range(0,256).Select(v=>Convert.ToString(v,2).Count(b=>b=='1')%2).ToArray();
    struct Mask {
        public ulong a,b,c,d;
        public Mask With(int v) {
            Mask m=this;
            ulong bit=1UL<<(v&63);
            switch(v>>6){case 0:m.a|=bit;break;case 1:m.b|=bit;break;case 2:m.c|=bit;break;default:m.d|=bit;break;}
            return m;
        }
        public bool Disjoint(Mask m){return ((a&m.a)|(b&m.b)|(c&m.c)|(d&m.d))==0;}
    }
    class Tree {
        public List<Mask>[] at=Enumerable.Range(0,99).Select(i=>new List<Mask>()).ToArray();
        readonly int[] forbidden=new int[256],path=new int[99],queue=new int[256],stamp=new int[256],free={128,128};
        readonly int min,limit;
        int stampID,stored;
        public int nodes,pruned;
        public bool complete=true;
        public Tree(int[] prefix,int[] other,int threshold,int maxNodes) {
            min=threshold;limit=maxNodes;
            foreach(int v in other)Block(v,1);
            Mask bits=new Mask();
            for(int i=0;i<prefix.Length;i++) {
                int v=prefix[i];path[i]=v;
                if(i>0)bits=bits.With(v);
                if(i+1<prefix.Length)Mark(v,1);
            }
            Visit(prefix.Length-1,bits);
        }
        void Block(int v,int delta) {
            int old=forbidden[v];forbidden[v]+=delta;
            if(old==0)free[Parity[v]]--;else if(forbidden[v]==0)free[Parity[v]]++;
        }
        void Mark(int v,int delta){Block(v,delta);foreach(int w in N[v])Block(w,delta);}
        bool EnoughReachable(int tip,int need) {
            int[] counts={0,0};
            int first=1-Parity[tip],wantedFirst=(need+1)/2,wantedSecond=need/2;
            if(free[first]<wantedFirst || free[1-first]<wantedSecond)return false;
            int head=0,tail=1;
            queue[0]=tip;stamp[tip]=++stampID;
            while(head<tail) {
                int u=queue[head++];
                foreach(int v in N[u]) if(forbidden[v]==0 && stamp[v]!=stampID) {
                    stamp[v]=stampID;queue[tail++]=v;counts[Parity[v]]++;
                    if(counts[first]>=wantedFirst && counts[1-first]>=wantedSecond)return true;
                }
            }
            return false;
        }
        void Visit(int depth,Mask bits) {
            if(nodes==limit || stored>=30000){complete=false;return;}
            nodes++;
            if(depth>=min){at[depth].Add(bits);stored++;}
            if(depth==98)return;
            int tip=path[depth],need=min-depth;
            if(need>=5 && depth%4==0 && !EnoughReachable(tip,need)){pruned++;return;}
            int options=0;
            for(int j=0;j<8;j++)if(forbidden[N[tip][j]]==0)options|=1<<j;
            if(options==0)return;
            Mark(tip,1);
            for(int j=0;j<8 && complete;j++) if((options&(1<<j))!=0) {
                int w=N[tip][j];path[depth+1]=w;
                Visit(depth+1,bits.With(w));
            }
            Mark(tip,-1);
        }
        public string Sizes(){return string.Join(",",at.Skip(min).Select(t=>t.Count));}
    }
    static int[] Read(){return Console.ReadLine().Split(',').Select(int.Parse).ToArray();}
    static int[] Recover(Mask m,int edges){
        var result=new List<int>{0};
        int v=0;
        while(result.Count<=edges) {
            var next=N[v].Where(w=>!m.Disjoint(new Mask().With(w)) && !result.Contains(w)).ToArray();
            if(next.Length!=1)throw new Exception("Mask is not an induced rooted arm");
            v=next[0];result.Add(v);
        }
        return result.ToArray();
    }
    static void Main(string[] args) {
        int target=int.Parse(args[0]),limit=int.Parse(args[1]),min=target-99;
        int[] a=Read(),b=Read();
        var x=new Tree(a,b,min,limit);var y=new Tree(b,a,min,limit);
        long pairs=0;bool decided=true;
        int[] wa=null,wb=null;
        for(int i=min;i<=98 && wa==null;i++) {
            int j=target-1-i;
            if(!((x.complete && x.at[i].Count==0) || (y.complete && y.at[j].Count==0) || (x.complete && y.complete)))decided=false;
            foreach(Mask p in x.at[i]) {
                foreach(Mask q in y.at[j]) {
                    if(pairs==12000000){decided=false;break;}
                    pairs++;
                    if(p.Disjoint(q)){wa=Recover(p,i);wb=Recover(q,j);break;}
                }
                if(wa!=null || pairs==12000000)break;
            }
        }
        Console.WriteLine(wa!=null?"witness":(decided?"excluded":"open"));
        foreach(Tree t in new[]{x,y})Console.WriteLine(t.nodes+" "+t.pruned+" "+(t.complete?1:0)+" "+t.Sizes());
        Console.WriteLine(pairs);
        if(wa!=null){Console.WriteLine(string.Join(",",wa));Console.WriteLine(string.Join(",",wb));}
    }
}
