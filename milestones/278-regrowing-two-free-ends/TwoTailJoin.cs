using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;

// Join two outward tails while preserving a literal ordered core in Q9.
class TwoTailJoin {
    static readonly int[][] adj=Enumerable.Range(0,512)
        .Select(v=>Enumerable.Range(0,9).Select(d=>v^(1<<d)).ToArray()).ToArray();
    static int target,storeLimit,timeLimit;
    static long nodeLimit,pairLimit;
    static bool near(int x,int y){int z=x^y;return (z&(z-1))==0;}
    static void validate(int[] path){
        bool[] seen=new bool[512];
        for(int i=0;i<path.Length;i++){
            int v=path[i];if(v<0||v>=512||seen[v])throw new Exception("Invalid or repeated vertex.");
            seen[v]=true;
            for(int j=0;j<i;j++)if(near(v,path[j])!=(j+1==i))throw new Exception("Invalid literal Q9 path.");
        }
    }
    sealed class Case {
        public readonly int[] core;
        public readonly int need;
        public readonly Stopwatch clock=Stopwatch.StartNew();
        public int[] witness;
        public long maskNodes,contactNodes,pairs;
        public int leftStored,rightStored;
        public string outcome="OPEN",reason="unstarted";
        public readonly int[] best={-1,-1};
        public readonly bool[] exact=new bool[2];
        public readonly long[][] hist=new long[2][];
        public Case(int[] p){core=p;need=target-p.Length+1;}
        public bool expired(){return clock.ElapsedMilliseconds>=timeLimit;}
        public void found(ushort[] left,ushort[] right,string why){
            int[] path=new int[left.Length+core.Length+right.Length];
            for(int j=0;j<left.Length;j++)path[j]=left[left.Length-1-j];
            Array.Copy(core,0,path,left.Length,core.Length);
            for(int j=0;j<right.Length;j++)path[left.Length+core.Length+j]=right[j];
            validate(path);
            if(path.Length-1<target)throw new Exception("Short witness.");
            for(int j=0;j<core.Length;j++)if(path[left.Length+j]!=core[j])throw new Exception("Core changed.");
            witness=path;outcome="WITNESS";reason=why;
        }
    }
    sealed class Traversal {
        public readonly long[] hist=new long[513];
        public readonly List<ushort[]> tails=new List<ushort[]>();
        public long nodes;
        public int best=-1;
        public bool complete=true;
        public string stop="";
        readonly bool[] free=new bool[512],used=new bool[512];
        readonly int[] touch=new int[512];
        readonly ushort[] seq=new ushort[513];
        readonly Case c;
        readonly int side,low,high;
        readonly bool replay,keep;
        public Traversal(Case spec,int s,bool contact,int lower,int upper,bool collect){
            c=spec;side=s;replay=contact;low=lower;high=upper;keep=collect;
        }
        bool enter(int depth){
            if(!complete||c.witness!=null)return false;
            if(nodes>=nodeLimit || ((nodes&255)==0&&c.expired())){
                complete=false;stop=c.expired()?"time":"nodes";return false;
            }
            nodes++;hist[depth]++;if(depth>best)best=depth;
            if(!keep&&depth==c.need){
                ushort[] tail=new ushort[depth];Array.Copy(seq,tail,depth);
                c.found(side==0?tail:new ushort[0],side==1?tail:new ushort[0],"one-end");
                complete=false;return false;
            }
            if(keep&&depth>=low){
                if(tails.Count>=storeLimit){complete=false;stop="tail-cap";return false;}
                ushort[] tail=new ushort[depth];Array.Copy(seq,tail,depth);tails.Add(tail);
            }
            return !keep||depth<high;
        }
        void retired(int tip,int depth){
            if(!enter(depth))return;
            int choices=0;
            for(int d=0;d<9;d++){
                int v=adj[tip][d];
                if(free[v]){choices|=1<<d;free[v]=false;}
            }
            for(int d=0;d<9&&complete&&c.witness==null;d++)if((choices&(1<<d))!=0){
                int v=adj[tip][d];seq[depth]=(ushort)v;retired(v,depth+1);
            }
            for(int d=0;d<9;d++)if((choices&(1<<d))!=0)free[adj[tip][d]]=true;
        }
        void mark(int v,bool add){
            used[v]=add;int delta=add?1:-1;
            foreach(int w in adj[v])touch[w]+=delta;
        }
        void contacts(int tip,int depth){
            if(!enter(depth))return;
            for(int d=8;d>=0&&complete&&c.witness==null;d--){
                int v=adj[tip][d];if(used[v]||touch[v]!=1)continue;
                seq[depth]=(ushort)v;mark(v,true);contacts(v,depth+1);mark(v,false);
            }
        }
        public void run(){
            int tip=c.core[side==0?0:c.core.Length-1];
            if(replay){
                foreach(int v in c.core)mark(v,true);
                contacts(tip,0);c.contactNodes+=nodes;
            }else{
                for(int v=0;v<512;v++)free[v]=true;
                foreach(int v in c.core){
                    free[v]=false;
                    if(v!=tip)foreach(int w in adj[v])free[w]=false;
                }
                retired(tip,0);c.maskNodes+=nodes;
            }
        }
    }
    static int compare(ushort[] a,ushort[] b){
        int n=Math.Min(a.Length,b.Length);
        for(int i=0;i<n;i++)if(a[i]!=b[i])return (int)a[i]-(int)b[i];
        return a.Length-b.Length;
    }
    static List<ushort[]> collect(Case c,int side,int low,int high){
        var a=new Traversal(c,side,false,low,high,true);a.run();
        if(!a.complete){c.reason=a.stop;return null;}
        var b=new Traversal(c,side,true,low,high,true);b.run();
        if(!b.complete){c.reason=b.stop;return null;}
        for(int i=0;i<=high;i++)if(a.hist[i]!=b.hist[i]||a.hist[i]!=c.hist[side][i])
            throw new Exception("Prefix histogram differs in tail collection.");
        a.tails.Sort(compare);b.tails.Sort(compare);
        if(a.tails.Count!=b.tails.Count)throw new Exception("Tail counts differ.");
        for(int i=0;i<a.tails.Count;i++){
            if(compare(a.tails[i],b.tails[i])!=0)throw new Exception("Tail sequences differ.");
            if(i>0 && compare(a.tails[i-1],a.tails[i])==0)throw new Exception("Duplicate ordered tail.");
        }
        return a.tails;
    }
    static void set(ulong[] mask,int v){mask[v>>6]|=1UL<<(v&63);}
    static void solve(Case c){
        if(c.need<=0){c.found(new ushort[0],new ushort[0],"core");return;}
        for(int side=0;side<2;side++){
            if(c.expired()){c.reason="time";break;}
            var first=new Traversal(c,side,false,0,0,false);first.run();
            c.hist[side]=first.hist;c.best[side]=first.best;
            if(c.witness!=null)return;
            if(!first.complete){c.reason=first.stop;continue;}
            var audit=new Traversal(c,side,true,0,0,false);audit.run();
            if(c.witness!=null)return;
            if(!audit.complete){c.reason=audit.stop;continue;}
            if(!first.hist.SequenceEqual(audit.hist))throw new Exception("Single-tail surveys disagree.");
            c.exact[side]=true;
        }
        if(!c.exact[0]||!c.exact[1])return;
        if(c.best[0]+c.best[1]<c.need){c.outcome="EXCLUDED";c.reason="sum";return;}
        int[] lo={Math.Max(0,c.need-c.best[1]),Math.Max(0,c.need-c.best[0])};
        int[] hi={Math.Min(c.need,c.best[0]),Math.Min(c.need,c.best[1])};
        long bytes=0;
        for(int side=0;side<2;side++){
            long count=0;
            for(int d=lo[side];d<=hi[side];d++){
                count+=c.hist[side][d];
                // Includes first and second tail arrays, list entries, and right-hand masks.
                bytes+=c.hist[side][d]*(180L+4L*d);
            }
            if(count>storeLimit){c.reason="tail-cap";return;}
        }
        if(bytes>96L*1024*1024){c.reason="memory";return;}
        var left=collect(c,0,lo[0],hi[0]);if(left==null)return;c.leftStored=left.Count;
        var right=collect(c,1,lo[1],hi[1]);if(right==null)return;c.rightStored=right.Count;
        var byLength=new List<int>[c.need+1];
        for(int k=0;k<=c.need;k++)byLength[k]=new List<int>();
        ulong[] rightMasks=new ulong[8*right.Count];
        for(int i=0;i<right.Count;i++){
            byLength[right[i].Length].Add(i);
            foreach(int v in right[i])rightMasks[8*i+(v>>6)]|=1UL<<(v&63);
        }
        long expected=0;
        foreach(ushort[] l in left){
            if(c.expired()){c.reason="time";return;}
            var ids=byLength[c.need-l.Length];
            if(ids.Count==0)continue;
            expected+=ids.Count;
            var closed=new ulong[8];var literal=new bool[512];
            foreach(int v in l){set(closed,v);foreach(int w in adj[v])set(closed,w);}
            for(int v=0;v<512;v++)foreach(int x in l)if(near(v,x)){literal[v]=true;break;}
            foreach(int i in ids){
                if(c.pairs>=pairLimit || ((c.pairs&255)==0&&c.expired())){
                    c.reason=c.expired()?"time":"pairs";return;
                }
                c.pairs++;
                bool disjoint=true;
                for(int j=0;j<8;j++)if((closed[j]&rightMasks[8*i+j])!=0){disjoint=false;break;}
                bool literalOK=true;
                foreach(int v in right[i])if(literal[v]){literalOK=false;break;}
                if(disjoint!=literalOK)throw new Exception("Cross-tail comparisons disagree.");
                if(disjoint){c.found(l,right[i],"pair");return;}
            }
        }
        if(c.pairs!=expected)throw new Exception("Incomplete pair sweep.");
        c.outcome="EXCLUDED";c.reason="pairs-exhausted";
    }
    static string histogram(long[] h){
        if(h==null)return "-";
        var rows=new List<string>();
        for(int i=0;i<h.Length;i++)if(h[i]>0)rows.Add(i+":"+h[i]);
        return rows.Count==0?"-":string.Join(",",rows);
    }
    static void Main(string[] args){
        if(args.Length!=5)throw new Exception("Expected target, node limit, tail limit, pair limit, milliseconds.");
        target=int.Parse(args[0]);nodeLimit=long.Parse(args[1]);storeLimit=int.Parse(args[2]);
        pairLimit=long.Parse(args[3]);timeLimit=int.Parse(args[4]);
        if(target<1||target>511||nodeLimit<=0||storeLimit<=0||pairLimit<=0||timeLimit<=0)throw new Exception("Invalid argument.");
        string line;
        while((line=Console.ReadLine())!=null){
            if(line.Length==0)continue;
            string[] entry=line.Split('\t');if(entry.Length!=2)throw new Exception("Expected identifier TAB core.");
            int[] p=entry[1].Split(',').Select(int.Parse).ToArray();validate(p);
            if(p.Length<2)throw new Exception("Core needs distinct endpoints.");
            var c=new Case(p);solve(c);
            Console.WriteLine(string.Join("\t",new string[]{entry[0],c.outcome,c.best[0].ToString(),c.best[1].ToString(),
                c.exact[0]?"1":"0",c.exact[1]?"1":"0",c.maskNodes.ToString(),c.contactNodes.ToString(),
                c.leftStored.ToString(),c.rightStored.ToString(),c.pairs.ToString(),c.reason,histogram(c.hist[0]),
                histogram(c.hist[1]),c.witness==null?"-":string.Join(",",c.witness)}));Console.Out.Flush();
        }
    }
}
