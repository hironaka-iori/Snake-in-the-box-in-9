using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;

// Join two outward tails while preserving a literal ordered core in Q9.
class TwoTailIndexed {
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
        public long maskNodes,contactNodes,pairs,indexWork,trieWork;
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
        public Tree tree;
        readonly int[] branch=new int[513];
        public long nodes;
        public int best=-1;
        public bool complete=true;
        public string stop="";
        readonly bool[] free=new bool[512],used=new bool[512];
        readonly int[] touch=new int[512];
        readonly ushort[] seq=new ushort[513];
        readonly Case c;
        readonly int side,high;
        readonly bool replay,keep;
        public Traversal(Case spec,int s,bool contact,int lower,int upper,bool collect){
            c=spec;side=s;replay=contact;high=upper;keep=collect;
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
            if(keep){
                int node=depth==0?0:tree.descend(branch[depth-1],seq[depth-1],depth,replay);
                branch[depth]=node;
                if(replay){
                    if(tree.checkedNode[node])throw new Exception("Repeated prefix in replay.");
                    tree.checkedNode[node]=true;tree.verified++;
                }
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
    // Every node is one distinct ordered tail prefix. The root is the empty tail.
    sealed class Tree {
        public readonly int[] parent,head,next,deep;
        public readonly ushort[] vertex;
        public readonly ushort[] depth;
        public readonly bool[] checkedNode;
        public readonly List<int>[] byLength;
        public int size=1, verified=0;
        public Tree(long[] hist,int high){
            int count=checked((int)hist.Take(high+1).Sum());
            parent=new int[count];head=new int[count];next=new int[count];deep=new int[count];vertex=new ushort[count];
            depth=new ushort[count];checkedNode=new bool[count];
            byLength=new List<int>[high+1];
            for(int d=0;d<=high;d++)byLength[d]=new List<int>(checked((int)hist[d]));
            byLength[0].Add(0);
        }
        public int descend(int p,int v,int d,bool audit){
            if(audit){
                for(int i=head[p];i!=0;i=next[i])if(vertex[i]==v)return i;
                throw new Exception("Ordered prefix absent from the primary tree.");
            }
            int j=size++;
            parent[j]=p;vertex[j]=(ushort)v;next[j]=head[p];head[p]=j;
            depth[j]=(ushort)d;deep[j]=d;byLength[d].Add(j);return j;
        }
        public void finish(){
            if(size!=parent.Length||verified!=size)throw new Exception("Prefix sets differ.");
            for(int j=size-1;j>0;j--)deep[parent[j]]=Math.Max(deep[parent[j]],deep[j]);
        }
        public ushort[] tail(int node){
            var a=new ushort[depth[node]];
            while(node!=0){a[depth[node]-1]=vertex[node];node=parent[node];}
            return a;
        }
    }
    static Tree collect(Case c,int side,int high){
        var tree=new Tree(c.hist[side],high);
        var a=new Traversal(c,side,false,0,high,true);a.tree=tree;a.run();
        if(!a.complete){c.reason=a.stop;return null;}
        var b=new Traversal(c,side,true,0,high,true);b.tree=tree;b.run();
        if(!b.complete){c.reason=b.stop;return null;}
        for(int i=0;i<=high;i++)if(a.hist[i]!=b.hist[i]||a.hist[i]!=c.hist[side][i])
            throw new Exception("Prefix histogram differs in tree construction.");
        tree.finish();return tree;
    }
    sealed class Limit : Exception {}
    static readonly int[][] literalNear=Enumerable.Range(0,512)
        .Select(v=>Enumerable.Range(0,512).Where(w=>near(v,w)).ToArray()).ToArray();
    sealed class IndexCheck{
        readonly Case c;readonly Tree lt,rt;
        ulong[] conflict,live;
        int width,goal;
        List<int> right;
        public int leftFound=-1,rightFound=-1;
        public IndexCheck(Case item,Tree left,Tree other){c=item;lt=left;rt=other;}
        void cost(long n){
            c.indexWork+=n;
            if(c.indexWork>pairLimit || c.expired())throw new Limit();
        }
        bool leftWalk(int node){
            int depth=lt.depth[node];
            if(depth==goal){
                for(int i=0;i<width;i++){
                    ulong w=live[depth*width+i];if(w==0)continue;
                    int b=0;while((w&1UL)==0){w>>=1;b++;}
                    leftFound=node;rightFound=right[i*64+b];return true;
                }
                return false;
            }
            for(int j=lt.head[node];j!=0;j=lt.next[j]){
                if(lt.deep[j]<goal)continue;
                cost(width);
                int a=lt.vertex[j]*width,b=depth*width,e=b+width;
                ulong any=0;
                for(int k=0;k<width;k++){
                    ulong w=live[b+k]&~conflict[a+k];live[e+k]=w;any|=w;
                }
                if(any!=0 && leftWalk(j))return true;
            }
            return false;
        }
        public bool run(int a,int b){
            goal=a;right=rt.byLength[b];width=(right.Count+63)/64;
            var incidence=new ulong[512*width];conflict=new ulong[512*width];
            live=new ulong[(goal+1)*width];
            for(int i=0;i<right.Count;i++){
                cost(b+1);
                for(int j=right[i];j!=0;j=rt.parent[j])
                    incidence[rt.vertex[j]*width+(i>>6)]|=1UL<<(i&63);
            }
            for(int v=0;v<512;v++){
                cost(10L*width);
                int vi=v*width;Array.Copy(incidence,vi,conflict,vi,width);
                for(int d=0;d<9;d++){
                    int off=(v^(1<<d))*width;
                    for(int z=0;z<width;z++)conflict[vi+z]|=incidence[off+z];
                }
            }
            for(int z=0;z<width;z++)live[z]=ulong.MaxValue;
            if((right.Count&63)!=0)live[width-1]=(1UL<<(right.Count&63))-1;
            bool hit=leftWalk(0);
            conflict=null;live=null;return hit;
        }
    }
    sealed class TrieCheck{
        readonly Case c;readonly Tree lt,rt;
        readonly int[] blocked=new int[512];
        int goal,other;
        public int leftFound=-1,rightFound=-1;
        public TrieCheck(Case item,Tree left,Tree right){c=item;lt=left;rt=right;}
        void visit(){
            c.trieWork++;
            if(c.trieWork>pairLimit || ((c.trieWork&1023L)==0 && c.expired()))throw new Limit();
        }
        int findRight(int node){
            visit();if(rt.depth[node]==other)return node;
            for(int j=rt.head[node];j!=0;j=rt.next[j]){
                visit();
                if(rt.deep[j]<other || blocked[rt.vertex[j]]!=0)continue;
                int hit=findRight(j);if(hit>=0)return hit;
            }
            return -1;
        }
        bool sweepLeft(int node){
            visit();
            int d=lt.depth[node];
            // No right tail compatible now can become compatible after this left prefix grows.
            if(d==goal || (d>=3 && d%3==0)){
                int hit=findRight(0);if(hit<0)return false;
                if(d==goal){leftFound=node;rightFound=hit;return true;}
            }
            for(int j=lt.head[node];j!=0;j=lt.next[j]){
                if(lt.deep[j]<goal)continue;
                foreach(int v in literalNear[lt.vertex[j]])blocked[v]++;
                bool success=sweepLeft(j);
                foreach(int v in literalNear[lt.vertex[j]])blocked[v]--;
                if(success)return true;
            }
            return false;
        }
        public bool run(int a,int b){
            goal=a;other=b;if(c.expired())throw new Limit();
            return sweepLeft(0);
        }
    }
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
        long estimatedBytes=4L*1024*1024;
        long[] counts=new long[2];
        for(int side=0;side<2;side++){
            for(int d=0;d<=hi[side];d++){
                estimatedBytes+=40L*c.hist[side][d];
                if(d>=lo[side])counts[side]+=c.hist[side][d];
            }
            if(counts[side]>storeLimit){c.reason="tail-cap";return;}
        }
        // All length bins combined use at most this many incidence and working words.
        estimatedBytes+=(1024L+hi[0]+1)*8*((counts[1]+63)/64+hi[1]+1);
        if(estimatedBytes>96L*1024*1024){c.reason="memory";return;}
        Tree left=collect(c,0,hi[0]);if(left==null)return;c.leftStored=(int)counts[0];
        Tree right=collect(c,1,hi[1]);if(right==null)return;c.rightStored=(int)counts[1];
        var index=new IndexCheck(c,left,right);var trie=new TrieCheck(c,left,right);
        long full=0;
        for(int a=lo[0];a<=hi[0];a++){
            int b=c.need-a;
            if(b<lo[1]||b>hi[1])continue;
            long pairs=(long)left.byLength[a].Count*right.byLength[b].Count;
            if(pairs==0)continue;
            bool exists;
            try {exists=index.run(a,b);}
            catch(Limit){c.reason=c.expired()?"time-index":"index-work";return;}
            if(exists){
                // Verify the reported literal pair independently, even if a later budget is exhausted.
                var x=left.tail(index.leftFound);var y=right.tail(index.rightFound);
                foreach(int v in x)foreach(int w in y)if(near(v,w))throw new Exception("Conflicting index witness.");
                c.found(x,y,"pair-index");return;
            }
            try {exists=trie.run(a,b);}
            catch(Limit){c.reason=c.expired()?"time-trie":"trie-work";return;}
            if(exists)throw new Exception("Negative index contradicted by trie.");
            full+=pairs;
        }
        if(c.expired()){c.reason="time";return;}
        c.pairs=full;c.outcome="EXCLUDED";c.reason="indexed-trie-exhausted";
    }
    static string histogram(long[] h){
        if(h==null)return "-";
        var rows=new List<string>();
        for(int i=0;i<h.Length;i++)if(h[i]>0)rows.Add(i+":"+h[i]);
        return rows.Count==0?"-":string.Join(",",rows);
    }
    static void Main(string[] args){
        if(args.Length!=5)throw new Exception("Expected target, node limit, tail limit, per-method work limit, milliseconds.");
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
                histogram(c.hist[1]),c.witness==null?"-":string.Join(",",c.witness),c.indexWork.ToString(),c.trieWork.ToString()}));Console.Out.Flush();
        }
    }
}
