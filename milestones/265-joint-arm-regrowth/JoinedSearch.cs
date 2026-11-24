using System;
using System.Collections.Generic;
using System.Linq;

class JoinedSearch {
    readonly int[][] neighbors = new int[256][];
    readonly int[] weight = new int[256], scratch = new int[256], order = new int[8];
    readonly int[] touches = new int[256];
    readonly bool[] used = new bool[256], blocked = new bool[256];
    readonly Random rng;
    readonly List<Pair> pool = new List<Pair>();
    int nodes, budget;
    int[] bestTail, bridge;
    int last;
    long tailNodes, bridgeNodes;
    int released, repaired, accepted;
    Pair champion, bestChanged;
    int[] seedA,seedB;
    bool fixedParent;

    class Pair {
        public int[] A,B;
        public int Score { get {return A.Length+B.Length-1;} }
        public Pair(int[] a,int[] b) { A=a; B=b; }
    }

    JoinedSearch(int salt) {
        rng=new Random(salt);
        for (int v=0;v<256;v++) {
            neighbors[v]=Enumerable.Range(0,8).Select(i=>v^(1<<i)).ToArray();
            if(v!=0) weight[v]=1+weight[v&(v-1)];
        }
        for(int i=0;i<8;i++) order[i]=i;
    }
    void Prepare(int[] other) {
        Array.Clear(used,0,256);Array.Clear(touches,0,256);Array.Clear(blocked,0,256);
        foreach(int v in other) blocked[v]=true;
        for(int i=7;i>0;i--) {int j=rng.Next(i+1),tmp=order[i];order[i]=order[j];order[j]=tmp;}
        nodes=0;
    }
    void Mark(int v,bool on) {
        used[v]=on;
        foreach(int w in neighbors[v]) touches[w]+=on?1:-1;
    }
    void Grow(int count) {
        if(nodes>=budget)return;
        nodes++;
        if(count>bestTail.Length) bestTail=scratch.Take(count).ToArray();
        foreach(int axis in order) {
            int w=neighbors[scratch[count-1]][axis];
            if(used[w] || blocked[w] || touches[w]!=1)continue;
            scratch[count]=w;Mark(w,true);Grow(count+1);Mark(w,false);
            if(nodes>=budget)return;
        }
    }
    int[] Tail(int[] arm,int[] other,int retain,int limit) {
        Prepare(other);budget=limit;
        bestTail=arm.Take(retain).ToArray();
        Array.Copy(arm,scratch,retain);
        foreach(int v in bestTail)Mark(v,true);
        Grow(retain);
        tailNodes+=nodes;
        return bestTail;
    }
    bool Fill(int v,int remaining,int index) {
        if(nodes>=budget)return false;
        nodes++;
        foreach(int axis in order) {
            int w=neighbors[v][axis], dist=weight[w^last];
            if(used[w] || blocked[w] || dist>remaining-1)continue;
            if(remaining==2) {
                if(dist==1 && touches[w]==2) {bridge[index]=w;return true;}
            } else if(dist>1 && touches[w]==1) {
                bridge[index]=w;Mark(w,true);
                bool found=Fill(w,remaining-1,index+1);
                Mark(w,false);if(found)return true;
            }
        }
        return false;
    }
    int[] Replace(int[] arm,int[] other,int left,int right,int length,int limit) {
        if(length<2 || weight[arm[left]^arm[right]]>length)return null;
        Prepare(other);budget=limit;last=arm[right];
        for(int i=0;i<arm.Length;i++) if(i<=left || i>=right)Mark(arm[i],true);
        bridge=new int[length-1];
        bool found=Fill(arm[left],length,0);
        bridgeNodes+=nodes;
        return found? arm.Take(left+1).Concat(bridge).Concat(arm.Skip(right)).ToArray():null;
    }
    int[] Avoid(int[] arm,int[] opposite,int hit) {
        if(hit==0)return null;
        if(hit==arm.Length-1) return Tail(arm,opposite,Math.Max(1,arm.Length-4),5500);
        // The opposite prefix needs the site at hit. Remove it before filling the interval.
        for(int trial=0;trial<9;trial++) {
            int margin=trial/3;
            int left=Math.Max(0,hit-1-margin-rng.Next(4));
            int right=Math.Min(arm.Length-1,hit+1+margin+rng.Next(4));
            int delta=(trial%3==0)?0:(trial%3==1?2:-2);
            int[] next=Replace(arm,opposite,left,right,right-left+delta,2400);
            if(next!=null)return next;
        }
        return null;
    }
    void Keep(int[] a,int[] b) {
        var next=new Pair(a,b);
        if(champion==null || next.Score>champion.Score)champion=next;
        if(!a.SequenceEqual(seedA) && !b.SequenceEqual(seedB) && (bestChanged==null || next.Score>bestChanged.Score))bestChanged=next;
        if(pool.Any(p=>p.A.SequenceEqual(a) && p.B.SequenceEqual(b)))return;
        if(pool.Count<40) {pool.Add(next);accepted++;return;}
        int worst=pool.Min(p=>p.Score);
        if(next.Score<worst || (next.Score==worst && rng.Next(3)!=0))return;
        var low=Enumerable.Range(0,pool.Count).Where(i=>pool[i].Score==worst).ToArray();
        pool[low[rng.Next(low.Length)]]=next;accepted++;
    }
    void Save(bool flip,int[] moving,int[] other) {
        if(flip)Keep(other,moving);else Keep(moving,other);
    }
    void Search(int[] a,int[] b,int steps,bool fixedA) {
        seedA=a;seedB=b;fixedParent=fixedA;Keep(a,b);
        for(int it=0;it<steps && champion.Score<192;it++) {
            Pair basePair=it%5==0?champion:pool[rng.Next(pool.Count)];
            bool flip=fixedParent || rng.Next(2)==0;
            int[] moving=flip?basePair.B:basePair.A, other=flip?basePair.A:basePair.B;
            if(!fixedParent && it%3==0) {
                // Explore a short new suffix until its first collision with the other arm.
                int cut=Math.Max(1,moving.Length-rng.Next(0,16));
                var next=moving.Take(cut).ToList();
                Prepare(new int[0]);
                foreach(int v in next)Mark(v,true);
                for(int j=0;j<24;j++) {
                    var opts=neighbors[next[next.Count-1]].Where(v=>!used[v] && touches[v]==1).ToArray();
                    if(opts.Length==0)break;
                    int w=opts[rng.Next(opts.Length)];next.Add(w);Mark(w,true);
                    int hit=Array.IndexOf(other,w);
                    if(hit<0)continue;
                    released++;
                    var advanced=next.ToArray();
                    int[] rerouted=Avoid(other,advanced,hit);
                    if(rerouted!=null) {
                        repaired++;
                        advanced=Tail(advanced,rerouted,advanced.Length,9000);
                        Save(flip,advanced,rerouted);
                        rerouted=Tail(rerouted,advanced,Math.Max(1,rerouted.Length-rng.Next(1,12)),9000);
                        Save(flip,advanced,rerouted);
                    }
                    break;
                }
            } else {
                if(it%4!=0 && moving.Length>4) {
                    int left=rng.Next(moving.Length-2);
                    int right=Math.Min(moving.Length-1,left+rng.Next(2,21));
                    int delta=new[]{0,0,2,2,4,-2}[rng.Next(6)];
                    int[] alt=Replace(moving,other,left,right,right-left+delta,4500);
                    if(alt!=null) {moving=alt;Save(flip,moving,other);}
                }
                int drop=it%7==0?rng.Next(24,53):rng.Next(2,23);
                int[] grown=Tail(moving,other,Math.Max(1,moving.Length-drop),it%7==0?39000:9000);
                Save(flip,grown,other);
            }
        }
        Print(champion);Print(bestChanged);
        Console.WriteLine(string.Join(",",new long[]{tailNodes,bridgeNodes,released,repaired,accepted}));
    }
    static void Print(Pair p) {
        if(p==null){Console.WriteLine("-");Console.WriteLine("-");return;}
        Console.WriteLine(string.Join(",",p.A));Console.WriteLine(string.Join(",",p.B));
    }
    static int[] Input(){return Console.ReadLine().Split(',').Select(int.Parse).ToArray();}
    static void Main(string[] args) {
        var worker=new JoinedSearch(int.Parse(args[0]));
        worker.Search(Input(),Input(),int.Parse(args[1]),args[2]=="fixed");
    }
}
