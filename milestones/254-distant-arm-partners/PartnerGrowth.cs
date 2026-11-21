using System;
using System.Collections.Generic;
using System.Linq;

// All vertices are in the eight-cube, translated so that the crossing is 0.
class PartnerGrowth
{
    readonly int[][] neighbors = new int[256][];
    readonly int[] weight = new int[256];
    readonly bool[] parent = new bool[256], used = new bool[256];
    readonly int[] contacts = new int[256], path = new int[256], axes = new int[8];
    readonly Random random;
    readonly List<int[]> pool = new List<int[]>();
    int[] best, local;
    int nodes, limit;
    bool cut;

    PartnerGrowth(int[] fixedArm, int salt)
    {
        random = new Random(salt);
        foreach (int v in fixedArm) parent[v] = true;
        for (int v=0; v<256; v++) {
            neighbors[v] = Enumerable.Range(0,8).Select(i=>v^(1<<i)).ToArray();
            if (v>0) weight[v] = 1+weight[v&(v-1)];
        }
        for (int i=0; i<8; i++) axes[i] = i;
    }

    void Mark(int v, bool on)
    {
        used[v] = on;
        int delta = on ? 1 : -1;
        foreach (int w in neighbors[v]) contacts[w] += delta;
    }

    void AxisOrder(bool shuffle)
    {
        for (int i=0; i<8; i++) axes[i] = i;
        if (shuffle) for (int i=7; i>0; i--) {
            int j=random.Next(i+1), t=axes[i]; axes[i]=axes[j]; axes[j]=t;
        }
    }

    bool Visit()
    {
        if (nodes == limit) { cut=true; return false; }
        nodes++; return true;
    }

    void Grow(int count)
    {
        if (!Visit()) return;
        if (count>local.Length) local=path.Take(count).ToArray();
        int tip=path[count-1];
        foreach (int i in axes) {
            int w=neighbors[tip][i];
            if (parent[w] || used[w] || contacts[w]!=1) continue;
            path[count]=w; Mark(w,true);
            Grow(count+1);
            Mark(w,false);
            if (cut) break;
        }
    }

    int[] Tail(int[] seed, int k, int budget, bool shuffle)
    {
        AxisOrder(shuffle);
        local=seed.Take(k+1).ToArray(); nodes=0; limit=budget; cut=false;
        foreach (int v in local) Mark(v,true);
        Array.Copy(local,path,k+1);
        Grow(k+1);
        for (int i=0; i<=k; i++) Mark(seed[i],false);
        return local;
    }

    // Replace open intervals between fixed anchors. Only the last new vertex
    // is allowed to touch the right anchor. All other retained vertices and
    // completed replacements are present in the contact counts throughout.
    sealed class Gap
    {
        public int left, right, length;
        public List<int> fill=new List<int>();
        public Gap(int a, int b, int n) { left=a; right=b; length=n; }
    }

    bool Bridge(int[] seed, Gap[] gaps, int which, int at, int remaining)
    {
        if (!Visit()) return false;
        Gap gap=gaps[which]; int right=seed[gap.right];
        foreach (int i in axes) {
            int w=neighbors[at][i], distance=weight[w^right];
            if (parent[w] || used[w] || distance>remaining-1) continue;
            bool last=remaining==2;
            if (last ? (distance!=1 || contacts[w]!=2) : (distance==1 || contacts[w]!=1)) continue;
            Mark(w,true); gap.fill.Add(w);
            bool found=last
                ? which+1==gaps.Length || Bridge(seed,gaps,which+1,seed[gaps[which+1].left],gaps[which+1].length)
                : Bridge(seed,gaps,which,w,remaining-1);
            Mark(w,false);
            if (found) return true;
            gap.fill.RemoveAt(gap.fill.Count-1);
            if (cut) break;
        }
        return false;
    }

    int[] Reroute(int[] seed, Gap[] gaps, int extra, int budget)
    {
        nodes=0; limit=budget; cut=false;
        bool[] removed=new bool[seed.Length];
        foreach (Gap g in gaps) {
            if (g.length<2 || weight[seed[g.left]^seed[g.right]]>g.length) return null;
            for (int j=g.left+1; j<g.right; j++) removed[j]=true;
        }
        for (int j=0; j<seed.Length; j++) if (!removed[j]) Mark(seed[j],true);
        bool allowed=extra<0 || (!parent[extra] && !used[extra] && contacts[extra]==1);
        int[] result=null;
        if (allowed) {
            if (extra>=0) Mark(extra,true);
            if (Bridge(seed,gaps,0,seed[gaps[0].left],gaps[0].length)) {
                List<int> answer=new List<int>();
                for (int j=0; j<seed.Length; j++) {
                    if (!removed[j]) answer.Add(seed[j]);
                    foreach (Gap g in gaps) if (g.left==j) answer.AddRange(g.fill);
                }
                if (extra>=0) answer.Add(extra);
                result=answer.ToArray();
            }
            if (extra>=0) Mark(extra,false);
        }
        for (int j=0; j<seed.Length; j++) if (!removed[j]) Mark(seed[j],false);
        return result;
    }

    void Keep(int[] seed)
    {
        if (seed==null) return;
        if (best==null || seed.Length>best.Length) best=seed;
        if (pool.Any(p=>p.SequenceEqual(seed))) return;
        if (pool.Count<18) { pool.Add(seed); return; }
        int shortest=pool.Min(p=>p.Length);
        if (seed.Length<shortest) return;
        var candidates=Enumerable.Range(0,pool.Count).Where(i=>pool[i].Length==shortest).ToArray();
        pool[candidates[random.Next(candidates.Length)]]=seed;
    }

    void Unblock(int[] seed)
    {
        int trials=0, success=0, traversed=0;
        int last=seed.Length-1;
        for (int axis=0; axis<8; axis++) {
            int extra=neighbors[seed[last]][axis];
            if (parent[extra]) continue;
            var hit=Enumerable.Range(0,last).Where(j=>weight[extra^seed[j]]<=1).ToArray();
            if (hit.Length==0) { Keep(seed.Concat(new[]{extra}).ToArray()); continue; }
            if (hit[0]==0) continue;
            var tried=new HashSet<string>();
            for (int split=0; split<hit.Length; split++)
                for (int margin=0; margin<=4; margin++)
                    foreach (int d1 in new[]{0,2,4,-2})
                        foreach (int d2 in split==0 ? new[]{0} : new[]{0,2,-2}) {
                            int right1=split==0?hit[hit.Length-1]:hit[split-1];
                            int a=Math.Max(0,hit[0]-1-margin), b=Math.Min(last,right1+1+margin);
                            var gaps=new List<Gap>{new Gap(a,b,b-a+d1)};
                            if (split>0) {
                                int c=Math.Max(0,hit[split]-1-margin), e=Math.Min(last,hit[hit.Length-1]+1+margin);
                                if (b>c) continue;
                                gaps.Add(new Gap(c,e,e-c+d2));
                            }
                            if (gaps.Any(g=>g.right-g.left>30 || g.length<2)) continue;
                            string key=string.Join("/",gaps.Select(g=>g.left+","+g.right+","+g.length));
                            if (!tried.Add(key)) continue;
                            AxisOrder(true);
                            int[] answer=Reroute(seed,gaps.ToArray(),extra,18000);
                            trials++; traversed+=nodes;
                            if (answer!=null) { success++; Keep(answer); }
                        }
        }
        Console.WriteLine("unblock "+trials+" "+traversed+" "+success+" "+string.Join(",",best));
    }

    void Search(int[] seed)
    {
        Keep(seed); Unblock(seed);
        for (int k=seed.Length-1-8; k>=Math.Max(0,seed.Length-1-56); k-=8) {
            int[] w=Tail(seed,k,1800000,false); Keep(w);
            Console.WriteLine("prefix "+k+" "+nodes+" "+(cut?0:1)+" "+string.Join(",",w));
        }
        long bridgeNodes=0, tailNodes=0; int bridges=0;
        for (int attempt=0; attempt<1000; attempt++) {
            int[] p=(attempt%3==0) ? best : pool[random.Next(pool.Count)];
            int left=random.Next(p.Length-3);
            int right=Math.Min(p.Length-1,left+2+random.Next(14));
            int delta=(attempt%5==0) ? -2 : ((attempt%5<3) ? 0 : 2);
            var gap=new Gap(left,right,right-left+delta);
            if (gap.length>=2) {
                AxisOrder(true);
                var variant=Reroute(p,new[]{gap},-1,9000);
                bridgeNodes+=nodes;
                if (variant!=null) { p=variant; bridges++; Keep(p); }
            }
            int drop=attempt%6==0 ? random.Next(12,50) : random.Next(3,23);
            var grown=Tail(p,Math.Max(0,p.Length-1-drop),36000,true);
            tailNodes+=nodes; Keep(grown);
        }
        Console.WriteLine("regrowth "+bridges+" "+bridgeNodes+" "+tailNodes+" "+string.Join(",",best));
    }

    static int[] ReadPath() { return Console.ReadLine().Split(',').Select(int.Parse).ToArray(); }
    static void Main(string[] args)
    {
        var solver=new PartnerGrowth(ReadPath(),int.Parse(args[0]));
        solver.Search(ReadPath());
    }
}
