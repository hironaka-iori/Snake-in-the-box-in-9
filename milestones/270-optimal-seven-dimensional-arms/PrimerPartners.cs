using System;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Runtime.CompilerServices;

// A rooted Q7 path in the allowed complement. The two engines use independent
// representations of legality. Both explore every admissible next vertex.
class PrimerPartners {
    struct Mask {
        internal ulong lo,hi;
        internal Mask(ulong a,ulong b){lo=a;hi=b;}
        internal bool Has(int v){return (((v<64?lo:hi)>>(v&63))&1UL)!=0;}
        internal void Add(int v){if(v<64)lo|=1UL<<v;else hi|=1UL<<(v-64);}
        internal void Remove(int v){if(v<64)lo&=~(1UL<<v);else hi&=~(1UL<<(v-64));}
    }
    static readonly int[][] adj=Enumerable.Range(0,128).Select(x=>Enumerable.Range(0,7).Select(j=>x^(1<<j)).ToArray()).ToArray();
    static int[] seq=new int[128];
    static readonly Mask[] nb=new Mask[128];
    static Mask evens;
    static readonly bool[] excluded=new bool[128],used=new bool[128];
    static readonly int[] contacts=new int[128],queue=new int[128],seen=new int[128];
    static readonly bool[] odd=new bool[128];
    static int generation,minimum,seconds;
    static long nodes,parityCuts,componentCuts,found,limit;
    static Stopwatch clock;
    static StreamWriter output;
    static bool stopped;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static int Bits(ulong z) {
        z-=(z>>1)&0x5555555555555555UL;
        z=(z&0x3333333333333333UL)+((z>>2)&0x3333333333333333UL);
        z=(z+(z>>4))&0x0f0f0f0f0f0f0f0fUL;
        return (int)(unchecked(z*0x0101010101010101UL)>>56);
    }
    static ulong Near(ulong x) {
        return ((x&0x5555555555555555UL)<<1)|((x>>1)&0x5555555555555555UL)
              |((x&0x3333333333333333UL)<<2)|((x>>2)&0x3333333333333333UL)
              |((x&0x0f0f0f0f0f0f0f0fUL)<<4)|((x>>4)&0x0f0f0f0f0f0f0f0fUL)
              |((x&0x00ff00ff00ff00ffUL)<<8)|((x>>8)&0x00ff00ff00ff00ffUL)
              |((x&0x0000ffff0000ffffUL)<<16)|((x>>16)&0x0000ffff0000ffffUL)
              |(x<<32)|(x>>32);
    }
    static Mask Reach(Mask free,int tip) {
        ulong x=nb[tip].lo&free.lo,y=nb[tip].hi&free.hi;
        while(true) {
            ulong a=x|(free.lo&(Near(x)|y)),b=y|(free.hi&(Near(y)|x));
            if(x==a&&y==b)return new Mask(x,y);
            x=a;y=b;
        }
    }
    static bool Room(Mask free,int d) {
        int need=minimum-d;
        if(need<=0)return true;
        int even=(need+(d&1))/2,oddCount=need-even;
        return Bits(free.lo&evens.lo)+Bits(free.hi&evens.hi)>=even &&
               Bits(free.lo&~evens.lo)+Bits(free.hi&~evens.hi)>=oddCount;
    }
    static bool Enter(int depth) {
        if(stopped)return false;
        if(nodes>=limit || ((nodes&32767)==0 && clock.Elapsed.TotalSeconds>=seconds)) {
            stopped=true;return false;
        }
        ++nodes;
        if(depth>=minimum) {
            output.WriteLine(string.Join(",",seq.Take(depth+1)));
            found++;
        }
        return true;
    }
    static void WalkMask(int depth,Mask free) {
        if(!Enter(depth))return;
        int tip=seq[depth];
        if(!Room(free,depth)){parityCuts++;return;}
        if(depth<minimum-3 && depth%3==0) {
            free=Reach(free,tip);
            if(!Room(free,depth)){componentCuts++;return;}
        }
        // free excludes the occupied prefix and neighbours of every earlier
        // prefix vertex other than tip. Remove neighbours of tip before descent.
        Mask next=new Mask(free.lo&~nb[tip].lo,free.hi&~nb[tip].hi);
        foreach(int v in adj[tip]) if(free.Has(v)) {
            seq[depth+1]=v;WalkMask(depth+1,next);
            if(stopped)return;
        }
    }
    static void Mark(int v,bool add) {
        used[v]=add;
        foreach(int w in adj[v])contacts[w]+=add?1:-1;
    }
    static bool ArrayRoom(int tip,int depth) {
        int need=minimum-depth;
        int evenNeed=(need+(odd[tip]?1:0))/2,oddNeed=need-evenNeed;
        int evenLeft=0,oddLeft=0,head=0,tail=1;
        ++generation;queue[0]=tip;seen[tip]=generation;
        while(head<tail) {
            int v=queue[head++];
            foreach(int w in adj[v]) {
                if(seen[w]==generation||used[w]||excluded[w])continue;
                int diff=tip^w;
                if(contacts[w]>0 && !(contacts[w]==1 && (diff&(diff-1))==0))continue;
                seen[w]=generation;queue[tail++]=w;
                if(odd[w])oddLeft++;else evenLeft++;
                if(evenLeft>=evenNeed && oddLeft>=oddNeed)return true;
            }
        }
        return false;
    }
    static void WalkArray(int depth) {
        if(!Enter(depth))return;
        int tip=seq[depth];
        if(depth<minimum-2 && depth%4==1 && !ArrayRoom(tip,depth)){componentCuts++;return;}
        foreach(int v in adj[tip]) if(!excluded[v] && !used[v] && contacts[v]==1) {
            Mark(v,true);seq[depth+1]=v;WalkArray(depth+1);Mark(v,false);
            if(stopped)return;
        }
    }
    static int[] Parse(string s){return s.Split(',').Select(int.Parse).ToArray();}
    static void Main(string[] args) {
        bool audit=args[0]=="array";
        minimum=int.Parse(args[1]);limit=long.Parse(args[2]);seconds=int.Parse(args[3]);
        int[] parent=Parse(Console.ReadLine()),prefix=Parse(Console.ReadLine());
        foreach(int v in parent.Skip(1))excluded[v]=true;
        var free=new Mask(ulong.MaxValue,ulong.MaxValue);
        for(int v=0;v<128;v++){
            odd[v]=(Bits((ulong)v)&1)!=0;if(!odd[v])evens.Add(v);
            foreach(int w in adj[v])nb[v].Add(w);
            if(excluded[v])free.Remove(v);
        }
        if(parent[0]!=0 || prefix[0]!=0 || excluded[0])throw new Exception("Invalid root.");
        free.Remove(0);
        for(int i=0;i<prefix.Length;i++){
            int v=prefix[i];
            if(i>0) {
                int prev=prefix[i-1];if(!nb[prev].Has(v)||!free.Has(v)||contacts[v]!=1||used[v])
                    throw new Exception("Invalid prefix.");
                free=new Mask(free.lo&~nb[prev].lo,free.hi&~nb[prev].hi);
            }
            seq[i]=v;Mark(v,true);
        }
        clock=Stopwatch.StartNew();
        using(output=new StreamWriter(args[4])) {
            if(audit)WalkArray(prefix.Length-1);else WalkMask(prefix.Length-1,free);
        }
        Console.WriteLine(string.Join(" ",stopped?"open":"complete",nodes,found,parityCuts,componentCuts));
    }
}

