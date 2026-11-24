using System;
using System.Collections.Generic;
using System.Linq;

// Fix each long enough first arm in turn. The second traversal avoids every
// site of that full arm, so it can return a joint witness directly.
class ConditionalPairs {
    static readonly int[][] N=Enumerable.Range(0,256).Select(v=>Enumerable.Range(0,8).Select(i=>v^(1<<i)).ToArray()).ToArray();
    static readonly int[] side=Enumerable.Range(0,256).Select(v=>Convert.ToString(v,2).Count(c=>c=='1')%2).ToArray();
    static int minimum;
    static long limit,firstNodes,secondNodes,firstArms,componentCuts;
    static bool complete=true,record=false;
    static int[] firstPrefix,secondPrefix,whole;
    static Dictionary<int,int> totals=new Dictionary<int,int>();
    static class Output {
        public static void Add(int[] first,int[] second) {
            int len=first.Length+second.Length-1;
            if(!totals.ContainsKey(len))totals[len]=0;
            totals[len]++;
            Console.WriteLine("P "+string.Join(",",first)+" "+string.Join(",",second));
            if(len>=192)record=true;
        }
    }
    class Walker {
        readonly bool primary;
        readonly int required;
        readonly bool[] occupied=new bool[256], other=new bool[256];
        readonly int[] contacts=new int[256],path=new int[99],queue=new int[256],seen=new int[256];
        int token;
        public Walker(bool first,int[] prefix,int[] excluded,int threshold) {
            primary=first;required=threshold;
            foreach(int v in excluded)other[v]=true;
            for(int i=0;i<prefix.Length;i++){path[i]=prefix[i];Mark(prefix[i],true);}
            Walk(prefix.Length-1);
        }
        void Mark(int v,bool on){occupied[v]=on;foreach(int w in N[v])contacts[w]+=on?1:-1;}
        bool Room(int tip,int need) {
            // Any suffix lies in the connected available component of the tip.
            // At most one non-tip vertex of degree one can be used, as the free end.
            int head=0,tail=1,even=0,odd=0;bool leafEven=false,leafOdd=false;
            int oddNeed=(need+(side[tip]==0?1:0))/2,evenNeed=need-oddNeed;
            token++;queue[0]=tip;seen[tip]=token;
            while(head<tail) {
                int v=queue[head++],degree=0;
                foreach(int w in N[v]) {
                    bool avail=w==tip || (!other[w] && !occupied[w] &&
                        (contacts[w]==0 || (contacts[w]==1 && (w^tip)!=0 && ((w^tip)&((w^tip)-1))==0)));
                    if(!avail)continue;
                    degree++;
                    if(seen[w]!=token){seen[w]=token;queue[tail++]=w;}
                }
                if(v==tip)continue;
                if(degree>1){if(side[v]==0)even++;else odd++;}
                else if(side[v]==0)leafEven=true;else leafOdd=true;
                if(even+(leafEven?1:0)>=evenNeed && odd+(leafOdd?1:0)>=oddNeed)return true;
            }
            return false;
        }
        void Walk(int depth) {
            if(!complete || record)return;
            if(firstNodes+secondNodes>=limit){complete=false;return;}
            if(primary)firstNodes++;else secondNodes++;
            if(depth>=required) {
                if(primary){
                    whole=path.Take(depth+1).ToArray();firstArms++;
                    new Walker(false,secondPrefix,whole,minimum-1-depth);
                }else Output.Add(whole,path.Take(depth+1).ToArray());
                if(record || !complete)return;
            }
            if(depth==98)return;
            int v=path[depth],need=required-depth;
            if(need>=5 && depth%4==1 && !Room(v,need)){componentCuts++;return;}
            foreach(int w in N[v]) {
                if(occupied[w] || other[w] || contacts[w]!=1)continue;
                path[depth+1]=w;Mark(w,true);Walk(depth+1);Mark(w,false);
                if(!complete || record)return;
            }
        }
    }
    static int[] Read(){return Console.ReadLine().Split(',').Select(int.Parse).ToArray();}
    static void Main(string[] args) {
        minimum=int.Parse(args[0]);limit=long.Parse(args[1]);
        firstPrefix=Read();secondPrefix=Read();
        new Walker(true,firstPrefix,secondPrefix,minimum-99);
        Console.WriteLine("S "+(record?"witness":(complete?"complete":"open"))+" "+firstNodes+" "+secondNodes+" "+firstArms+" "+componentCuts);
    }
}
