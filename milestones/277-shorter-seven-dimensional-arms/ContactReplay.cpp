// Independent rooted enumeration in Q7 with occupied-neighbour counts and Q4 upper bounds.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdio>
#include <intrin.h>

using Bits = std::uint64_t;
struct Mask { Bits x[2]; };
struct Capacity { int sites, evenTwice, oddTwice; };
static std::array<Capacity,65536> cap;
static Mask neighbors[128], evenSites;
static int adjacent[128][7], contacts[128], seq[128];
static bool blocked[128], used[128];
static long long visits, localCuts, reachCuts, outputs;
static int target;
static int weight(Bits x) { return int(__popcnt64(x)); }
static void put(Mask& m,int v) { m.x[v/64]|=Bits(1)<<(v%64); }

static void buildTable() {
    int nb[16]={};
    for(int i=0;i<16;i++) for(int j=0;j<4;j++) nb[i]|=1<<(i^(1<<j));
    for(int s=1;s<65536;s++) {
        bool forest=true;
        int ancestors[16],ev=0,od=0;
        for(int i=0;i<16;i++) ancestors[i]=i;
        for(int i=0;i<16&&forest;i++) if(s&(1<<i)) {
            if(weight(s&nb[i])>2){forest=false;break;}
            if(weight(i)%2==0) ev++;else od++;
            for(int j=0;j<4;j++) {
                int v=i^(1<<j);
                if(v>=i || !(s&(1<<v))) continue;
                int a=i,b=v;
                while(ancestors[a]!=a)a=ancestors[a];
                while(ancestors[b]!=b)b=ancestors[b];
                if(a==b){forest=false;break;}
                ancestors[a]=b;
            }
        }
        if(forest) cap[s]={ev+od,2*ev+od,ev+2*od};
        else {
            for(int bits=s;bits;bits&=bits-1) {
                int t=s^(bits&-bits);
                cap[s].sites=std::max(cap[s].sites,cap[t].sites);
                cap[s].evenTwice=std::max(cap[s].evenTwice,cap[t].evenTwice);
                cap[s].oddTwice=std::max(cap[s].oddTwice,cap[t].oddTwice);
            }
        }
    }
}

static bool enough(const Mask& m,int need,int depth) {
    int e=(need+(depth&1))/2, o=need-e;
    return weight(m.x[0]&evenSites.x[0])+weight(m.x[1]&evenSites.x[1])>=e &&
           weight(m.x[0]&~evenSites.x[0])+weight(m.x[1]&~evenSites.x[1])>=o;
}

// The restriction of an induced path to each Q4 face is a disjoint union of paths.
static bool localRoom(const Mask& m,int need,int depth) {
    int total=0,even=0,odd=0;
    for(int face=0;face<8;face++) {
        int mask=int((m.x[face/4]>>(16*(face%4)))&65535);
        const Capacity a=cap[mask];
        total+=a.sites;
        if(weight(face)&1){even+=a.oddTwice;odd+=a.evenTwice;}
        else{even+=a.evenTwice;odd+=a.oddTwice;}
    }
    int e=(need+(depth&1))/2;
    return total>=need && even>=need+e && odd>=2*need-e;
}

static Bits nearHalf(Bits x) {
    Bits n=0;
    const Bits masks[] = {0x5555555555555555ULL,0x3333333333333333ULL,
        0x0f0f0f0f0f0f0f0fULL,0x00ff00ff00ff00ffULL,
        0x0000ffff0000ffffULL,0x00000000ffffffffULL};
    for(int d=0;d<6;d++) {
        int k=1<<d;n|=((x&masks[d])<<k)|((x>>k)&masks[d]);
    }
    return n;
}

static void walk(int depth,Mask untouched) {
    visits++;
    int t=seq[depth],need=target-depth;
    if(need<=0) {
        std::printf("P");
        for(int i=0;i<=depth;i++)std::printf(" %d",seq[i]);
        std::printf("\n");outputs++;
    }
    int choices[7],count=0;
    Mask first{};
    for(int j=6;j>=0;j--) {
        int v=adjacent[t][j];
        if(!blocked[v]&&!used[v]&&contacts[v]==1) {
            choices[count++]=v;put(first,v);
        }
    }
    if(count==0)return;
    if(need>3 && depth%3==0) {
        Mask all{{untouched.x[0]|first.x[0],untouched.x[1]|first.x[1]}};
        if(!localRoom(all,need,depth)){localCuts++;return;}
        Mask reachable=first;
        for(;;) {
            Mask prev=reachable;
            for(int part=0;part<2;part++)
                reachable.x[part]|=all.x[part]&(nearHalf(prev.x[part])|prev.x[1-part]);
            if(reachable.x[0]==prev.x[0] && reachable.x[1]==prev.x[1])break;
        }
        if(!enough(reachable,need,depth)){reachCuts++;return;}
        if(!localRoom(reachable,need,depth)){localCuts++;return;}
        // Vertices unreachable in this relaxation can never become reachable at a descendant.
        untouched.x[0]&=reachable.x[0];untouched.x[1]&=reachable.x[1];
    }
    for(int i=0;i<count;i++) {
        int v=choices[i];seq[depth+1]=v;used[v]=true;
        for(int n:adjacent[v])contacts[n]++;
        Mask zero{{untouched.x[0]&~neighbors[v].x[0],untouched.x[1]&~neighbors[v].x[1]}};
        walk(depth+1,zero);
        for(int n:adjacent[v])contacts[n]--;
        used[v]=false;
    }
}

int main(int argc,char** argv) {
    buildTable();
    if(argc==2){
        std::FILE* f=std::fopen(argv[1],"wb");
        if(!f)return 3;
        for(const Capacity c:cap){std::fputc(c.sites,f);std::fputc(c.evenTwice,f);std::fputc(c.oddTwice,f);}
        std::fclose(f);
    }
    for(int v=0;v<128;v++) {
        if(weight(v)%2==0)put(evenSites,v);
        for(int j=0;j<7;j++){int w=v^(1<<j);adjacent[v][j]=w;put(neighbors[v],w);}
    }
    int id,size;
    while(std::scanf("%d%d%d",&id,&target,&size)==3) {
        std::fill(blocked,blocked+128,false);
        for(int i=0,v;i<size;i++){if(std::scanf("%d",&v)!=1)return 2;blocked[v]=true;}
        visits=localCuts=reachCuts=outputs=0;
        Mask open{};
        for(int v=1;v<128;v++) if(!blocked[v] && weight(v)>1)put(open,v);
        used[0]=true;for(int v:adjacent[0])contacts[v]++;
        walk(0,open);
        for(int v:adjacent[0])contacts[v]--;used[0]=false;
        std::printf("G %d %lld %lld %lld %lld\n",id,visits,outputs,localCuts,reachCuts);
        std::fflush(stdout);
    }
}
