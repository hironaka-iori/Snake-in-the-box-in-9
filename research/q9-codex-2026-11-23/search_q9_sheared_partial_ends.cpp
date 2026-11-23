// Search slices that start or finish inside a stretched edge.
// Assign the two new slice endpoints before refilling each interior geodesic.
#define main integral_search_main
#include "search_q9_sheared_geodesics.cpp"
#undef main
struct Tip{int v,len;};
vector<Tip> tips(int root,int diff,const array<int,512>& touch,const array<int,512>& occupied){
 vector<Tip> out{{root,0}};
 for(int m=(diff-1)&diff;m;m=(m-1)&diff){
  int x=root^m,h=popcount(unsigned(m));if(!occupied[x]&&touch[x]==int(h==1))out.push_back({x,h});
 }return out;
}
int main(int argc,char**argv){
 if(argc!=4)return 2;int goal=stoi(argv[1]),low=stoi(argv[2]),high=stoi(argv[3]);string w;int rows=0;
 uint64_t maps=0,windows=0,trials=0,capped=0;
 while(cin>>w){vector<int>orig{0};for(char c:w)orig.push_back(orig.back()^(1<<(c-'0')));int n=orig.size();
  for(int d=0;d<9;d++)for(int t=1;t<512;t++){
   int h=popcount(unsigned(t));if((t&(1<<d))||h<low||h>high)continue;maps++;
   vector<int>v(n),cost(n);for(int i=0;i<n;i++){v[i]=orig[i]^(((orig[i]>>d)&1)?t:0);if(i)cost[i]=cost[i-1]+popcount(unsigned(v[i]^v[i-1]));}
   int s=0;array<int,512>when;when.fill(-1);
   for(int j=0;j<n;j++){
    int x=v[j];s=max(s,when[x]+1);
    for(int bit=0;bit<9;bit++){int k=when[x^(1<<bit)];if(k!=j-1)s=max(s,k+1);}
    when[x]=j;int right=j+1<n?v[j]^v[j+1]:0,rmax=max(0,popcount(unsigned(right))-1);
    for(int a=s;a<j;a++){
     int remain=goal-(cost[j]-cost[a]);if(remain<=0)continue;if(remain>h+rmax)break;
     int left=a?v[a]^v[a-1]:0,lmax=max(0,popcount(unsigned(left))-1);if(remain>lmax+rmax)continue;
     windows++;array<int,512>touch{},occupied{};
     for(int k=a;k<=j;k++){occupied[v[k]]=1;for(int b=0;b<9;b++)touch[v[k]^(1<<b)]++;}
     auto starts=tips(v[a],left,touch,occupied),ends=tips(v[j],right,touch,occupied);
     for(auto start:starts)for(auto end:ends){
      if(start.len+end.len!=remain||start.v==end.v||has_single_bit(unsigned(start.v^end.v)))continue;
      vector<int>anchors;if(start.len)anchors.push_back(start.v);
      anchors.insert(anchors.end(),v.begin()+a,v.begin()+j+1);if(end.len)anchors.push_back(end.v);
      trials++;Scan test;if(test.run(anchors,0,anchors.size()-1)){cout<<"PARAM "<<rows<<" "<<d<<" "<<t<<" "<<a<<" "<<j<<" "<<start.v<<" "<<end.v<<endl;return 0;}capped+=test.capped;if(test.capped){cout<<"CAPPED";for(int x:test.anchors)cout<<" "<<x;cout<<endl;}
     }
    }
   }
  }if(++rows%10==0)cout<<"AT "<<rows<<" "<<maps<<" "<<windows<<" "<<trials<<" "<<capped<<endl;
 }cout<<"DONE "<<rows<<" "<<maps<<" "<<windows<<" "<<trials<<" "<<capped<<endl;
}
