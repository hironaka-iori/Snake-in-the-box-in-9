#define main layer_main_omitted
#include "search.cpp"
#undef main
struct Recurrence{
 Word w,preferred;Perm f;int p,cap,def;vector<int> tracks,last,viol;array<int,512>blocked{};vector<int> points{0};long long nodes=0;bool cut=false;int maxdepth=0;
 Recurrence(Word s,int per,Perm perm,vector<int>r,int miss,int budget):w(s),preferred(s),f(perm),p(per),cap(budget),def(miss),tracks(r),last(r.size(),-1),viol(r.size(),0){mark(0,1);}
 void mark(int x,int n){blocked[x]+=n;for(int d=0;d<9;d++)blocked[x^(1<<d)]+=n;}
 bool dfs(int i){
  if(++nodes>cap){cut=true;return false;}maxdepth=max(maxdepth,i);if(i==int(w.size()))return true;
  auto it=find(tracks.begin(),tracks.end(),i%p);int ri=it-tracks.begin();bool free=it!=tracks.end();int old=free?last[ri]:-1,expected=old<0?-1:f[old];
  int avail=free?(expected<0||viol[ri]<def?511:1<<expected):1<<w[i];
  int first=1<<preferred[i];for(int round=0;round<2;round++){int opts=avail&(round?~first:first);
   for(;opts;opts&=opts-1){int bit=opts&-opts,d=countr_zero(unsigned(bit)),v=points.back()^bit;if(blocked[v]!=1)continue;
    bool exception=free && old>=0 && d!=expected;if(free){last[ri]=d;viol[ri]+=exception;}
    points.push_back(v);mark(v,1);if(dfs(i+1))return true;mark(v,-1);points.pop_back();
    if(free){last[ri]=old;viol[ri]-=exception;}if(cut)return false;
   }
  }return false;
 }
};
int main(int argc,char**argv){
 if(argc!=7)return 2;int count_=stoi(argv[1]),seed=stoi(argv[2]),num=stoi(argv[3]),def=stoi(argv[4]),cap=stoi(argv[5]),ctrl=stoi(argv[6]);mt19937 rng(seed);
 vector<Word>bank;string s;while(cin>>s)bank.push_back(decode(s));long long nodes=0;int used=0,clipped=0,maxdepth=0;set<int>rs,ps;
 for(int t=0;t<count_;t++){int row=rng()%bank.size();auto w=bank[row];auto lags=periods(w);vector<int> choices;for(auto lag:lags)if(lag.p<=60&&choices.size()<5)choices.push_back(lag.p);
  int p=choices[rng()%choices.size()],sep=rng()%9;vector<int> residues(p);iota(residues.begin(),residues.end(),0);shuffle(residues.begin(),residues.end(),rng);residues.resize(num);
  if(ctrl){int r=residues[0];int pos=r+p*(rng()%(1+(w.size()-1-r)/p));int d=rng()%9;if(d==w[pos])continue;w[pos]=d;if(cleanPrefix(w)==int(w.size()))continue;}
  auto perm=fit(w,p,sep);Recurrence search(w,p,perm,residues,def,cap);used++;rs.insert(row);ps.insert(p);
  bool found=search.dfs(0);nodes+=search.nodes;clipped+=search.cut;maxdepth=max(maxdepth,search.maxdepth);
  if(found){cout<<"REC "<<row<<" "<<p<<" "<<sep<<" "<<def<<" "<<str(w)<<"\nRES";for(int r:residues)cout<<" "<<r;cout<<"\nPERM";for(int y:perm)cout<<" "<<y;cout<<"\nPATH";for(int v:search.points)cout<<" "<<v;cout<<endl;return 0;}
 }
 cout<<"DONE trials "<<count_<<" tested "<<used<<" rows "<<rs.size()<<" periods "<<ps.size()<<" nodes "<<nodes<<" capped "<<clipped<<" longest "<<maxdepth<<endl;return 0;
}
