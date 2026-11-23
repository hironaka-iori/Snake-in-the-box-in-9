#define main old_recolor_main
#include "search_q9_recolor_projection.cpp"
#undef main
int main(int argc,char**argv){
 if(argc!=5)return 2;
 int goal=stoi(argv[1]),save=stoi(argv[2]),limit=stoi(argv[3]),maxmerge=stoi(argv[4]);
 Run s(goal,13,0,save);long long maps=0,competitive=0,ends=0;int rows=0;
 string ln;
 while(rows<limit&&getline(cin,ln)){
  rows++;istringstream in(ln);int d,axis;in>>d;array<int,16> mp;P word;while(in>>axis)word.push_back(axis);
  auto mapping=[&](auto&& self,int i,int labels,int merged)->void{
   if(labels+d-i<8||merged>maxmerge)return;
   if(i<d){
    mp[i]=0;self(self,i+1,labels,merged);
    for(int k=0;k<labels;k++){mp[i]=1<<k;self(self,i+1,labels,merged+1);}
    if(labels<8){mp[i]=1<<labels;self(self,i+1,labels+1,merged);}
    return;
   }
   maps++;P w{0};for(int a:word)if(mp[a])w.push_back(w.back()^mp[a]);
   int pos[256];fill(pos,pos+256,-1);int lo=0;vector<int> tag(w.size(),-1);
   for(int j=0;j<(int)w.size();j++){
    lo=max(lo,pos[w[j]]+1);pos[w[j]]=j;
    int n=j-lo+1;
    if(n-1+(n+1)/2<save)continue;
    ends++;
    int forbid=0;
    for(int k=j;k>=lo;k--){
     int v=w[k];
     for(int a=0;a<8;a++){int t=pos[v^(1<<a)];
      if(t<=k+1)continue;
      if(tag[t]!=j){tag[t]=j;forbid++;}
      if(tag[k]!=j){tag[k]=j;forbid++;}
     }
     int count=j-k+1;
     if(count-1+min(count-forbid,(count+1)/2)<save)continue;
     competitive++;s.eval(P(w.begin()+k,w.begin()+j+1));
    }
   }
  };
  mapping(mapping,0,0,0);
 }
 cerr<<"inputs "<<rows<<" maps "<<maps<<" endpoints "<<ends<<" windows "<<competitive<<" parityconsistent "<<s.feasible<<" skipped "<<s.skips<<" best "<<s.best<<" saved "<<s.saved.size()<<endl;
}
