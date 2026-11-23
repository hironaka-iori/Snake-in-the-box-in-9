#define main experimental_main
#include "forest.cpp"
#undef main
int main(int argc,char**argv){
 if(argc!=3)return 2;int kind=atoi(argv[1]),tips=atoi(argv[2]),typ,id,np;
 mt19937 rng(437);long long total=0,ready=0,vis=0,caps=0,hits=0;
 while(cin>>typ>>id>>np){
  vector<int> p(np);for(auto &v:p)cin>>v;if(typ!=kind)continue;
  for(int flip=0;flip<(typ?2:1);flip++){
   vector<int> e;for(int i=flip;i<np;i+=2)e.push_back(p[i]);int n=e.size(),m=n/2;
   for(int lenA=1;lenA<=2;lenA++)for(int lenB=1;lenB<=2;lenB++)
   for(int l=0;l+lenA<=m;l++)for(int r=m+1;r+lenB<=n;r++){
    int sum=lenA+lenB+97-tips/2-n;
    for(int a=0;a<=sum;a++){
     vector<Gap> g={{l,l+lenA-1,a,l==0,{}},{r,r+lenB-1,sum-a,false,{}}};
     Solver s(e,e,g,1000000,tips,rng);total++;if(!s.init)continue;ready++;bool ok=s.next(0);vis+=s.vis;caps+=s.capped;
     if(ok){hits++;cout<<"W "<<id<<" "<<flip<<" 192 "<<total;for(int v:s.w)cout<<" "<<v;cout<<endl;}
    }
   }
  }
  cout<<"COUNT "<<id<<" "<<total<<" "<<ready<<" "<<vis<<" "<<caps<<" "<<hits<<endl;
 }
}
