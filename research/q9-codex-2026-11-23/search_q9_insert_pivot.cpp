// Insert one step anywhere in a bank path, then isometrically pivot the entire suffix.
#define main single_pivot_main
#include "search_q9_pivot.cpp"
#undef main
int main(){
  vector<int>b(192);Count cases=0,perms=0,sites=0;
  while(cin>>b[0]){
    for(int i=1;i<192;i++)if(!(cin>>b[i]))return 3;
    if(!valid(b))return 4;
    for(int i=0;i<192;i++){
      ++sites;
      for(int axis=0;axis<9;axis++){
        int bit=1<<axis,connector=b[i]^bit;
        bool legal=true;
        for(int j=0;j<=i;j++)if(connector==b[j]||(j<i && popcount(unsigned(connector^b[j]))==1)){legal=false;break;}
        if(!legal)continue;
        vector<int>p(b.begin(),b.begin()+i+1);
        for(int j=i;j<192;j++)p.push_back(b[j]^bit);
        Pivot t;++cases;if(t.solve(p,i+1)){
          for(int j=i+2;j<193;j++)p[j]=connector^t.mapped[connector^p[j]];
          if(!valid(p))return 6;cout<<"FOUND ";for(int x:p)cout<<x<<" ";cout<<"\n";return 0;
        }
        if(t.leaves!=362880)return 7;perms+=t.leaves;
      }
    }
  }
  cout<<"sites "<<sites<<" legal connectors "<<cases<<" perms "<<perms<<"\n";
}
