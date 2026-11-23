#define Q9_OMIT_DETOUR_MAIN
#include "detour.cpp"
int main(){
 string line;getline(cin,line);istringstream in(line);Path source;int x;while(in>>x)source.push_back(x);if(source.size()!=192||!valid(source,9))return 2;
 Engine e(0,0,191,1097);Detour d(e,250000,2,2,1097);Path witness;
 for(int axis=0;axis<9;++axis){auto q=project(source,axis);if(e.score(q,191,witness)<191)continue;
  for(int a=0;a+4<(int)q.size();++a){int b=a+4;if(popcount(unsigned(q[a]^q[b]))!=2)continue;
   for(int bit=1;bit<256;bit*=2){int mid=q[a]^bit;if(popcount(unsigned(mid^q[b]))!=1)continue;Path small(q.begin(),q.begin()+a+1);small.push_back(mid);small.insert(small.end(),q.begin()+b,q.end());
    if(set<int>(small.begin(),small.end()).size()!=small.size()||e.score(small,191,witness)>=191)continue;
    cout<<"PLANT original_axis "<<axis<<" shorten "<<a<<" "<<b<<"\nBASE";for(int v:small)cout<<" "<<v;cout<<endl;
    d.run(small,0,axis);return 5;
   }
  }
 }return 6;
}
