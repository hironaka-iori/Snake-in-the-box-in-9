// Use the existing exact single-shortcut verifier on the complete author bank.
#define main old_projection_driver
#include "search_q9_project_records.cpp"
#undef main
#include <map>
int main(int argc,char**argv){
  if(argc<2||argc>3)return 2;
  int first=argc==3?std::stoi(argv[2]):0;
  int cap=std::stoi(argv[1]); Search s;s.minimum=189;s.shortcuts=true;
  for(int v=0;v<512;v++){s.near[v][0]=v;for(int i=0;i<9;i++)s.near[v][i+1]=v^(1<<i);}
  std::map<int,int> count;std::string line;int row=0;
  while(getline(std::cin,line)){
    ++row;if(line.empty()||line[0]<'0'||line[0]>'9')continue;
    auto a=line.find(','),b=line.find(',',a+1),c=line.find(',',b+1);
    int n=std::stoi(line.substr(0,a));if(n<=9)continue;
    std::istringstream in(line.substr(b+1,c-b-1));int d;std::array<int,16> freq{};
    s.steps.clear();while(in>>d){freq[d]++;s.steps.push_back(d);}
    if(s.steps.size()!=std::stoul(line.substr(a+1,b-a-1)))return 3;
    std::vector<std::pair<int,int>> masks;
    for(int m=0;m<(1<<n);m++)if(__builtin_popcount(unsigned(m))==n-9){
      int w=0;for(int k=0;k<n;k++)if(m&(1<<k))w+=freq[k];
      masks.emplace_back(w,m);
    }
    std::sort(masks.begin(),masks.end());s.row=row;s.maps=0;s.n=n;
    for(int j=first;j<(int)masks.size()&&(!cap||j<cap);j++){
      int k=0;for(int i=0;i<n;i++)s.mapping[i]=(masks[j].second&(1<<i))?0:(1<<k++);
      s.check();
    }
    if(++count[n]%1000==0)std::cerr<<"progress Q"<<n<<" rows "<<count[n]<<" maps "<<s.total<<" best "<<s.best<<std::endl;
  }
  for(auto [n,v]:count)std::cerr<<"COMPLETE Q"<<n<<" rows "<<v<<std::endl;
  std::cerr<<"maps "<<s.total<<" shortcut pairs "<<s.bridges<<" best "<<s.best<<std::endl;
}
