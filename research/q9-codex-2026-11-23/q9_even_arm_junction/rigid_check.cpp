#define main prior_brute_driver
#include "brute.cpp"
#undef main
int main(int argc,char**argv){ifstream f(argv[1]);permutations();string a,b;int cases=0;U attempts=0;while(f>>a>>b){array<bool,512>ban{};int v=0;for(char c:a){v^=1<<(c-'0');ban[v]=true;for(int bit=1;bit<512;bit*=2)ban[v^bit]=true;}P right;v=0;for(char c:b){v^=1<<(c-'0');right.push_back(v);}int good=0;
 for(const auto&perm:group){attempts++;bool ok=true;for(int v:right)if(ban[applyP(perm,v)]){ok=false;break;}good+=ok;}assert(!good);cases++;}cout<<"DONE cases "<<cases<<" permutations "<<attempts<<" hits 0"<<endl;}
