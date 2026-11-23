#define main layer_main_omitted
#include "search.cpp"
#undef main
int main(){
 mt19937 rng(53159);vector<Word> bank;string s;while(cin>>s)bank.push_back(decode(s));
 int kept=0;
 for(int t=0;t<10000&&kept<48;t++){
  int row=rng()%bank.size();auto w=bank[row];vector<int> dims;for(int d=0;d<9;d++){int k=count(w.begin(),w.end(),d);if(k>=2&&k<=4)dims.push_back(d);}if(dims.empty())continue;int d=dims[rng()%dims.size()];auto p=periods(w)[rng()%6].p;
  Search h(w,d,p,2,4000000,0,12,rng);if(h.donorOptions<2||any_of(h.blocks.begin(),h.blocks.end(),[](auto&b){return b.word.empty()||b.variants.empty();}))continue;
  bool ok=h.dfs(0,2);if(h.clipped)continue;
  cout<<"CASE "<<kept<<" "<<row<<" "<<d<<" "<<p<<" "<<h.n<<" "<<ok<<" "<<h.attempts<<"\n";
  for(int j=0;j<h.n;j++)for(auto&o:h.blocks[j].variants)cout<<"OPTION "<<j<<" "<<o.source<<" "<<o.offset<<" "<<o.length<<" "<<o.power<<" "<<o.flip<<" "<<str(o.word)<<"\n";
  if(ok){h.show(row,t);return 0;}kept++;
 }
 return kept==48?0:3;
}
