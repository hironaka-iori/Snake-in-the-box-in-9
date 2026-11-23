// Re-embed both chord-free sides of a defective walk with an arbitrary bridge.
#define Q9_FREE_BRIDGE_JOIN_NO_MAIN
#include "search_q9_free_bridge_join.cpp"
#include <map>
int main(int argc,char**argv){
 if(argc!=3)return 1;
 lenBridge=stoi(argv[1]);int limit=stoi(argv[2]);
 map<Path,set<Path>> partners;
 map<Path,Path> anchorFor;
 long long oriented=0,rows=0;
 string line;
 while(getline(cin,line)){
  if(rows>=limit)break;
  istringstream input(line);int x;Path parent;
  while(input>>x){if(x<0||x>=512)return 2;parent.push_back(x);}
  int L=int(parent.size())-1;if(L<1||int(set<int>(parent.begin(),parent.end()).size())!=L+1)return 3;
  if(rows && target!=L)return 4;target=L;rows++;
  int maxLeft=L,minRight=0;
  for(int j=1;j<=L;j++)for(int i=0;i<j;i++){
    int d=__builtin_popcount(parent[i]^parent[j]);
    if(j==i+1 && d!=1)return 5;
    if(j>i+1 && d==1){maxLeft=min(maxLeft,j-1);minRight=max(minRight,i+1);}
  }
  for(int off=max(0,minRight-lenBridge);off<=min(L-lenBridge,maxLeft);off++){
   Path a(parent.begin(),parent.begin()+off+1),b(parent.begin()+off+lenBridge,parent.end());
   if(a.size()<b.size())swap(a,b);
   for(int ra=0;ra<2;ra++,reverse(a.begin(),a.end())){
    auto leftKey=word(a,a.size()-1,-1,a.size()-1);anchorFor.try_emplace(leftKey,a);
    for(int rb=0;rb<2;rb++,reverse(b.begin(),b.end())){
     partners[leftKey].insert(word(b,0,1,b.size()-1));oriented++;
    }
   }
  }
 }
 for(auto &[leftKey,rights]:partners){
  lenA=leftKey.size();lenB=target-lenBridge-lenA;
  p=anchorFor.at(leftKey);blocked.fill(0);for(int v:p)mark(v,1);
  trie.assign(1,Node{});
  for(auto &w:rights){if(int(w.size())!=lenB)return 6;int id=0;
   for(int d:w){if(!trie[id].child[d]){trie[id].child[d]=trie.size();trie[id].active|=1<<d;trie.emplace_back();}id=trie[id].child[d];}
  }
  auto was=bridges;bridge(lenBridge);goodAnchors+=bridges>was;anchors++;
 }
 cout<<"NO_JOIN rows "<<rows<<" bridge "<<lenBridge<<" splits_oriented "<<oriented<<" anchors "<<anchors<<" bridges "<<bridges<<" trie_states "<<states<<endl;
}
