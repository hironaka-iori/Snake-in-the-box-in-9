#define TIP_SEARCH
#define main search_driver
#include "search.cpp"
#undef main
int main(){
 string word;cin>>word;Path p{0};for(char c:word)p.push_back(p.back()^(1<<(c-'0')));assert(p.size()==192&&defects(p).empty());
 Path q(p.begin()+2,p.end()-3);assert(q.size()==187);Extend ext(q);ext.search(false);
 assert(w191.count(key(p)));cout<<"CONTROL tips reproduced reference 191 from 186; extension_nodes "<<extensionnodes<<endl;
}

