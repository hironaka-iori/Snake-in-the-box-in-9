#define Q9_SEQUENTIAL_LIBRARY
#include "sequential.cpp"
int main(int argc,char**argv){ifstream f(argv[1]);mt19937 rng(195196192);string line;int id=0;while(id<24&&getline(f,line)){
 istringstream in(line);Path q;int v;while(in>>v)q.push_back(v);assert(valid(q)&&q.size()==192);string w;for(int i=1;i<q.size();i++)w+='A'+countr_zero(unsigned(q[i]^q[i-1]));
 array<string,3> pieces={w.substr(0,64),w.substr(64,64),w.substr(128)};for(auto&piece:pieces){string alphabet="ABCDEFGHI";shuffle(alphabet.begin(),alphabet.end(),rng);for(char&c:piece)c=alphabet[c-'A'];}
 assert(!valid(vertices(pieces[0]+pieces[1]+pieces[2])));string a(pieces[0].rbegin(),pieces[0].rend());All ab(a,pieces[1],0,1000000);ab.visit(0,0);assert(!ab.cut);bool ok=false;
 for(auto& b:ab.list){string rev(b.w.rbegin(),b.w.rend());rev+=a;Glue c(rev,pieces[2]);if(!c.search(0,0))continue;string path(rev.rbegin(),rev.rend());path+=c.word;assert(valid(vertices(path)));cout<<"S "<<id<<" "<<pieces[0]<<" "<<pieces[1]<<" "<<pieces[2]<<" "<<path<<endl;ok=true;break;}
 assert(ok);id++;}cout<<"DONE "<<id<<endl;}
